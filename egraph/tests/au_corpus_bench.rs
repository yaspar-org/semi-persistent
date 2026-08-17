// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The anytime/regret corpus (plan item B3, doc/au-solver-plan.md).
//!
//! Generates a mixed-family instance corpus, takes the exact optimum as
//! ground truth, computes each instance's certification budget `sum of A(v)`
//! with the search-graph census (`au::census`, plan item B1), and runs MCGS at
//! a doubling playout ladder, recording the optimality gap, the wall time, and
//! the completion certificate at every rung. Output is one CSV row per
//! (instance, budget) at `$AU_BENCH_DIR/corpus.csv`, written incrementally, so
//! a killed run still leaves usable data; `comparison/au/analyze.py` turns the
//! CSV into the paper's tables.
//!
//! Families (round-robin interleaved, so a deadline cut leaves every stratum
//! represented):
//!
//! * `dec` — the deceptive family (`au_deceptive.rs`): the estimate misranks
//!   the root actions, so MCGS starts at a known positive gap and closes it
//!   only by searching past the decoys at every buried level. This is the
//!   family that makes the gap-vs-budget curve non-flat.
//! * `mixed` — deceptive gadgets planted at disjoint positions of a random
//!   backbone that also carries the crossover family's cyclic classes: the
//!   gadget supplies the misranking, the cyclic classes supply the exact
//!   solver's context product.
//! * `rand` — the same random backbone with no gadget (the pilot's stratum).
//! * `xover` — the crossover family: `cycles` mutually reachable cyclic
//!   classes under a binary backbone with hot/shared/diff leaves.
//! * `width` — acyclic spine, `width` same-operator members per side per
//!   level, so every level-pair OR state fans out `width^2` actions.
//! * `ac` — one MSet class pair with `members` monomials per side; both
//!   solvers enumerate the `members^2` representation-pair product.
//!
//! * `wide` — a deceptive gadget under a width-family spine: hard for exact
//!   (the spine's actions all sit under the generalize value, so neither the
//!   projection bound nor context subsumption removes them) and deceptive for
//!   MCGS (the gadget at the base is what the estimate misranks).
//!
//! Selection rule, stated because the curves are conditional on it. Ground
//! truth is the exact solver with `exact_pruning` and `context_subsumption`
//! on, under `EXACT_GUARD`; an instance that does not finish is dropped. The
//! plan called for a 10 ms hardness floor as well, and the calibration sweep
//! (`calibrate_hardness`) shows why this harness does not apply one by
//! default: with A2 and A6 on, the cyclic families are microseconds wide open
//! — crossover at `cycles=20` is 0.3 ms, mixed at `cycles=24` is 0.4 ms — so a
//! 10 ms floor would have selected the `width` and `ac` families and nothing
//! else. The floor is therefore a reported stratification rather than an
//! exclusion: every kept instance carries its `exact_ms`, `HARD_EXACT_MS`
//! marks the hard subset the wall-clock-normalized tables are computed on, and
//! `$AU_MIN_EXACT_MS` reinstates a hard floor for anyone who wants the
//! selected corpus instead.
//!
//! Determinism: MCGS carries no random number generator, so one run per
//! (instance, budget) is the complete picture; per-instance variation comes
//! from the generation seeds. Every builder is a deterministic function of its
//! parameters and is re-run on each worker thread, so the guarded runs all see
//! the identical instance.
//!
//! Run with (release; the wall budget defaults to one hour and is the knob to
//! extend):
//!
//! ```text
//! AU_BENCH_DIR=comparison/au AU_CORPUS_SECS=21600 \
//!   cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
//!   -- --ignored --nocapture
//! ```
//!
//! `$AU_LADDER_TOP` raises the top of the playout ladder (default 2^14) and
//! `$AU_FAMILIES` restricts the run to a comma-separated family list, which is
//! how the deep families' certification knees were measured past the default
//! ladder; the CSV name follows `$AU_CSV_NAME` (default `corpus.csv`) so such
//! a run does not overwrite the main one.

use std::fs;
use std::io::Write as _;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::census::{Census, certification_budget};
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::au::space::CycleMode;
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;

#[path = "au_deceptive.rs"]
#[allow(dead_code)]
mod families;

use families::{
    DeceptiveParams, Instance, MixedParams, WideParams, build_deceptive, build_mixed,
    build_wide_deceptive, case_seed,
};

type Eg = EGraph31<NiraLitVal, false, false>;

/// Ground-truth guard. A2 + A6 put the crossover family's `cycles=10` instance
/// at 3.6 ms where the unpruned solver timed out at 30 s, so a minute of
/// pruned exact reaches instances the pilot could not have used.
const EXACT_GUARD: Duration = Duration::from_secs(60);
/// Hardness floor in exact milliseconds, overridable with `$AU_MIN_EXACT_MS`.
/// Zero by default: see the module doc's selection rule.
fn min_exact_ms() -> f64 {
    std::env::var("AU_MIN_EXACT_MS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0.0)
}
/// Exact milliseconds above which an instance is reported as hard. The
/// wall-clock-normalized tables are computed on this subset.
const HARD_EXACT_MS: f64 = 10.0;
/// Per-budget MCGS guard.
const MCGS_GUARD: Duration = Duration::from_secs(30);
/// Cumulative MCGS budget per instance: once the ladder has spent this much,
/// the remaining rungs are cut and the rows already written are kept.
const LADDER_BUDGET: Duration = Duration::from_secs(25);
/// Wall-clock cap of the census walk per instance.
const CENSUS_GUARD: Duration = Duration::from_secs(20);
/// OR-state cap of the census walk per instance.
const CENSUS_MAX_STATES: u64 = 4_000_000;
/// The playout ladder: 2^0 up to `$AU_LADDER_TOP` (default 2^14). Raising the
/// top is how the knee of an instance whose `sum A(v)` the default ladder
/// cannot pay for gets measured.
fn budgets() -> Vec<u64> {
    let top: u64 = std::env::var("AU_LADDER_TOP")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(16384);
    let mut out = vec![1u64];
    while *out.last().unwrap() < top {
        out.push(out.last().unwrap() * 2);
    }
    out
}

// ---------------------------------------------------------------------------
// Families beyond the deceptive/mixed/rand ones shared from au_deceptive.rs.
// ---------------------------------------------------------------------------

/// Crossover family (mirrors `au_scaling_crossover.rs`'s `build_instance`):
/// `cycles` mutually reachable cyclic W classes with `width` same-operator
/// members each, under a depth-`depth` binary backbone whose leaves cycle
/// through hot (distinct W pair), shared, and diff kinds.
fn build_crossover(depth: usize, width: usize, cycles: usize) -> Instance {
    assert!(cycles >= 2, "hot leaves need two distinct W classes");
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let f = eg.register_op2("f", sort, sort, sort);
    let b = eg.register_op2("b", sort, sort, sort);
    let h = eg.register_op1("h", sort, sort);
    let p_op = eg.register_op0("p", sort);
    let dl_op = eg.register_op0("dl", sort);
    let dr_op = eg.register_op0("dr", sort);
    let w: Vec<ENodeId> = (0..cycles)
        .map(|i| {
            let op = eg.register_op0(&format!("w{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    let tags: Vec<ENodeId> = (0..cycles)
        .map(|i| {
            let op = eg.register_op0(&format!("t{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    for &wi in &w {
        let hw = eg.add(h, &[wi]);
        eg.merge(hw, wi);
    }
    let fan = width.min(cycles - 1);
    for (i, &tag) in tags.iter().enumerate() {
        for j in 1..=fan {
            let member = eg.add(b, &[w[(i + j) % cycles], tag]);
            eg.merge(member, w[i]);
        }
    }
    eg.rebuild();
    let shared = eg.add(p_op, &[]);
    let dl = eg.add(dl_op, &[]);
    let dr = eg.add(dr_op, &[]);
    let n_leaves = 1usize << depth;
    let mut left_level: Vec<ENodeId> = Vec::with_capacity(n_leaves);
    let mut right_level: Vec<ENodeId> = Vec::with_capacity(n_leaves);
    for t in 0..n_leaves {
        match t % 4 {
            0 => {
                left_level.push(w[t % cycles]);
                right_level.push(w[(t + 1) % cycles]);
            }
            2 => {
                left_level.push(dl);
                right_level.push(dr);
            }
            _ => {
                left_level.push(shared);
                right_level.push(shared);
            }
        }
    }
    while left_level.len() > 1 {
        left_level = left_level.chunks(2).map(|c| eg.add(f, c)).collect();
        right_level = right_level.chunks(2).map(|c| eg.add(f, c)).collect();
    }
    eg.rebuild();
    Instance {
        eg,
        left: left_level[0],
        right: right_level[0],
    }
}

/// Width family: acyclic spine, `width` same-operator members per class per
/// side per level, distinguished by per-level tags shared between the sides.
fn build_width(depth: usize, width: usize) -> Instance {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let b = eg.register_op2("b", sort, sort, sort);
    let cl_op = eg.register_op0("cl", sort);
    let cr_op = eg.register_op0("cr", sort);
    let mut left = eg.add(cl_op, &[]);
    let mut right = eg.add(cr_op, &[]);
    for level in 0..depth {
        let tags: Vec<ENodeId> = (0..width)
            .map(|j| {
                let op = eg.register_op0(&format!("t{level}_{j}"), sort);
                eg.add(op, &[])
            })
            .collect();
        let l_members: Vec<ENodeId> = tags.iter().map(|&t| eg.add(b, &[left, t])).collect();
        let r_members: Vec<ENodeId> = tags.iter().map(|&t| eg.add(b, &[right, t])).collect();
        for &m in &l_members[1..] {
            eg.merge(m, l_members[0]);
        }
        for &m in &r_members[1..] {
            eg.merge(m, r_members[0]);
        }
        left = l_members[0];
        right = r_members[0];
    }
    eg.rebuild();
    Instance { eg, left, right }
}

/// AC family: one MSet class pair, `members` sliding-window monomials per side
/// over a shared constant ring, plus a side marker.
fn build_ac(members: usize, children: usize) -> Instance {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let m = eg.register_mset("m", sort, sort);
    let lmark_op = eg.register_op0("lmark", sort);
    let rmark_op = eg.register_op0("rmark", sort);
    let lmark = eg.add(lmark_op, &[]);
    let rmark = eg.add(rmark_op, &[]);
    let ring = members + children;
    let cs: Vec<ENodeId> = (0..ring)
        .map(|i| {
            let op = eg.register_op0(&format!("c{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    let left = add_ac_side(&mut eg, m, lmark, &cs, members, children);
    let right = add_ac_side(&mut eg, m, rmark, &cs, members, children);
    eg.rebuild();
    Instance { eg, left, right }
}

fn add_ac_side(
    eg: &mut Eg,
    m: OpId,
    mark: ENodeId,
    cs: &[ENodeId],
    members: usize,
    children: usize,
) -> ENodeId {
    let ms: Vec<ENodeId> = (0..members)
        .map(|i| {
            let mut kids = Vec::with_capacity(children + 1);
            kids.push(mark);
            for j in 0..children {
                kids.push(cs[(i + j) % cs.len()]);
            }
            eg.add(m, &kids)
        })
        .collect();
    for &member in &ms[1..] {
        eg.merge(member, ms[0]);
    }
    ms[0]
}

// ---------------------------------------------------------------------------
// Guarded runners.
// ---------------------------------------------------------------------------

type Builder = Arc<dyn Fn() -> Instance + Send + Sync>;

#[derive(Clone, Copy)]
struct ExactMeasurement {
    size: u32,
    vmass: u32,
    ms: f64,
}

fn run_guarded<T: Send + 'static>(
    label: String,
    timeout: Duration,
    body: impl FnOnce() -> T + Send + 'static,
) -> Option<T> {
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .name(label.clone())
        .spawn(move || {
            let _ = tx.send(body());
        })
        .unwrap();
    match rx.recv_timeout(timeout) {
        Ok(v) => Some(v),
        Err(mpsc::RecvTimeoutError::Timeout) => None,
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("worker {label} panicked; its message is above")
        }
    }
}

/// Exact ground truth under both accelerations. `None` = the guard expired;
/// the worker is leaked, detached and still running, the accepted pattern from
/// `au_scaling_crossover.rs`.
fn run_exact(label: &str, build: Builder) -> Option<ExactMeasurement> {
    run_guarded(format!("au-exact-{label}"), EXACT_GUARD, move || {
        let inst = build();
        let snap = AuSnapshot::new(&inst.eg).unwrap();
        let cfg = AuConfig {
            algorithm: AuAlgorithm::Exact,
            exact_pruning: true,
            context_subsumption: true,
            ..Default::default()
        };
        let start = Instant::now();
        let result = anti_unify(&snap, inst.left, inst.right, &cfg).unwrap();
        let ms = start.elapsed().as_secs_f64() * 1e3;
        let (size, vmass) = result.pool.quality(result.term_id);
        assert!(
            matches!(result.completion, Completion::Exact),
            "exact returned without a certificate"
        );
        ExactMeasurement { size, vmass, ms }
    })
}

struct McgsMeasurement {
    size: u32,
    vmass: u32,
    certified: bool,
    ms: f64,
}

fn run_mcgs(label: &str, build: Builder, playouts: u64) -> Option<McgsMeasurement> {
    run_guarded(
        format!("au-mcgs-{label}-p{playouts}"),
        MCGS_GUARD,
        move || {
            let inst = build();
            let snap = AuSnapshot::new(&inst.eg).unwrap();
            let cfg = AuConfig {
                algorithm: AuAlgorithm::Uct,
                playouts,
                ..Default::default()
            };
            let start = Instant::now();
            let result = anti_unify(&snap, inst.left, inst.right, &cfg).unwrap();
            let ms = start.elapsed().as_secs_f64() * 1e3;
            let (size, vmass) = result.pool.quality(result.term_id);
            McgsMeasurement {
                size,
                vmass,
                certified: matches!(result.completion, Completion::Exact),
                ms,
            }
        },
    )
}

/// `sum of A(v)` for one instance, under the same guard pattern.
fn run_census(label: &str, build: Builder) -> Option<Census> {
    run_guarded(
        format!("au-census-{label}"),
        CENSUS_GUARD + Duration::from_secs(5),
        move || {
            let inst = build();
            let snap = AuSnapshot::new(&inst.eg).unwrap();
            let l = snap.class_of(inst.left).unwrap();
            let r = snap.class_of(inst.right).unwrap();
            certification_budget(
                &snap,
                l,
                r,
                CycleMode::AncestorOnly,
                CENSUS_MAX_STATES,
                Some(Instant::now() + CENSUS_GUARD),
            )
            .unwrap()
        },
    )
}

// ---------------------------------------------------------------------------
// The corpus.
// ---------------------------------------------------------------------------

struct Spec {
    id: String,
    family: &'static str,
    params: String,
    build: Builder,
    /// Exempt from the hardness floor (see the module doc's selection rule).
    exempt: bool,
}

const MIX_BASE: u64 = 0x5EED_D00D_BEEF_2026;
const RAND_BASE: u64 = 0xA11F_00D5_EED0_2026;

/// Deceptive knob grid, feasible combinations only.
fn dec_specs() -> Vec<Spec> {
    let mut out = Vec::new();
    let mut i = 0usize;
    for &burial_depth in &[3usize, 5, 8, 12, 16, 20] {
        for &margin in &[2usize, 3, 5, 9] {
            for &gap in &[1usize, 2, 6, 12] {
                for &decoys in &[1usize, 2, 4] {
                    let p = DeceptiveParams {
                        burial_depth,
                        margin,
                        gap,
                        decoys,
                    };
                    if !p.is_feasible() {
                        continue;
                    }
                    let plan = p.plan();
                    out.push(Spec {
                        id: format!("dec-{i:03}"),
                        family: "dec",
                        params: format!(
                            "d_b={burial_depth};m={margin};gap={};k={decoys};q={};s={}",
                            plan.gap_eff, plan.shared, plan.decoy_bs
                        ),
                        build: Arc::new(move || build_deceptive(p)),
                        exempt: true,
                    });
                    i += 1;
                }
            }
        }
    }
    out
}

/// Deceptive gadgets planted in random cyclic backbones.
fn mixed_specs() -> Vec<Spec> {
    let mut out = Vec::new();
    let mut i = 0u64;
    for &cycles in &[6usize, 7, 8, 9, 10] {
        for &n_deceptive in &[1usize, 2, 3] {
            for &(burial_depth, margin, gap, decoys) in &[
                (4usize, 2usize, 1usize, 2usize),
                (8, 3, 2, 2),
                (12, 2, 6, 4),
                (16, 5, 2, 1),
            ] {
                for rep in 0..3u64 {
                    let deceptive = DeceptiveParams {
                        burial_depth,
                        margin,
                        gap,
                        decoys,
                    };
                    if !deceptive.is_feasible() {
                        continue;
                    }
                    let seed = case_seed(MIX_BASE, i * 7 + rep);
                    let p = MixedParams {
                        seed,
                        cycles,
                        n_deceptive,
                        deceptive,
                    };
                    out.push(Spec {
                        id: format!("mixed-{i:03}-{rep}"),
                        family: "mixed",
                        params: format!(
                            "seed={seed:#018x};cycles={cycles};planted={n_deceptive};\
                             d_b={burial_depth};m={margin};gap={gap};k={decoys}"
                        ),
                        build: Arc::new(move || build_mixed(p).0),
                        exempt: false,
                    });
                }
                i += 1;
            }
        }
    }
    out
}

/// The pilot's random stratum: the same backbones with no planted gadget.
fn rand_specs() -> Vec<Spec> {
    let mut out = Vec::new();
    for (i, &cycles) in [6usize, 7, 8, 9, 10].iter().enumerate() {
        for rep in 0..24u64 {
            let seed = case_seed(RAND_BASE, i as u64 * 101 + rep);
            let p = MixedParams {
                seed,
                cycles,
                n_deceptive: 0,
                deceptive: DeceptiveParams {
                    burial_depth: 4,
                    margin: 2,
                    gap: 1,
                    decoys: 1,
                },
            };
            out.push(Spec {
                id: format!("rand-{i:02}-{rep:02}"),
                family: "rand",
                params: format!("seed={seed:#018x};cycles={cycles}"),
                build: Arc::new(move || build_mixed(p).0),
                exempt: false,
            });
        }
    }
    out
}

/// Deceptive gadgets under width-family spines: the hardness knob is the
/// spine, the regret knob is the gadget.
fn wide_specs() -> Vec<Spec> {
    let mut out = Vec::new();
    let mut i = 0usize;
    for &(depth, width) in &[
        (2usize, 32usize),
        (4, 32),
        (4, 64),
        (8, 64),
        (4, 128),
        (8, 128),
        (12, 128),
        (4, 256),
        (8, 256),
        (12, 256),
    ] {
        for &(burial_depth, margin, gap, decoys) in &[
            (4usize, 2usize, 1usize, 1usize),
            (8, 2, 2, 2),
            (12, 3, 6, 2),
            (16, 5, 2, 4),
        ] {
            let deceptive = DeceptiveParams {
                burial_depth,
                margin,
                gap,
                decoys,
            };
            if !deceptive.is_feasible() {
                continue;
            }
            let p = WideParams {
                depth,
                width,
                deceptive,
            };
            out.push(Spec {
                id: format!("wide-{i:03}"),
                family: "wide",
                params: format!(
                    "d{depth}w{width};d_b={burial_depth};m={margin};gap={gap};k={decoys}"
                ),
                build: Arc::new(move || build_wide_deceptive(p)),
                exempt: false,
            });
            i += 1;
        }
    }
    out
}

fn xover_specs() -> Vec<Spec> {
    let mut out = Vec::new();
    let mut i = 0usize;
    for &depth in &[3usize, 4, 5] {
        for &width in &[2usize, 4, 8] {
            for &cycles in &[4usize, 6, 8, 10, 12] {
                out.push(Spec {
                    id: format!("xover-{i:02}"),
                    family: "xover",
                    params: format!("d{depth}w{width}c{cycles}"),
                    build: Arc::new(move || build_crossover(depth, width, cycles)),
                    exempt: false,
                });
                i += 1;
            }
        }
    }
    out
}

fn width_specs() -> Vec<Spec> {
    let mut out = Vec::new();
    let mut i = 0usize;
    for &depth in &[4usize, 8, 12] {
        for &width in &[16usize, 32, 64, 128, 256] {
            out.push(Spec {
                id: format!("width-{i:02}"),
                family: "width",
                params: format!("d{depth}w{width}"),
                build: Arc::new(move || build_width(depth, width)),
                exempt: false,
            });
            i += 1;
        }
    }
    out
}

fn ac_specs() -> Vec<Spec> {
    let mut out = Vec::new();
    let mut i = 0usize;
    for &members in &[24usize, 48, 64, 96, 128] {
        for &children in &[4usize, 8, 12] {
            out.push(Spec {
                id: format!("ac-{i:02}"),
                family: "ac",
                params: format!("m{members}c{children}"),
                build: Arc::new(move || build_ac(members, children)),
                exempt: false,
            });
            i += 1;
        }
    }
    out
}

/// Every stratum, interleaved round-robin.
fn corpus() -> Vec<Spec> {
    let mut streams: [std::vec::IntoIter<Spec>; 7] = [
        dec_specs().into_iter(),
        wide_specs().into_iter(),
        mixed_specs().into_iter(),
        rand_specs().into_iter(),
        xover_specs().into_iter(),
        width_specs().into_iter(),
        ac_specs().into_iter(),
    ];
    let mut out = Vec::new();
    loop {
        let mut any = false;
        for s in &mut streams {
            if let Some(spec) = s.next() {
                out.push(spec);
                any = true;
            }
        }
        if !any {
            return out;
        }
    }
}

#[test]
fn corpus_specs_are_well_formed() {
    let specs = corpus();
    assert!(specs.len() >= 400, "corpus is {} instances", specs.len());
    let mut ids: Vec<&str> = specs.iter().map(|s| s.id.as_str()).collect();
    ids.sort_unstable();
    let before = ids.len();
    ids.dedup();
    assert_eq!(before, ids.len(), "duplicate instance ids");
    for family in ["dec", "wide", "mixed", "rand", "xover", "width", "ac"] {
        assert!(
            specs.iter().any(|s| s.family == family),
            "family {family} is empty"
        );
    }
    println!("corpus: {} instances", specs.len());
    for family in ["dec", "wide", "mixed", "rand", "xover", "width", "ac"] {
        println!(
            "  {family}: {}",
            specs.iter().filter(|s| s.family == family).count()
        );
    }
}

/// One smoke instance per family end to end, so the harness itself is covered
/// by the default suite: exact, census, and two ladder rungs.
#[test]
fn corpus_pipeline_smoke() {
    let inst = build_crossover(3, 2, 4);
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let l = snap.class_of(inst.left).unwrap();
    let r = snap.class_of(inst.right).unwrap();
    let census = certification_budget(
        &snap,
        l,
        r,
        CycleMode::AncestorOnly,
        CENSUS_MAX_STATES,
        None,
    )
    .unwrap();
    assert!(!census.capped && census.sum_actions > 0);
    let build: Builder = Arc::new(|| build_crossover(3, 2, 4));
    let exact = run_exact("smoke", Arc::clone(&build)).expect("exact fits the guard");
    for &p in &[1u64, 64] {
        let m = run_mcgs("smoke", Arc::clone(&build), p).expect("MCGS fits the guard");
        assert!(
            (m.size, m.vmass) >= (exact.size, exact.vmass),
            "MCGS beat the exact optimum"
        );
        if m.certified {
            assert_eq!((m.size, m.vmass), (exact.size, exact.vmass));
        }
    }
    println!(
        "smoke: sum_A={} or_states={} exact ({}, {}) in {:.2} ms",
        census.sum_actions, census.or_states, exact.size, exact.vmass, exact.ms
    );
}

#[test]
#[ignore = "corpus run: hours of release-mode measurement, writes $AU_BENCH_DIR/corpus.csv \
            (wall budget from $AU_CORPUS_SECS, default 3600 s)"]
fn anytime_corpus() {
    let bench_dir =
        std::env::var("AU_BENCH_DIR").expect("set AU_BENCH_DIR to the directory for corpus.csv");
    fs::create_dir_all(&bench_dir).unwrap();
    let csv_name = std::env::var("AU_CSV_NAME").unwrap_or_else(|_| "corpus.csv".to_owned());
    let csv_path = PathBuf::from(&bench_dir).join(csv_name);
    let wall_budget = Duration::from_secs(
        std::env::var("AU_CORPUS_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(3600),
    );

    let mut csv = fs::File::create(&csv_path).unwrap();
    csv.write_all(
        b"instance,family,params,sum_a,sum_a_capped,or_states,exact_ms,exact_size,exact_vmass,\
          playouts,mcgs_ms,mcgs_size,mcgs_vmass,certified\n",
    )
    .unwrap();

    let start = Instant::now();
    let mut kept = 0usize;
    let mut hard = 0usize;
    let floor = min_exact_ms();
    let mut rows = 0usize;
    let mut skipped_easy = 0usize;
    let mut skipped_timeout = 0usize;
    let mut census_timeouts = 0usize;
    let mut mcgs_timeouts = 0usize;
    let mut ladder_cuts = 0usize;
    let mut cut_after = 0usize;
    let ladder = budgets();
    let families: Option<Vec<String>> = std::env::var("AU_FAMILIES")
        .ok()
        .map(|s| s.split(',').map(|f| f.trim().to_owned()).collect());
    let specs: Vec<Spec> = corpus()
        .into_iter()
        .filter(|s| {
            families
                .as_ref()
                .is_none_or(|fs| fs.iter().any(|f| f == s.family))
        })
        .collect();
    let total = specs.len();
    println!(
        "ladder {:?}, {} specs{}",
        ladder,
        total,
        match &families {
            Some(fs) => format!(" (families {})", fs.join(",")),
            None => String::new(),
        }
    );

    for spec in specs {
        if start.elapsed() > wall_budget {
            cut_after += 1;
            continue;
        }
        let Spec {
            id,
            family,
            params,
            build,
            exempt,
        } = spec;
        let Some(exact) = run_exact(&id, Arc::clone(&build)) else {
            println!("{id} [{family} {params}]: exact TIMEOUT({EXACT_GUARD:?}) — skipped");
            skipped_timeout += 1;
            continue;
        };
        if !exempt && exact.ms < floor {
            skipped_easy += 1;
            continue;
        }
        if exact.ms >= HARD_EXACT_MS {
            hard += 1;
        }
        let census = run_census(&id, Arc::clone(&build));
        if census.is_none() {
            census_timeouts += 1;
        }
        let (sum_a, sum_a_capped, or_states) = match census {
            Some(c) => (c.sum_actions.to_string(), c.capped, c.or_states.to_string()),
            None => (String::new(), true, String::new()),
        };
        kept += 1;
        println!(
            "{id} [{family} {params}]: exact ({}, {}) in {:.1} ms, sum_A={} states={}{}",
            exact.size,
            exact.vmass,
            exact.ms,
            if sum_a.is_empty() { "?" } else { &sum_a },
            if or_states.is_empty() {
                "?"
            } else {
                &or_states
            },
            if sum_a_capped { " (capped)" } else { "" }
        );

        let mut spent = Duration::ZERO;
        for &playouts in &ladder {
            if spent > LADDER_BUDGET || start.elapsed() > wall_budget + LADDER_BUDGET {
                ladder_cuts += 1;
                break;
            }
            let Some(mcgs) = run_mcgs(&id, Arc::clone(&build), playouts) else {
                mcgs_timeouts += 1;
                println!("  {id} p={playouts}: MCGS TIMEOUT({MCGS_GUARD:?}) — ladder stopped");
                break;
            };
            spent += Duration::from_secs_f64(mcgs.ms / 1e3);
            assert!(
                (mcgs.size, mcgs.vmass) >= (exact.size, exact.vmass),
                "{id}: MCGS quality ({}, {}) beats the exact optimum ({}, {}); \
                 exact optimality is broken",
                mcgs.size,
                mcgs.vmass,
                exact.size,
                exact.vmass
            );
            if mcgs.certified {
                assert_eq!(
                    (mcgs.size, mcgs.vmass),
                    (exact.size, exact.vmass),
                    "{id}: MCGS reports Completion::Exact away from the optimum; \
                     the certificate is unsound"
                );
            }
            csv.write_all(
                format!(
                    "{id},{family},{params},{sum_a},{sum_a_capped},{or_states},{:.3},{},{},\
                     {playouts},{:.3},{},{},{}\n",
                    exact.ms,
                    exact.size,
                    exact.vmass,
                    mcgs.ms,
                    mcgs.size,
                    mcgs.vmass,
                    mcgs.certified
                )
                .as_bytes(),
            )
            .unwrap();
            csv.flush().unwrap();
            rows += 1;
        }
    }

    println!();
    println!(
        "corpus: {kept} instances kept of {total} specs ({hard} of them at or above \
         {HARD_EXACT_MS} ms of exact, {skipped_easy} under the {floor} ms floor, \
         {skipped_timeout} exact timeouts, {cut_after} past the {wall_budget:?} wall \
         budget); {rows} rows; {census_timeouts} census timeouts, {mcgs_timeouts} MCGS \
         timeouts, {ladder_cuts} ladders cut on the per-instance budget"
    );
    println!("wrote {}", csv_path.display());
    println!("elapsed {:.1} s", start.elapsed().as_secs_f64());
}

/// Parameter calibration for the corpus grids: pruned exact wall time per
/// candidate parameter point, printed so the grids can be set against the
/// `MIN_EXACT_MS` floor and the `EXACT_GUARD` ceiling. Not a corpus run.
#[test]
#[ignore = "calibration sweep, minutes; prints pruned exact times per parameter point"]
fn calibrate_hardness() {
    let mut probes: Vec<(String, Builder)> = Vec::new();
    for &c in &[10usize, 12, 14, 16, 20] {
        for &w in &[2usize, 8, 16] {
            for &d in &[4usize, 6] {
                probes.push((
                    format!("xover d{d}w{w}c{c}"),
                    Arc::new(move || build_crossover(d, w, c)),
                ));
            }
        }
    }
    for &c in &[10usize, 14, 18, 24] {
        for rep in 0..2u64 {
            let seed = case_seed(MIX_BASE, 900 + rep);
            let p = MixedParams {
                seed,
                cycles: c,
                n_deceptive: 1,
                deceptive: DeceptiveParams {
                    burial_depth: 8,
                    margin: 3,
                    gap: 2,
                    decoys: 2,
                },
            };
            probes.push((
                format!("mixed cycles={c} rep={rep}"),
                Arc::new(move || build_mixed(p).0),
            ));
        }
    }
    for &(m, c) in &[(160usize, 8usize), (192, 8), (256, 8), (128, 16), (192, 16)] {
        probes.push((format!("ac m{m}c{c}"), Arc::new(move || build_ac(m, c))));
    }
    for &(d, w) in &[(8usize, 384usize), (12, 256), (12, 384), (16, 256)] {
        probes.push((
            format!("width d{d}w{w}"),
            Arc::new(move || build_width(d, w)),
        ));
    }
    for (label, build) in probes {
        match run_exact(&label, Arc::clone(&build)) {
            Some(m) => println!(
                "{label}: exact {:.1} ms, optimum ({}, {})",
                m.ms, m.size, m.vmass
            ),
            None => println!("{label}: exact TIMEOUT({EXACT_GUARD:?})"),
        }
    }
}
