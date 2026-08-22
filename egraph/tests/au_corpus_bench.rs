// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The anytime/regret corpus described in
//! `doc/benchmarks/records/au/anytime-corpus.md`.
//!
//! Generates a mixed-family instance corpus, takes the exact optimum as
//! ground truth, computes each instance's certification budget `sum of A(v)`
//! with the search-graph census (`au::census`), and runs MCGS at
//! a doubling playout ladder, recording the optimality gap, the wall time, and
//! the completion certificate at every rung. Output is one CSV row per
//! (instance, budget) at `$AU_BENCH_DIR/corpus.csv`, written incrementally, so
//! a killed run still leaves usable data; `doc/benchmarks/records/au/analyze.py` turns the
//! CSV into the paper's tables.
//!
//! Families (round-robin interleaved, so a deadline cut leaves every stratum
//! represented):
//!
//! * `dec`: the deceptive family (`au_deceptive.rs`): the estimate misranks
//!   the root actions, so MCGS starts at a known positive gap and closes it
//!   only by searching past the decoys at every buried level. This is the
//!   family that makes the gap-vs-budget curve non-flat.
//! * `mixed`: deceptive gadgets planted at disjoint positions of a random
//!   backbone that also carries the crossover family's cyclic classes: the
//!   gadget supplies the misranking, the cyclic classes supply the exact
//!   solver's reachable pair/action graph.
//! * `rand`: the same random backbone with no gadget (the control stratum).
//! * `xover`: the crossover family: `cycles` mutually reachable cyclic
//!   classes under a binary backbone with hot/shared/diff leaves.
//! * `width`: acyclic spine, `width` same-operator members per side per
//!   level, so every level-pair OR state fans out `width^2` actions.
//! * `ac`: one MSet class pair with `members` monomials per side; both
//!   solvers enumerate the `members^2` representation-pair product.
//!
//! * `wide`: a deceptive gadget under a width-family spine: hard for exact
//!   (the spine's actions all sit under the generalize value, so the
//!   projection bound does not remove them) and deceptive for
//!   MCGS (the gadget at the base is what the estimate misranks).
//!
//! Selection rule, stated because the curves are conditional on it. Ground
//! truth is explicitly pair-mode root Exact with `exact_pruning` on, under
//! `EXACT_GUARD`; an instance that does not finish is dropped. The
//! plan called for a 10 ms hardness floor as well, and the calibration sweep
//! (`calibrate_hardness`) shows why this harness does not apply one by
//! default: in the predecessor campaign the cyclic
//! families are microseconds wide open
//! (crossover at `cycles=20` is 0.3 ms, mixed at `cycles=24` is 0.4 ms), so a
//! 10 ms floor would have selected the `width` and `ac` families and nothing
//! else. The floor is therefore a reported stratification rather than an
//! exclusion: every kept instance carries its `exact_ms`, `HARD_EXACT_MS`
//! marks the hard subset the wall-clock-normalized tables are computed on, and
//! `$AU_MIN_EXACT_MS` reinstates a hard floor for anyone who wants the
//! selected corpus instead.
//! Those timing numbers predate `exact_fixed.rs`; rerun the complete corpus on
//! one current build before treating them as current evidence.
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
//! AU_BENCH_DIR=doc/benchmarks/records/au AU_CORPUS_SECS=21600 \
//!   cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
//!   -- --ignored --nocapture
//! ```
//!
//! `$AU_LADDER_TOP` raises the top of the playout ladder (default 2^14) and
//! `$AU_FAMILIES` restricts the run to a comma-separated family list, which is
//! how the deep families' certification knees were measured past the default
//! ladder; the CSV name follows `$AU_CSV_NAME` (default `corpus.csv`) so such
//! a run does not overwrite the main one. `$AU_CLOSED_BIT` runs MCGS with the
//! closed bit on and `$AU_HYBRID=T` runs it with the hybrid exact trigger at
//! reachable-pair threshold `T`: both are
//! different solver configurations, so each belongs in its own CSV, never
//! mixed into a flag-off one.

use std::fs;
use std::io::Write as _;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use semi_persistent_egraph::au::census::{Census, certification_budget};
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::au::space::CycleMode;
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::nodes::ENodeId64;
use semi_persistent_egraph::{EGraph31, EGraph63};

#[path = "au_deceptive.rs"]
#[allow(dead_code)]
mod families;

use families::{
    DeceptiveParams, Instance, MixedParams, WideParams, build_deceptive, build_mixed,
    build_wide_deceptive, case_seed,
};

type Eg = EGraph31<NiraLitVal, false, false>;

/// Ground-truth guard. Projection pruning plus context subsumption put the
/// crossover family's `cycles=10` instance
/// at 3.6 ms where the unpruned solver timed out at 30 s, so a minute of
/// pruned exact reaches a substantially wider instance range.
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
            cycle_mode: CycleMode::Pair,
            exact_pruning: true,
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
    hybrid_calls: u64,
    hybrid_ms: f64,
}

/// Whether this run measures MCGS with the closed bit on (`$AU_CLOSED_BIT`,
/// default off). The flag changes which subgraphs selection may
/// enter, so a flag-on run is a separate CSV, never mixed into a flag-off one.
fn closed_bit() -> bool {
    std::env::var("AU_CLOSED_BIT").is_ok_and(|v| v != "0")
}

/// Live-incumbent arm pruning for this run: `$AU_LIVE_PRUNE` set and
/// nonzero turns the flag on. Requires `$AU_CLOSED_BIT` (the run refuses the
/// combination otherwise, by the flag's own contract). A flag-on run is a
/// separate CSV.
fn live_prune() -> bool {
    std::env::var("AU_LIVE_PRUNE").is_ok_and(|v| v != "0")
}

/// Scaled exact-cost grid: `$AU_SCALED_EXACT_GRID` set and
/// nonzero swaps the `wide`, `width` and `ac` grids for scaled-up ones, so
/// the ladder measures the regime where exact costs tens-to-hundreds of ms.
/// A scaled-grid run is a separate CSV; the 60 s guards and
/// `$AU_MIN_EXACT_MS` apply unchanged.
fn scaled_exact_grid() -> bool {
    std::env::var("AU_SCALED_EXACT_GRID").is_ok_and(|v| v != "0")
}

/// Hybrid exact threshold for this run: `$AU_HYBRID` unset or
/// `0` leaves the trigger off, any other value is the reachable-pair threshold
/// it fires at. Same rule as the closed bit: a flag-on run is a separate CSV.
fn hybrid_threshold() -> Option<u64> {
    let value: u64 = std::env::var("AU_HYBRID").ok()?.parse().ok()?;
    (value > 0).then_some(value)
}

/// The second admission gate: `$AU_HYBRID_ACTIONS` is the
/// action-count ceiling (unset = `u64::MAX`, rectangle-only admission).
fn hybrid_action_threshold() -> u64 {
    std::env::var("AU_HYBRID_ACTIONS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(u64::MAX)
}

/// The in-call backstop: `$AU_HYBRID_NODES` is the node-entry
/// budget per hybrid call (unset or 0 = unbounded).
fn hybrid_node_budget() -> Option<u64> {
    let value: u64 = std::env::var("AU_HYBRID_NODES").ok()?.parse().ok()?;
    (value > 0).then_some(value)
}

/// `$AU_ROLLOUT_HYBRID` fires the hybrid trigger inside the
/// initial rollout too (requires `$AU_HYBRID`).
fn rollout_hybrid() -> bool {
    std::env::var("AU_ROLLOUT_HYBRID").is_ok_and(|v| v != "0")
}

/// `$AU_SESSION_MEMO` shares clean exact solves across
/// hybrid calls (requires `$AU_HYBRID`).
fn session_memo() -> bool {
    std::env::var("AU_SESSION_MEMO").is_ok_and(|v| v != "0")
}

/// `$AU_STATIC_SEED` seeds fresh children statically and
/// defers their rollout to first selection.
fn static_seed() -> bool {
    std::env::var("AU_STATIC_SEED").is_ok_and(|v| v != "0")
}

/// `$AU_INTERVALS` makes arm bounds dynamic (requires
/// `$AU_LIVE_PRUNE`).
fn intervals() -> bool {
    std::env::var("AU_INTERVALS").is_ok_and(|v| v != "0")
}

fn run_mcgs(label: &str, build: Builder, playouts: u64) -> Option<McgsMeasurement> {
    let closed_bit = closed_bit();
    let hybrid = hybrid_threshold();
    let live_prune = live_prune();
    let rollout = rollout_hybrid();
    let memo = session_memo();
    let action_threshold = hybrid_action_threshold();
    let node_budget = hybrid_node_budget();
    let seed = static_seed();
    let iv = intervals();
    run_guarded(
        format!("au-mcgs-{label}-p{playouts}"),
        MCGS_GUARD,
        move || {
            let inst = build();
            let snap = AuSnapshot::new(&inst.eg).unwrap();
            let cfg = AuConfig {
                algorithm: AuAlgorithm::Uct,
                playouts,
                closed_bit,
                hybrid_exact: hybrid.is_some(),
                hybrid_threshold: hybrid.unwrap_or(0),
                live_incumbent_pruning: live_prune,
                rollout_hybrid: rollout && hybrid.is_some(),
                session_exact_memo: memo && hybrid.is_some(),
                hybrid_action_threshold: action_threshold,
                hybrid_node_budget: node_budget,
                static_child_seed: seed,
                interval_bounds: iv,
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
                hybrid_calls: result.hybrid.calls,
                hybrid_ms: result.hybrid.time.as_secs_f64() * 1e3,
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

/// Random control stratum: the same backbones with no planted gadget.
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
    let spines: &[(usize, usize)] = if scaled_exact_grid() {
        &[(12, 512), (16, 512), (16, 1024), (20, 1024)]
    } else {
        &[
            (2, 32),
            (4, 32),
            (4, 64),
            (8, 64),
            (4, 128),
            (8, 128),
            (12, 128),
            (4, 256),
            (8, 256),
            (12, 256),
        ]
    };
    for &(depth, width) in spines {
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
    let (depths, widths): (&[usize], &[usize]) = if scaled_exact_grid() {
        (&[16, 24, 32], &[256, 512, 1024])
    } else {
        (&[4, 8, 12], &[16, 32, 64, 128, 256])
    };
    for &depth in depths {
        for &width in widths {
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
    let (member_grid, child_grid): (&[usize], &[usize]) = if scaled_exact_grid() {
        (&[128, 192, 256, 384], &[12, 16, 24])
    } else {
        (&[24, 48, 64, 96, 128], &[4, 8, 12])
    };
    for &members in member_grid {
        for &children in child_grid {
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

// ---------------------------------------------------------------------------
// Saturated if-then-else funnel family.
// Built by ACTUAL SATURATION: user rules saturate the e-graph before
// anti-unification, the announced workflow, which none of the other families
// exercises. Guard swap is the width source: saturating k nested guards
// enumerates guard orderings (the BDD variable-ordering explosion), and that
// is also the realistic source of variation, since two independent
// formalizations of the same sentence nest conditions in different orders.
// ---------------------------------------------------------------------------

/// One backbone decision tree of depth `k` over guards `G0..Gk-1`, with one
/// distinct leaf atom per truth assignment; `left` reads the guards in
/// ascending order, `right` in descending order with `edits` leaves
/// redirected to fresh atoms (the planted variation points). Both sides
/// saturate under branch-swap, redundant-guard and guard-swap rules for
/// `cap` iterations. The planted optimum, valid once saturation has made the
/// two guard orders coincide, from the projection identity
/// `size = size(proj_L) + size(proj_R) - #backbone`: each side projects to
/// one full decision tree (`2 * (2^k - 1)` internal-plus-guard nodes and
/// `2^k` leaves), the backbone is everything except the edited leaves, so
/// each edit adds exactly one node over the tree:
/// `2 * (2^k - 1) + 2^k + edits`. Validated against exact on small k by
/// `sat_ite_planted_optimum_matches_exact`.
fn sat_ite_predicted_optimum(k: usize, edits: usize) -> u32 {
    let leaves = 1u32 << k;
    2 * (leaves - 1) + leaves + edits as u32
}

fn sat_ite_term(
    order: &[usize],
    assignment_prefix: usize,
    level: usize,
    edited: &[usize],
) -> String {
    if level == order.len() {
        // Leaf atom index = the truth assignment in backbone guard order.
        if edited.contains(&assignment_prefix) {
            format!("(B{assignment_prefix})")
        } else {
            format!("(A{assignment_prefix})")
        }
    } else {
        let guard = order[level];
        // The assignment bit is recorded at the BACKBONE position of the
        // guard, so both sides compute the same backbone leaf for the same
        // semantic branch.
        let then_branch = sat_ite_term(order, assignment_prefix | (1 << guard), level + 1, edited);
        let else_branch = sat_ite_term(order, assignment_prefix, level + 1, edited);
        format!("(Ite (G{guard}) {then_branch} {else_branch})")
    }
}

/// The program text both builders run: declarations, the width-producing
/// rewrites, the two guard orders, and the saturation cap.
fn sat_ite_program(k: usize, edits: usize, cap: usize) -> String {
    let leaves = 1usize << k;
    let mut decls = String::from("(datatype B (Ite B B B) (Not B)");
    for g in 0..k {
        decls.push_str(&format!(" (G{g})"));
    }
    for a in 0..leaves {
        decls.push_str(&format!(" (A{a})"));
    }
    // Edited leaves use B<assignment> atoms; declare one per edited slot,
    // indexed by the assignment it replaces so the name is stable.
    let edited: Vec<usize> = (0..edits).map(|e| e * (leaves / edits.max(1))).collect();
    for &a in &edited {
        decls.push_str(&format!(" (B{a})"));
    }
    decls.push_str(")\n");

    let rules = "\
(rewrite (Ite (Not c) t e) (Ite c e t))\n\
(rewrite (Ite c (Ite c t u) e) (Ite c t e))\n\
(rewrite (Ite c t (Ite c u e)) (Ite c t e))\n\
(rewrite (Ite c1 (Ite c2 a b) (Ite c2 x y)) (Ite c2 (Ite c1 a x) (Ite c1 b y)))\n\
(rewrite (Not (Ite c t e)) (Ite c (Not t) (Not e)))\n";

    let asc: Vec<usize> = (0..k).collect();
    let desc: Vec<usize> = (0..k).rev().collect();
    let left = sat_ite_term(&asc, 0, 0, &[]);
    let right = sat_ite_term(&desc, 0, 0, &edited);
    format!("{decls}{rules}(let L {left})\n(let R {right})\n(run {cap})\n")
}

/// `sat-ite` with `blind`'s decoy arms grafted on: the family the hybrid claim
/// needs, where the greedy rollout is wrong AND exact does not scale.
///
/// Neither existing family is in that intersection. `blind` makes greedy wrong
/// but its class product is linear in the depth, so exact finishes in
/// milliseconds. `sat-ite` makes exact blow up but greedy already returns the
/// optimum, so section (k)'s ablation showed delegation buying nothing that
/// more rollouts do not buy for free.
///
/// The composition keeps `sat-ite`'s two guard orders untouched, so exact faces
/// the same class product, and unions a decoy arm into the classes along the
/// leftmost path AFTER saturation, so the decoy is inert and cannot be
/// rewritten. A decoy arm is a pair of chains over different unary operators,
/// `P^S(X)` on the left and `Q^S(Y)` on the right. The three conditions are
/// `blind`'s, restated at each level's own optimum `W`:
///
///   attract   the pair's generalize cost `2S + 2` is BELOW the winner's
///             estimate (about `2W`), so the rollout prefers the decoy;
///   decoy     `2S + 2` is ABOVE the winner's true cost `W`, since chains over
///             different operators share no structure and pay both sides;
///   shallow   the arm is a linear chain, so exact refutes it in time linear in
///             `S` even though exact on the whole instance times out. This is
///             what delegation is supposed to exploit.
///
/// Both hold for `(W - 2) / 2 < S < W - 1`; `S = 2W / 3` sits inside for every
/// `W > 6`, which is the same two-thirds ratio `build_blind` uses.
///
/// `levels` decoys nest along the leftmost path, one per ITE level, so escaping
/// them requires rejecting all of them. That is the property section (k) found
/// missing: on `sat-ite` greedy is only wrong until the next rollout, while
/// here the chance a uniform rollout avoids every decoy decays with `levels`.
fn sat_decoy_program(
    k: usize,
    edits: usize,
    cap: usize,
    levels: usize,
    num: usize,
    den: usize,
) -> String {
    let leaves = 1usize << k;
    let mut decls = String::from("(datatype B (Ite B B B) (Not B) (P B) (Q B)");
    // One base atom per level per side. A shared base would defeat the
    // construction: chain lengths halve as the levels descend, so every
    // level's spine would hash-cons to a prefix of level 0's, the arms would
    // share structure with each other, and the decoy stops being structure-free
    // relative to the winner. Measured: with a shared base, `levels = 2` and
    // `levels = 4` both returned the optimum at one playout while `levels = 1`
    // was wrong by 18 to 20%.
    for lvl in 0..levels.min(k) {
        decls.push_str(&format!(" (X{lvl}) (Y{lvl})"));
    }
    for g in 0..k {
        decls.push_str(&format!(" (G{g})"));
    }
    for a in 0..leaves {
        decls.push_str(&format!(" (A{a})"));
    }
    let edited: Vec<usize> = (0..edits).map(|e| e * (leaves / edits.max(1))).collect();
    for &a in &edited {
        decls.push_str(&format!(" (B{a})"));
    }
    decls.push_str(")\n");

    let rules = "\
(rewrite (Ite (Not c) t e) (Ite c e t))\n\
(rewrite (Ite c (Ite c t u) e) (Ite c t e))\n\
(rewrite (Ite c t (Ite c u e)) (Ite c t e))\n\
(rewrite (Ite c1 (Ite c2 a b) (Ite c2 x y)) (Ite c2 (Ite c1 a x) (Ite c1 b y)))\n\
(rewrite (Not (Ite c t e)) (Ite c (Not t) (Not e)))\n";

    let asc: Vec<usize> = (0..k).collect();
    let desc: Vec<usize> = (0..k).rev().collect();
    let left = sat_ite_term(&asc, 0, 0, &[]);
    let right = sat_ite_term(&desc, 0, 0, &edited);
    let mut prog = format!("{decls}{rules}(let L {left})\n(let R {right})\n(run {cap})\n");

    // Chain length per level, from the decoyed subtree's own optimum. The arm
    // hangs off the THEN child at spine level `lvl`, which carries
    // `k - lvl - 1` remaining guards.
    let chain_len = |lvl: usize| -> usize {
        let sub_leaves = 1usize << (k - lvl);
        let w = 3 * sub_leaves - 2;
        (w * num) / den
    };
    // Two independent spines per level, built with flat `let` bindings rather
    // than nested application: at these lengths a single nested term would
    // drive the recursive-descent parser thousands of frames deep.
    //
    // Unioned after `(run cap)`, so no rule ever sees a decoy: the arms change
    // what AU may choose, not what saturation derives.
    for lvl in 0..levels.min(k) {
        let s = chain_len(lvl);
        prog.push_str(&format!(
            "(let PL{lvl}_0 (X{lvl}))\n(let QR{lvl}_0 (Y{lvl}))\n"
        ));
        for i in 1..=s {
            prog.push_str(&format!("(let PL{lvl}_{i} (P PL{lvl}_{}))\n", i - 1));
            prog.push_str(&format!("(let QR{lvl}_{i} (Q QR{lvl}_{}))\n", i - 1));
        }
        // The node AT spine level `lvl`. Hanging the arm off that level's THEN
        // child instead was measured and rejected: at every chain length from
        // 2/3 to 5x the subtree optimum, the arm was either cheap enough to
        // become the optimum (exact fell from 191 to 160) or expensive enough
        // that the rollout ignored it (greedy returned 191 at one playout).
        // There was no length in between, so a THEN-child arm cannot be a decoy
        // here. Spine placement has the window, and `levels = 1` puts the arm
        // at the root.
        let l_sub = sat_ite_term(&asc, 0, lvl, &[]);
        let r_sub = sat_ite_term(&desc, 0, lvl, &edited);
        prog.push_str(&format!("(union {l_sub} PL{lvl}_{s})\n"));
        prog.push_str(&format!("(union {r_sub} QR{lvl}_{s})\n"));
    }
    prog
}

fn build_sat_decoy(
    k: usize,
    edits: usize,
    cap: usize,
    levels: usize,
    num: usize,
    den: usize,
) -> Instance {
    use semi_persistent_egraph::interpret::Interpreter;
    use semi_persistent_egraph::literal::NiraModel;
    use semi_persistent_egraph::nodes::DefaultConfig;

    let program = sat_decoy_program(k, edits, cap, levels, num, den);
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&program)
        .expect("sat-decoy program parses");
    let mut interp =
        Interpreter::<DefaultConfig, NiraLitVal, NiraModel, false, false>::new(NiraModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("sat-decoy program sortchecks");
    interp
        .run_checked(&checked)
        .expect("sat-decoy program runs");
    let (left, _) = interp.global("L").expect("global L bound");
    let (right, _) = interp.global("R").expect("global R bound");
    eprintln!(
        "sat-decoy k={k} e={edits} cap={cap} L={levels} chain={num}/{den}: nodes={} classes={}",
        interp.eg.node_count(),
        interp.eg.class_count(),
    );
    Instance {
        eg: interp.eg,
        left,
        right,
    }
}

/// A `Config64` e-graph has 63-bit AU arenas. `build_sat_ite` builds on the
/// 31-bit default, which a `k = 12` instance exhausts: its search space passes
/// 2^31 spans and the arena traps with "span start ... exceeds the configured
/// AU capacity". That trap is the width guard working, so the large instances
/// run on this binding instead.
pub struct Instance64 {
    pub eg: EGraph63<NiraLitVal, false, false>,
    pub left: ENodeId64,
    pub right: ENodeId64,
}

fn build_sat_ite_64(k: usize, edits: usize, cap: usize) -> Instance64 {
    use semi_persistent_egraph::interpret::Interpreter;
    use semi_persistent_egraph::literal::NiraModel;
    use semi_persistent_egraph::nodes::Config64;

    let program = sat_ite_program(k, edits, cap);
    let cmds =
        semi_persistent_egraph::parser::parse_program_v2(&program).expect("sat-ite program parses");
    let mut interp = Interpreter::<Config64, NiraLitVal, NiraModel, false, false>::new(NiraModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("sat-ite program sortchecks");
    interp.run_checked(&checked).expect("sat-ite program runs");
    let (left, _) = interp.global("L").expect("global L bound");
    let (right, _) = interp.global("R").expect("global R bound");
    eprintln!(
        "sat-ite(63-bit) k={k} edits={edits} cap={cap}: nodes={} classes={} saturated={}",
        interp.eg.node_count(),
        interp.eg.class_count(),
        interp.last_sat().map(|s| s.saturated).unwrap_or(false),
    );
    Instance64 {
        eg: interp.eg,
        left,
        right,
    }
}

fn build_sat_ite(k: usize, edits: usize, cap: usize) -> Instance {
    use semi_persistent_egraph::interpret::Interpreter;
    use semi_persistent_egraph::literal::NiraModel;
    use semi_persistent_egraph::nodes::DefaultConfig;

    let program = sat_ite_program(k, edits, cap);
    let cmds =
        semi_persistent_egraph::parser::parse_program_v2(&program).expect("sat-ite program parses");
    let mut interp =
        Interpreter::<DefaultConfig, NiraLitVal, NiraModel, false, false>::new(NiraModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("sat-ite program sortchecks");
    interp.run_checked(&checked).expect("sat-ite program runs");

    let (left_node, _) = interp.global("L").expect("global L bound");
    let (right_node, _) = interp.global("R").expect("global R bound");
    // Realized width, the honest knob report: rules decide it, not the spec.
    eprintln!(
        "sat-ite k={k} edits={edits} cap={cap}: nodes={} classes={} saturated={}",
        interp.eg.node_count(),
        interp.eg.class_count(),
        interp.last_sat().map(|s| s.saturated).unwrap_or(false),
    );
    Instance {
        eg: interp.eg,
        left: left_node,
        right: right_node,
    }
}

/// The sat-ite grid, env-gated (`$AU_SAT_ITE`): a new family changes the
/// instance set of every run that includes it, so it stays out of the
/// default corpus unless explicitly enabled.
fn sat_ite_specs() -> Vec<Spec> {
    if !std::env::var("AU_SAT_ITE").is_ok_and(|v| v != "0") {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut i = 0usize;
    for &k in &[6usize, 8, 10] {
        for &edits in &[1usize, 2] {
            for &cap in &[6usize, 10] {
                out.push(Spec {
                    id: format!("sat-{i:02}"),
                    family: "sat",
                    params: format!("k{k}e{edits}c{cap}"),
                    build: Arc::new(move || build_sat_ite(k, edits, cap)),
                    exempt: true,
                });
                i += 1;
            }
        }
    }
    out
}

/// Warm-start control: on the sat-ite funnel, compare (a) cold exact,
/// (b) session MCGS at one
/// playout with the full flag set, and (c) exact warm-started with (b)'s
/// incumbent and memo, all under the exact guard. If (c) also clears the
/// funnel, the honest claim is "probes make exact feasible" and the write-up
/// says that. Run with:
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
///   warm_start_control -- --ignored --nocapture
/// ```
#[test]
#[ignore = "manual report; prints the warm-start table"]
fn warm_start_control() {
    use semi_persistent_egraph::au::session::SearchSession;
    println!(
        "{:12} {:>10} {:>10} {:>10} {:>6} {:>6} {:>6}",
        "instance", "cold_ms", "mcgs1_ms", "warm_ms", "cold✓", "mcgs✓", "warm✓"
    );
    for &(k, edits, cap) in &[
        (8usize, 1usize, 6usize),
        (8, 2, 6),
        (10, 1, 6),
        (10, 2, 6),
        (10, 1, 10),
        (10, 2, 10),
    ] {
        let inst = build_sat_ite(k, edits, cap);
        let snap = AuSnapshot::new(&inst.eg).unwrap();

        // (a) cold exact, pruned + subsumed, under the guard as a deadline.
        let start = Instant::now();
        let cold = anti_unify(
            &snap,
            inst.left,
            inst.right,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                cycle_mode: CycleMode::Pair,
                exact_pruning: true,
                exact_deadline: Some(EXACT_GUARD),
                ..Default::default()
            },
        )
        .unwrap();
        let cold_ms = start.elapsed().as_secs_f64() * 1e3;
        let cold_exact = cold.completion == Completion::Exact;

        // (b) one playout of the full MCGS configuration on a session, then
        // (c) warm exact on the same session (incumbent + memo carried over).
        let mut session = SearchSession::new(&snap, Default::default());
        let cfg = AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 1,
            closed_bit: true,
            live_incumbent_pruning: true,
            hybrid_exact: true,
            hybrid_threshold: 4096,
            rollout_hybrid: true,
            session_exact_memo: true,
            static_child_seed: true,
            ..Default::default()
        };
        let start = Instant::now();
        let (_, mcgs_completion) = session
            .run_uct(
                inst.left,
                inst.right,
                &semi_persistent_egraph::au::mcgs::McgsConfig {
                    playouts: cfg.playouts,
                    closed_bit: cfg.closed_bit,
                    live_incumbent_pruning: cfg.live_incumbent_pruning,
                    hybrid_exact: cfg.hybrid_exact,
                    hybrid_threshold: cfg.hybrid_threshold,
                    rollout_hybrid: cfg.rollout_hybrid,
                    session_exact_memo: cfg.session_exact_memo,
                    static_child_seed: cfg.static_child_seed,
                    ..Default::default()
                },
            )
            .unwrap();
        let mcgs_ms = start.elapsed().as_secs_f64() * 1e3;

        let start = Instant::now();
        let (_, warm_completion) = session
            .run_exact_warm(inst.left, inst.right, true, true, Some(EXACT_GUARD))
            .unwrap();
        let warm_ms = start.elapsed().as_secs_f64() * 1e3;

        println!(
            "sat-k{k}e{edits}c{cap} planted={} {cold_ms:>10.1} {mcgs_ms:>10.1} {warm_ms:>10.1} {:>6} {:>6} {:>6}",
            sat_ite_predicted_optimum(k, edits),
            cold_exact,
            mcgs_completion == Completion::Exact,
            warm_completion == Completion::Exact,
        );
    }
}

/// Hard-funnel regression: the regime where exact is infeasible and the planted value is the only
/// ground truth. `k=10, edits=2, cap=6` is that cell: the corpus run records
/// its exact solve timing out at the 60 s guard (an unsaturated cap leaves
/// the two guard orders only partly merged, which is harder than the
/// saturated `cap=10` instance exact finishes in 35 ms). MCGS must return
/// the planted optimum at one playout, in single-digit milliseconds.
#[test]
fn sat_ite_mcgs_reaches_planted_optimum_where_exact_times_out() {
    let inst = build_sat_ite(10, 2, 6);
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let start = Instant::now();
    let result = anti_unify(
        &snap,
        inst.left,
        inst.right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 1,
            closed_bit: true,
            live_incumbent_pruning: true,
            hybrid_exact: true,
            hybrid_threshold: 4096,
            rollout_hybrid: true,
            session_exact_memo: true,
            static_child_seed: true,
            ..Default::default()
        },
    )
    .unwrap();
    let ms = start.elapsed().as_secs_f64() * 1e3;
    let planted = sat_ite_predicted_optimum(10, 2);
    println!(
        "sat k10e2c6: one playout -> size {} (planted {planted}) in {ms:.1} ms",
        result.size
    );
    assert_eq!(
        result.size, planted,
        "one playout did not reach the planted optimum on the cell where exact times out"
    );
    assert!(
        ms < 100.0,
        "one playout took {ms:.1} ms; the anytime claim needs it far below exact's 60 s guard"
    );
}

/// The crossover study (the paper's two tables): map where exact wins and
/// where it stops scaling, on one parameterized family, with ground truth that
/// survives exact timing out.
///
/// The axis is the auto-formalization one: `cap` is how much saturation was
/// spent reconciling the two sides, `edits` is how far apart they are. The
/// planted optimum is known by construction, so the anytime columns are
/// measurable past the point where exact stops answering.
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
///   crossover_study -- --ignored --nocapture
/// ```
#[test]
#[ignore = "manual report; prints the crossover tables"]
fn crossover_study() {
    // Where exact stops being the answer, measured rather than assumed.
    const EXACT_GUARD_MS: f64 = 60_000.0;
    // Anytime thresholds, as a fraction above the planted optimum.
    const BANDS: [f64; 5] = [0.50, 0.20, 0.10, 0.05, 0.0];

    println!(
        "{:12} {:>6} {:>7} {:>10} {:>9} | {:>8} {:>8} {:>8} {:>8} {:>8} | {:>9}",
        "instance",
        "exact",
        "planted",
        "exact_ms",
        "status",
        "<=50%",
        "<=20%",
        "<=10%",
        "<=5%",
        "optimal",
        "playouts"
    );

    // Only caps at which the planted optimum is reachable: below 6 the guard
    // orders are still unmerged, the true optimum is larger than the planted
    // value, and a gap measured against it is meaningless
    // (`sat_ite_planted_vs_exact` records the deltas).
    for &k in &[8usize, 10, 12] {
        for &cap in &[6usize, 10] {
            // The cap that suffices at k <= 10 does not scale with k: at
            // k = 12 the instance is 1.1M nodes and still unsaturated at cap 6,
            // exact returns 24572 against a planted 12287, and MCGS proves 14599
            // feasible. The planted value is therefore not the optimum there.
            // `sat_ite_planted_vs_exact_64` records this.
            if k >= 12 && cap < 10 {
                continue;
            }
            for &edits in &[1usize, 2, 4] {
                if edits >= (1 << k) {
                    continue;
                }
                // Above k = 10 the 31-bit AU arenas are exhausted, so those
                // instances run on the 63-bit binding. Both paths measure the
                // same program; only the id width differs.
                let wide = k > 10;
                let inst = (!wide).then(|| build_sat_ite(k, edits, cap));
                let inst64 = wide.then(|| build_sat_ite_64(k, edits, cap));
                let snap31 = inst.as_ref().map(|i| AuSnapshot::new(&i.eg).unwrap());
                let snap64 = inst64.as_ref().map(|i| AuSnapshot::new(&i.eg).unwrap());
                let planted = sat_ite_predicted_optimum(k, edits);

                macro_rules! solve {
                    ($cfg:expr) => {
                        match (&snap31, &snap64) {
                            (Some(s), _) => {
                                let i = inst.as_ref().unwrap();
                                let r = anti_unify(s, i.left, i.right, &$cfg).unwrap();
                                (r.size, r.completion)
                            }
                            (_, Some(s)) => {
                                let i = inst64.as_ref().unwrap();
                                let r = anti_unify(s, i.left, i.right, &$cfg).unwrap();
                                (r.size, r.completion)
                            }
                            _ => unreachable!("one binding is always built"),
                        }
                    };
                }

                // Exact, under the guard.
                let start = Instant::now();
                let (exact_size, exact_completion) = solve!(AuConfig {
                    algorithm: AuAlgorithm::Exact,
                    cycle_mode: CycleMode::Pair,
                    exact_pruning: true,
                    exact_deadline: Some(EXACT_GUARD),
                    ..Default::default()
                });
                let exact_ms = start.elapsed().as_secs_f64() * 1e3;
                let exact_done = exact_completion == Completion::Exact;

                // MCGS + exact on shallow subproblems, walking the ladder and
                // recording the first budget that lands inside each band. Time
                // is cumulative across the ladder, which is what an anytime
                // consumer actually pays.
                let mut hit = [None::<(f64, u64)>; BANDS.len()];
                let mut cumulative = 0.0;
                let mut playouts = 1u64;
                while playouts <= 4096 {
                    let start = Instant::now();
                    let (size, _) = solve!(AuConfig {
                        algorithm: AuAlgorithm::Uct,
                        playouts,
                        closed_bit: true,
                        live_incumbent_pruning: true,
                        interval_bounds: true,
                        hybrid_exact: true,
                        hybrid_threshold: 4096,
                        rollout_hybrid: true,
                        session_exact_memo: true,
                        ..Default::default()
                    });
                    cumulative += start.elapsed().as_secs_f64() * 1e3;
                    let gap = (size as f64 - planted as f64) / planted as f64;
                    for (i, band) in BANDS.iter().enumerate() {
                        if hit[i].is_none() && gap <= *band + 1e-12 {
                            hit[i] = Some((cumulative, playouts));
                        }
                    }
                    if hit[BANDS.len() - 1].is_some() {
                        break;
                    }
                    playouts *= 2;
                }

                let cell = |i: usize| match hit[i] {
                    Some((ms, _)) => format!("{ms:8.1}"),
                    None => "       -".to_owned(),
                };
                let at_opt = match hit[BANDS.len() - 1] {
                    Some((_, p)) => format!("{p:9}"),
                    None => "        -".to_owned(),
                };
                println!(
                    "k{k:<2}e{edits}c{cap:<2} {:>6} {planted:>7} {exact_ms:>10.1} {:>9} | {} {} {} {} {} | {}",
                    exact_size,
                    if exact_done { "ok" } else { "TIMEOUT" },
                    cell(0),
                    cell(1),
                    cell(2),
                    cell(3),
                    cell(4),
                    at_opt
                );
            }
        }
    }
    println!(
        "\nexact_ms is wall clock under a {EXACT_GUARD_MS:.0} ms guard; the band columns are \
         cumulative MCGS+exact milliseconds to first reach that gap against the PLANTED \
         optimum, which is ground truth whether or not exact finished."
    );
}

/// Is the planted optimum reachable at a given saturation cap? The planted
/// formula assumes saturation merged the two guard orders; under a small cap
/// it has not, so the planted value may be below anything achievable and is
/// then invalid as ground truth. Prints exact's answer beside it.
#[test]
#[ignore = "diagnostic"]
fn sat_ite_planted_vs_exact() {
    println!(
        "{:12} {:>8} {:>8} {:>8} {:>9}",
        "cell", "planted", "exact", "delta", "complete"
    );
    for &(k, edits, cap) in &[
        (8usize, 1usize, 2usize),
        (8, 1, 4),
        (8, 1, 6),
        (8, 4, 6),
        (10, 1, 2),
        (10, 1, 4),
        (10, 1, 6),
    ] {
        let inst = build_sat_ite(k, edits, cap);
        let snap = AuSnapshot::new(&inst.eg).unwrap();
        let planted = sat_ite_predicted_optimum(k, edits);
        let r = anti_unify(
            &snap,
            inst.left,
            inst.right,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                cycle_mode: CycleMode::Pair,
                exact_pruning: true,
                exact_deadline: Some(EXACT_GUARD),
                ..Default::default()
            },
        )
        .unwrap();
        println!(
            "k{k}e{edits}c{cap:<4} {planted:>8} {:>8} {:>8} {:>9}",
            r.size,
            r.size as i64 - planted as i64,
            r.completion == Completion::Exact
        );
    }
}

/// The same ground-truth validation at k = 12, on the 63-bit binding. The
/// planted value is only the true optimum once saturation has merged the guard
/// orders; below that cap the construction's target is not representable and
/// every distance-to-optimum reading against it is meaningless. This prints
/// exact's answer and, when exact does not finish, a value MCGS proved
/// feasible, so an unreachable cap is visible rather than inferred.
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
///   sat_ite_planted_vs_exact_64 -- --ignored --nocapture
/// ```
#[test]
#[ignore = "long-running manual report with guarded exact searches"]
fn sat_ite_planted_vs_exact_64() {
    println!(
        "{:12} {:>8} {:>8} {:>9} {:>10} {:>9}",
        "cell", "planted", "exact", "complete", "feasible", "verdict"
    );
    for &(k, edits, cap) in &[(12usize, 1usize, 6usize), (12, 1, 10), (12, 2, 10)] {
        let inst = build_sat_ite_64(k, edits, cap);
        let snap = AuSnapshot::new(&inst.eg).unwrap();
        let planted = sat_ite_predicted_optimum(k, edits);
        let exact = anti_unify(
            &snap,
            inst.left,
            inst.right,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                cycle_mode: CycleMode::Pair,
                exact_pruning: true,
                exact_deadline: Some(EXACT_GUARD),
                ..Default::default()
            },
        )
        .unwrap();
        let feasible = anti_unify(
            &snap,
            inst.left,
            inst.right,
            &AuConfig {
                algorithm: AuAlgorithm::Uct,
                playouts: 256,
                ..Default::default()
            },
        )
        .unwrap();
        let proven = exact.completion == Completion::Exact;
        // A feasible value below the planted target refutes the target: the
        // planted optimum cannot be the minimum if a smaller term exists, and
        // an exact answer above a feasible one means exact did not finish.
        let verdict = if proven && exact.size == planted {
            "verified"
        } else if proven {
            "PLANTED WRONG"
        } else if feasible.size < exact.size {
            "UNVERIFIED"
        } else {
            "inconclusive"
        };
        println!(
            "k{k}e{edits}c{cap:<4} {planted:>8} {:>8} {proven:>9} {:>10} {verdict:>9}",
            exact.size, feasible.size,
        );
    }
}

/// Ablation: what actually finds the optimum at one playout? Compares the
/// bare greedy rollout, the rollout with exact delegation, and the full
/// configuration, on the cells where exact does not finish. If the bare
/// rollout already wins, the search is not the contribution.
#[test]
#[ignore = "manual report; prints the one-playout ablation"]
fn one_playout_ablation() {
    println!(
        "{:12} {:>8} | {:>9} {:>8} | {:>9} {:>8} | {:>9} {:>8}",
        "cell", "planted", "greedy", "ms", "+delegate", "ms", "full", "ms"
    );
    for &(k, edits, cap) in &[
        (8usize, 1usize, 6usize),
        (8, 4, 6),
        (8, 8, 6),
        (10, 2, 6),
        (10, 4, 6),
        (10, 8, 6),
        (10, 4, 10),
    ] {
        let inst = build_sat_ite(k, edits, cap);
        let snap = AuSnapshot::new(&inst.eg).unwrap();
        let planted = sat_ite_predicted_optimum(k, edits);

        let run = |cfg: AuConfig| {
            let start = Instant::now();
            let r = anti_unify(&snap, inst.left, inst.right, &cfg).unwrap();
            (r.size, start.elapsed().as_secs_f64() * 1e3)
        };

        // Bare greedy: one playout, every optional rule off.
        let (greedy, greedy_ms) = run(AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 1,
            ..Default::default()
        });
        // The same, plus exact delegation from inside the rollout.
        let (delegated, delegated_ms) = run(AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 1,
            hybrid_exact: true,
            hybrid_threshold: 4096,
            rollout_hybrid: true,
            ..Default::default()
        });
        // Everything on, as the crossover study runs it.
        let (full, full_ms) = run(AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 1,
            closed_bit: true,
            live_incumbent_pruning: true,
            interval_bounds: true,
            hybrid_exact: true,
            hybrid_threshold: 4096,
            rollout_hybrid: true,
            session_exact_memo: true,
            ..Default::default()
        });
        let mark = |v: u32| if v == planted { "=opt" } else { "" };
        println!(
            "k{k}e{edits}c{cap:<4} {planted:>8} | {greedy:>5}{:>4} {greedy_ms:>8.1} | \
             {delegated:>5}{:>4} {delegated_ms:>8.1} | {full:>5}{:>4} {full_ms:>8.1}",
            mark(greedy),
            mark(delegated),
            mark(full)
        );
    }
}

/// Does the `sat-decoy` composition actually sit in the intersection? Runs at a
/// size where exact still certifies, so every question has ground truth:
///
///   1. is the greedy rollout wrong (its answer above exact's)?
///   2. do more rollouts fix it, as they did on `sat-ite`?
///   3. does delegation fix it, which is what the hybrid claim needs?
///
/// `levels = 0` is the decoy-free control, and must reproduce plain `sat-ite`.
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
///   sat_decoy_probe -- --ignored --nocapture
/// ```
#[test]
#[ignore = "manual report; prints the sat-decoy control table"]
fn sat_decoy_probe() {
    println!(
        "{:14} {:>7} {:>8} {:>8} {:>8} {:>8} {:>8}",
        "cell", "exact", "greedy1", "greedy16", "greedy256", "full1", "full16"
    );
    for &(k, edits, cap) in &[(6usize, 1usize, 10usize), (8, 1, 10)] {
        for &(levels, num, den) in &[
            (0usize, 2usize, 3usize),
            (1, 1, 3),
            (1, 1, 2),
            (1, 2, 3),
            (1, 5, 6),
            (1, 1, 1),
            (1, 3, 2),
        ] {
            let inst = build_sat_decoy(k, edits, cap, levels, num, den);
            let snap = AuSnapshot::new(&inst.eg).unwrap();
            let exact = anti_unify(
                &snap,
                inst.left,
                inst.right,
                &AuConfig {
                    algorithm: AuAlgorithm::Exact,
                    cycle_mode: CycleMode::Pair,
                    exact_pruning: true,
                    exact_deadline: Some(EXACT_GUARD),
                    ..Default::default()
                },
            )
            .unwrap();
            let run = |playouts: u64, hybrid: bool| {
                anti_unify(
                    &snap,
                    inst.left,
                    inst.right,
                    &AuConfig {
                        algorithm: AuAlgorithm::Uct,
                        playouts,
                        hybrid_exact: hybrid,
                        hybrid_threshold: if hybrid { 4096 } else { 0 },
                        rollout_hybrid: hybrid,
                        ..Default::default()
                    },
                )
                .unwrap()
                .size
            };
            let tag = if exact.completion == Completion::Exact {
                ""
            } else {
                "*"
            };
            println!(
                "k{k}e{edits}L{levels}r{num}/{den:<3} {:>6}{tag} {:>8} {:>8} {:>8} {:>8} {:>8}",
                exact.size,
                run(1, false),
                run(16, false),
                run(256, false),
                run(1, true),
                run(16, true),
            );
        }
    }
    println!("* = exact did not certify within the guard");
}

/// `sat-decoy` at the scale where exact does not finish. The probe establishes
/// that the root decoy misleads the rollout and leaves the optimum unchanged;
/// this asks the two questions the hybrid claim turns on, at k = 10 cap 6 where
/// exact times out:
///
///   does the decoy survive more rollouts, which is what defeated `sat-ite`?
///   does delegation beat the bare rollout at EQUAL WALL CLOCK, not just at
///   equal playouts, which is what section (k) found it failing to do?
///
/// `levels = 0` is the decoy-free control and reproduces plain `sat-ite`.
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
///   sat_decoy_ladder -- --ignored --nocapture
/// ```
#[test]
#[ignore = "long-running manual report with guarded exact searches"]
fn sat_decoy_ladder() {
    // `edits = 1` is not in the intersection: exact certifies k = 10 cap 6 in
    // 21 ms there. Exact only stops finishing once the two sides disagree in
    // several places, which is what `edits` controls.
    for &(k, edits, cap) in &[(10usize, 2usize, 6usize), (10, 4, 6)] {
        for &levels in &[0usize, 1] {
            let inst = build_sat_decoy(k, edits, cap, levels, 2, 3);
            let snap = AuSnapshot::new(&inst.eg).unwrap();
            let planted = sat_ite_predicted_optimum(k, edits);
            let start = Instant::now();
            let exact = anti_unify(
                &snap,
                inst.left,
                inst.right,
                &AuConfig {
                    algorithm: AuAlgorithm::Exact,
                    cycle_mode: CycleMode::Pair,
                    exact_pruning: true,
                    exact_deadline: Some(EXACT_GUARD),
                    ..Default::default()
                },
            )
            .unwrap();
            let exact_ms = start.elapsed().as_secs_f64() * 1e3;
            println!(
                "\nk{k} e{edits} cap{cap} levels={levels}  planted {planted}  \
                 exact {} in {exact_ms:.0} ms ({})",
                exact.size,
                if exact.completion == Completion::Exact {
                    "certified"
                } else {
                    "TIMEOUT"
                },
            );
            println!(
                "{:>9} | {:>8} {:>9} | {:>8} {:>9}",
                "playouts", "greedy", "ms", "full", "ms"
            );
            for playouts in [1u64, 4, 16, 64, 256] {
                let run = |cfg: AuConfig| {
                    let t = Instant::now();
                    let r = anti_unify(&snap, inst.left, inst.right, &cfg).unwrap();
                    (r.size, t.elapsed().as_secs_f64() * 1e3)
                };
                let (bare, bare_ms) = run(AuConfig {
                    algorithm: AuAlgorithm::Uct,
                    playouts,
                    ..Default::default()
                });
                let (full, full_ms) = run(AuConfig {
                    algorithm: AuAlgorithm::Uct,
                    playouts,
                    closed_bit: true,
                    live_incumbent_pruning: true,
                    interval_bounds: true,
                    hybrid_exact: true,
                    hybrid_threshold: 4096,
                    rollout_hybrid: true,
                    session_exact_memo: true,
                    ..Default::default()
                });
                let pct = |v: u32| (v as f64 / planted as f64 - 1.0) * 100.0;
                println!(
                    "{playouts:>9} | {bare:>5}{:+4.0}% {bare_ms:>9.1} | {full:>5}{:+4.0}% {full_ms:>9.1}",
                    pct(bare),
                    pct(full)
                );
            }
        }
    }
}

/// The deciding experiment: at the scale where MCGS is NOT optimal on the
/// first playout, does the search plus delegation beat the bare greedy
/// rollout? Below k = 12 every configuration returns the optimum immediately,
/// so the ablation cannot separate them; here it can.
///
/// The planted value is not the optimum at this cap
/// (`sat_ite_planted_vs_exact_64` refutes it: exact times out at 24572 while
/// MCGS proves 14599 feasible), so the printed percentages are distances to a
/// construction target, not to the optimum. Two readings are valid anyway:
/// the three configurations run on the same e-graph, so comparing them to each
/// other is sound at equal playouts and at equal wall clock; and any value
/// below exact's timed-out answer is a proved improvement on it.
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
///   deep_ablation -- --ignored --nocapture
/// ```
#[test]
#[ignore = "manual report; prints the deep-instance ablation"]
fn deep_ablation() {
    for &(k, edits, cap) in &[(12usize, 1usize, 6usize), (12, 4, 6)] {
        let inst = build_sat_ite_64(k, edits, cap);
        let snap = AuSnapshot::new(&inst.eg).unwrap();
        let planted = sat_ite_predicted_optimum(k, edits);
        println!(
            "\nk{k}e{edits}c{cap}  planted {planted}\n{:>9} | {:>9} {:>9} | {:>9} {:>9} | {:>9} {:>9}",
            "playouts", "greedy", "ms", "+delegate", "ms", "full", "ms"
        );

        for playouts in [1u64, 4, 16, 64, 256] {
            let run = |cfg: AuConfig| {
                let start = Instant::now();
                let r = anti_unify(&snap, inst.left, inst.right, &cfg).unwrap();
                (r.size, start.elapsed().as_secs_f64() * 1e3)
            };
            let (bare, bare_ms) = run(AuConfig {
                algorithm: AuAlgorithm::Uct,
                playouts,
                ..Default::default()
            });
            let (deleg, deleg_ms) = run(AuConfig {
                algorithm: AuAlgorithm::Uct,
                playouts,
                hybrid_exact: true,
                hybrid_threshold: 4096,
                rollout_hybrid: true,
                ..Default::default()
            });
            let (full, full_ms) = run(AuConfig {
                algorithm: AuAlgorithm::Uct,
                playouts,
                closed_bit: true,
                live_incumbent_pruning: true,
                interval_bounds: true,
                hybrid_exact: true,
                hybrid_threshold: 4096,
                rollout_hybrid: true,
                session_exact_memo: true,
                ..Default::default()
            });
            let pct = |v: u32| (v as f64 / planted as f64 - 1.0) * 100.0;
            println!(
                "{playouts:>9} | {bare:>6}{:+5.0}% {bare_ms:>9.1} | {deleg:>6}{:+5.0}% {deleg_ms:>9.1} | {full:>6}{:+5.0}% {full_ms:>9.1}",
                pct(bare),
                pct(deleg),
                pct(full)
            );
        }
    }
}

/// Ground-truth validation: on small instances with a generous cap, the
/// saturation completes and the exact optimum must equal the planted
/// arithmetic. The planted value is only trusted at scale because this holds
/// where exact is feasible.
#[test]
fn sat_ite_planted_optimum_matches_exact() {
    for &(k, edits) in &[(2usize, 1usize), (3, 1), (3, 2)] {
        let inst = build_sat_ite(k, edits, 12);
        let snap = AuSnapshot::new(&inst.eg).unwrap();
        let cfg = AuConfig {
            algorithm: AuAlgorithm::Exact,
            cycle_mode: CycleMode::Pair,
            exact_pruning: true,
            ..Default::default()
        };
        let result = anti_unify(&snap, inst.left, inst.right, &cfg).unwrap();
        assert_eq!(
            result.size,
            sat_ite_predicted_optimum(k, edits),
            "k={k} edits={edits}: exact disagrees with the planted arithmetic"
        );
    }
}

// ---------------------------------------------------------------------------
// The `blind` family: a decoy the static bound cannot see.
//
// Live-incumbent pruning excludes an arm when `1 + Σ lb_pair(child)` exceeds the node's
// incumbent, and `lb_pair = max(bs_l, bs_r) + 1`. That test sees a decoy
// whose children are LARGE, because the bound grows with them. It is blind
// to a decoy whose children are moderate in size but structurally unrelated,
// because then the bound stays near `max(bs) + 1` while the true
// anti-unifier is about `bs_l + bs_r`: the whole cost of a decoy is the
// variant it is forced into, and the static bound never charges for that.
//
// Each level offers two routes out of the same class pair:
//
//   win  : `w(m, next)` where the two `m` sides are the same chain shape
//          over different atoms, so the pair anti-unifies tightly and its
//          static bound is nearly exact;
//   decoy: `d(c)` where the two `c` sides are chains of the SAME size built
//          from DIFFERENT unary operators, so no structural action applies,
//          the node is terminal at the generalize value `bs_l + bs_r`, and
//          its static bound is barely half of that.
//
// The decoy's size is chosen per level so that
// `static bound < win cost < true decoy cost`: the static test cannot exclude the arm at
// any budget, while one expansion under `interval_bounds` learns the
// terminal child's exact floor, lifts the arm above the incumbent, and kills
// it permanently. Chaining the gadget to depth d is what separates the two:
// budget exponential in d against budget linear in d.
//
// The shape is the auto-formalization case where a pairing looks plausible
// (same size, same position) and is only revealed to be semantically
// unrelated once its subterms are examined.
// ---------------------------------------------------------------------------

/// `op^len(atom)`, a chain of size `len + 1`.
fn blind_chain(eg: &mut Eg, op: OpId, atom: ENodeId, len: usize) -> ENodeId {
    let mut node = atom;
    for _ in 0..len {
        node = eg.add(op, &[node]);
    }
    node
}

fn build_blind(depth: usize, matched: usize) -> Instance {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let f = eg.register_op1("f", sort, sort);
    let g = eg.register_op1("g", sort, sort);
    let w = eg.register_op2("w", sort, sort, sort);

    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);

    // Unrelated-chain length. With `S` strictly between `matched / 2` and
    // `matched`, the level's three conditions all hold:
    //
    //   attract  : the decoy's rollout estimate `2(S+1)` is BELOW the
    //              winner's `2(matched+1)`, so greedy takes the decoy;
    //   decoy    : its true cost `2S+2` is ABOVE the winner's `matched+3`,
    //              because unrelated chains have no structural action and
    //              collapse to a variant of both sides;
    //   blind     : its static bound `S+2` is BELOW the winner's `matched+2`,
    //              so `1 + Σ lb_pair` can never exceed an incumbent the
    //              winner itself produced. No budget makes the static test exclude it.
    let unrelated = (2 * matched) / 3;

    let mut left = blind_chain(&mut eg, f, a, matched);
    let mut right = blind_chain(&mut eg, f, b, matched);
    // A second spine of the same shape, reachable only through the decoy
    // arms. Excluding a decoy therefore skips a whole region rather than a
    // single node, which is what makes the exclusion worth its bookkeeping.
    let mut junk_left = blind_chain(&mut eg, f, a, matched + 1);
    let mut junk_right = blind_chain(&mut eg, f, b, matched + 1);

    for _ in 0..depth {
        let m_left = blind_chain(&mut eg, f, a, matched);
        let m_right = blind_chain(&mut eg, f, b, matched);
        let u_left = blind_chain(&mut eg, f, a, unrelated);
        let u_right = blind_chain(&mut eg, g, b, unrelated);

        let win_left = eg.add(w, &[m_left, left]);
        let win_right = eg.add(w, &[m_right, right]);
        // The decoy carries the unrelated pair AND its own subtree.
        let decoy_left = eg.add(w, &[u_left, junk_left]);
        let decoy_right = eg.add(w, &[u_right, junk_right]);

        // Grow the junk spine in step so the region stays proportional.
        let jm_left = blind_chain(&mut eg, f, a, matched + 1);
        let jm_right = blind_chain(&mut eg, f, b, matched + 1);
        junk_left = eg.add(w, &[jm_left, junk_left]);
        junk_right = eg.add(w, &[jm_right, junk_right]);

        eg.merge(win_left, decoy_left);
        eg.merge(win_right, decoy_right);
        eg.rebuild();
        left = win_left;
        right = win_right;
    }
    eg.rebuild();
    Instance { eg, left, right }
}

/// Dynamic-interval acceptance: on the `blind`
/// family, count the EXACT playouts to a certificate with and without
/// `interval_bounds`, stepping one playout at a time instead of the
/// doubling ladder, which is too coarse to show the difference. The static bound alone
/// cannot exclude a `blind` decoy at any budget (its static bound sits below
/// every incumbent the winner can produce), so its certificate has to
/// realize both regions; intervals refute each decoy after one expansion.
///
/// ```text
/// cargo test -p semi-persistent-egraph --release --test au_corpus_bench \
///   blind_interval_certification -- --ignored --nocapture
/// ```
#[test]
#[ignore = "manual report; prints the interval-bound comparison"]
fn blind_interval_certification() {
    println!(
        "{:10} {:>9} {:>10} {:>10} {:>8}",
        "instance", "sum A(v)", "static", "interval", "speedup"
    );
    for &(depth, matched) in &[
        (2usize, 12usize),
        (4, 12),
        (6, 12),
        (8, 12),
        (10, 12),
        (12, 12),
        (16, 12),
        (6, 20),
        (10, 20),
    ] {
        let inst = build_blind(depth, matched);
        let snap = AuSnapshot::new(&inst.eg).unwrap();
        let sum_a = certification_budget(
            &snap,
            snap.class_of(inst.left).unwrap(),
            snap.class_of(inst.right).unwrap(),
            CycleMode::AncestorOnly,
            4_000_000,
            None,
        )
        .map(|c| c.sum_actions)
        .unwrap_or(0);

        // The certified size, so the table cannot report a speedup that came
        // from certifying something worse.
        let mut certified_size: Option<u32> = None;
        let mut first_cert = |intervals: bool| -> Option<u64> {
            let mut p = 1u64;
            while p <= 8192 {
                let r = anti_unify(
                    &snap,
                    inst.left,
                    inst.right,
                    &AuConfig {
                        algorithm: AuAlgorithm::Uct,
                        playouts: p,
                        closed_bit: true,
                        live_incumbent_pruning: true,
                        interval_bounds: intervals,
                        ..Default::default()
                    },
                )
                .unwrap();
                if r.completion == Completion::Exact {
                    match certified_size {
                        None => certified_size = Some(r.size),
                        Some(prev) => assert_eq!(
                            prev, r.size,
                            "d{depth}m{matched}: the two configurations certified different \
                             optima ({prev} and {}), so the interval bound pruned a winner",
                            r.size
                        ),
                    }
                    return Some(p);
                }
                p += if p < 64 { 1 } else { p / 8 };
            }
            None
        };
        let s1 = first_cert(false);
        let s6 = first_cert(true);
        let sp = match (s1, s6) {
            (Some(a), Some(b)) if b > 0 => format!("{:.2}x", a as f64 / b as f64),
            _ => "n/a".to_owned(),
        };
        println!(
            "d{depth}m{matched:<7} {sum_a:>9} {:>10} {:>10} {sp:>8}",
            s1.map(|v| v.to_string()).unwrap_or_else(|| ">4096".into()),
            s6.map(|v| v.to_string()).unwrap_or_else(|| ">4096".into()),
        );
    }
}

/// The `blind` grid, env-gated (`$AU_BLIND`).
fn blind_specs() -> Vec<Spec> {
    if !std::env::var("AU_BLIND").is_ok_and(|v| v != "0") {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut i = 0usize;
    for &depth in &[2usize, 4, 6, 8, 10, 12] {
        for &matched in &[12usize, 20] {
            out.push(Spec {
                id: format!("blind-{i:02}"),
                family: "blind",
                params: format!("d{depth}m{matched}"),
                build: Arc::new(move || build_blind(depth, matched)),
                exempt: true,
            });
            i += 1;
        }
    }
    out
}

/// Every stratum, interleaved round-robin.
fn corpus() -> Vec<Spec> {
    let mut streams: [std::vec::IntoIter<Spec>; 9] = [
        dec_specs().into_iter(),
        wide_specs().into_iter(),
        mixed_specs().into_iter(),
        rand_specs().into_iter(),
        xover_specs().into_iter(),
        width_specs().into_iter(),
        ac_specs().into_iter(),
        sat_ite_specs().into_iter(),
        blind_specs().into_iter(),
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
#[ignore = "corpus run: 1854 s release for the committed 673-instance run, writes \
            $AU_BENCH_DIR/corpus.csv (wall budget from $AU_CORPUS_SECS, default 3600 s)"]
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
          playouts,mcgs_ms,mcgs_size,mcgs_vmass,certified,hybrid_calls,hybrid_ms\n",
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
            println!("{id} [{family} {params}]: exact TIMEOUT({EXACT_GUARD:?}), skipped");
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
                println!("  {id} p={playouts}: MCGS TIMEOUT({MCGS_GUARD:?}), ladder stopped");
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
                     {playouts},{:.3},{},{},{},{},{:.3}\n",
                    exact.ms,
                    exact.size,
                    exact.vmass,
                    mcgs.ms,
                    mcgs.size,
                    mcgs.vmass,
                    mcgs.certified,
                    mcgs.hybrid_calls,
                    mcgs.hybrid_ms
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

/// Calibration for the hybrid trigger's threshold: per family,
/// the root's `reachable_pairs` estimate, the trigger's input, against what
/// the exact solver actually costs there and against `sum A(v)`. A threshold
/// is only usable if the estimate orders instances the way exact's cost does,
/// so this is the measurement that says which families the estimate protects
/// and which it does not. Not a corpus run.
#[test]
#[ignore = "hybrid threshold calibration; prints the trigger's estimate against exact's cost"]
fn calibrate_hybrid_threshold() {
    let mut probes: Vec<(String, Builder)> = Vec::new();
    for &(d, k) in &[(5usize, 1usize), (12, 2), (20, 4)] {
        let p = DeceptiveParams {
            burial_depth: d,
            margin: 2,
            gap: 2,
            decoys: k,
        };
        probes.push((
            format!("dec d{d}k{k}"),
            Arc::new(move || build_deceptive(p)),
        ));
    }
    for &c in &[6usize, 10] {
        let p = MixedParams {
            seed: case_seed(MIX_BASE, 4242),
            cycles: c,
            n_deceptive: 1,
            deceptive: DeceptiveParams {
                burial_depth: 8,
                margin: 3,
                gap: 2,
                decoys: 2,
            },
        };
        probes.push((format!("mixed c{c}"), Arc::new(move || build_mixed(p).0)));
    }
    for &(d, w) in &[(4usize, 16usize), (4, 64), (8, 64), (12, 256)] {
        probes.push((
            format!("width d{d}w{w}"),
            Arc::new(move || build_width(d, w)),
        ));
    }
    for &(m, c) in &[(24usize, 4usize), (64, 8), (128, 12)] {
        probes.push((format!("ac m{m}c{c}"), Arc::new(move || build_ac(m, c))));
    }
    for &(d, w) in &[(4usize, 32usize), (8, 128)] {
        let p = WideParams {
            depth: d,
            width: w,
            deceptive: DeceptiveParams {
                burial_depth: 8,
                margin: 2,
                gap: 2,
                decoys: 2,
            },
        };
        probes.push((
            format!("wide d{d}w{w}"),
            Arc::new(move || build_wide_deceptive(p)),
        ));
    }
    for &(d, w, c) in &[(4usize, 4usize, 8usize), (5, 8, 12)] {
        probes.push((
            format!("xover d{d}w{w}c{c}"),
            Arc::new(move || build_crossover(d, w, c)),
        ));
    }

    println!(
        "{:<16} {:>10} {:>11} {:>12} {:>10} {:>10}",
        "instance", "root est", "max acts", "sum_A", "exact ms", "est/act"
    );
    for (label, build) in probes {
        let inst = build();
        let snap = AuSnapshot::new(&inst.eg).unwrap();
        let l = snap.class_of(inst.left).unwrap();
        let r = snap.class_of(inst.right).unwrap();
        let est = semi_persistent_egraph::au::estimates::reachable_pairs(&snap, l, r);
        let census = certification_budget(
            &snap,
            l,
            r,
            CycleMode::AncestorOnly,
            CENSUS_MAX_STATES,
            Some(Instant::now() + CENSUS_GUARD),
        )
        .unwrap();
        let exact = run_exact(&label, Arc::clone(&build));
        println!(
            "{label:<16} {est:>10} {:>11} {:>12} {:>10} {:>10}",
            census.max_actions,
            if census.capped {
                format!("{}+", census.sum_actions)
            } else {
                census.sum_actions.to_string()
            },
            exact.map_or("TIMEOUT".to_string(), |m| format!("{:.2}", m.ms)),
            est.saturating_mul(census.max_actions),
        );
    }
}

/// Parameter calibration for the corpus grids: pruned exact wall time per
/// candidate parameter point, printed so the grids can be set against the
/// `MIN_EXACT_MS` floor and the `EXACT_GUARD` ceiling. Not a corpus run.
#[test]
#[ignore = "calibration sweep, 15 s release; prints pruned exact times per parameter point"]
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
