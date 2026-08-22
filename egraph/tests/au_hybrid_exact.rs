// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Hybrid exact subproblems.
//!
//! The closed bit makes the certification budget track `sum A(v)`: MCGS
//! still has to realize every action of every reachable OR node, it just
//! stops wasting playouts on the ones it already realized. Hybrid exact
//! solving removes actions
//! from that count instead of scheduling them better — a subproblem small
//! enough to solve outright is proved by one exact call and never enumerated,
//! and the proof enters the search as a node that is terminal at creation and
//! therefore closed at birth.
//!
//! What this suite asserts: the proof is sound at every budget (never better
//! than the exact optimum, and a certificate implies it), the answer at a
//! fixed budget never gets worse than the flag-off run's, and the knee moves
//! below the closed bit's own. `hybrid_threshold_sweep` is `#[ignore]`d and
//! measures rather than asserts; it is one of the two sweeps behind the
//! default threshold, the other being
//! `au_corpus_bench.rs::calibrate_hybrid_threshold`, and both are written up
//! in doc/benchmarks/records/au/anytime-corpus.md section (g).
//!
//! Budgets are the corpus ladder (powers of two), so a knee reported at `b`
//! means the certificate appeared in `(b/2, b]`.

use std::time::Instant;

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::census::certification_budget;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::estimates::reachable_pairs;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::au::space::CycleMode;
use semi_persistent_egraph::literal::NiraLitVal;

#[path = "au_deceptive.rs"]
#[allow(dead_code)]
mod families;

use families::{DeceptiveParams, Instance, MixedParams, build_deceptive, build_mixed, case_seed};

type Eg = EGraph31<NiraLitVal, false, false>;

const LADDER_TOP: u32 = 14;

/// The threshold this suite measures at: one below the instance's own root
/// estimate. `reachable_pairs` is monotone non-increasing down the search
/// graph — a child class reaches a subset of what its parent reaches — so this
/// is the largest threshold that excludes the root and admits every proper
/// subproblem. It isolates the hybrid claim (subproblems are proved instead of
/// enumerated) from the degenerate setting where the trigger simply solves the
/// whole instance, which `hybrid_threshold_sweep` measures separately.
fn subproblems_only(inst: &Instance) -> u64 {
    root_estimate(inst) - 1
}

#[derive(Clone, Copy)]
struct Flags {
    hybrid: bool,
    closed: bool,
    threshold: u64,
}

struct Run {
    size: u32,
    vmass: u32,
    certified: bool,
    calls: u64,
    proved: u64,
    hybrid_ms: f64,
    ms: f64,
}

fn run(inst: &Instance, playouts: u64, flags: Flags) -> Run {
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let start = Instant::now();
    let result = anti_unify(
        &snap,
        inst.left,
        inst.right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts,
            closed_bit: flags.closed,
            hybrid_exact: flags.hybrid,
            hybrid_threshold: flags.threshold,
            ..Default::default()
        },
    )
    .unwrap();
    let ms = start.elapsed().as_secs_f64() * 1e3;
    Run {
        size: result.size,
        vmass: result.pool.variant_mass(result.term_id),
        certified: result.completion == Completion::Exact,
        calls: result.hybrid.calls,
        proved: result.hybrid.proved,
        hybrid_ms: result.hybrid.time.as_secs_f64() * 1e3,
        ms,
    }
}

fn exact(inst: &Instance) -> (u32, u32) {
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let result = anti_unify(
        &snap,
        inst.left,
        inst.right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            cycle_mode: CycleMode::Pair,
            exact_pruning: true,
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(result.completion, Completion::Exact);
    (result.size, result.pool.variant_mass(result.term_id))
}

/// `sum A(v)`, computed without running either solver, with the census's own
/// cap flag: on the cyclic families the walk runs into its state cap and the
/// number is then a lower bound, which the sweep reports rather than asserts.
fn sum_actions(inst: &Instance) -> (u128, bool) {
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let l = snap.class_of(inst.left).unwrap();
    let r = snap.class_of(inst.right).unwrap();
    let census = certification_budget(
        &snap,
        l,
        r,
        CycleMode::AncestorOnly,
        4_000_000,
        Some(Instant::now() + std::time::Duration::from_secs(20)),
    )
    .unwrap();
    (census.sum_actions, census.capped)
}

/// The trigger's own input at the root: how big a rectangle of class pairs the
/// whole instance lives in.
fn root_estimate(inst: &Instance) -> u64 {
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let l = snap.class_of(inst.left).unwrap();
    let r = snap.class_of(inst.right).unwrap();
    reachable_pairs(&snap, l, r)
}

/// The smallest ladder budget that certifies, or `None` past the ladder.
fn knee(inst: &Instance, flags: Flags) -> Option<u64> {
    (0..=LADDER_TOP)
        .map(|k| 1u64 << k)
        .find(|&playouts| run(inst, playouts, flags).certified)
}

fn deceptive(burial_depth: usize, decoys: usize) -> Instance {
    build_deceptive(DeceptiveParams {
        burial_depth,
        margin: 2,
        gap: 2,
        decoys,
    })
}

fn mixed(seed: u64, cycles: usize, n_deceptive: usize) -> Instance {
    build_mixed(MixedParams {
        // The closed-bit suite's own base seed: the two suites then measure the
        // same instances, so their knee and gap numbers are comparable.
        seed: case_seed(0x0C10_5ED0_0000_0001, seed),
        cycles,
        n_deceptive,
        deceptive: DeceptiveParams {
            burial_depth: 5,
            margin: 2,
            gap: 2,
            decoys: 2,
        },
    })
    .0
}

fn closed(inst: &Instance) -> Flags {
    Flags {
        hybrid: false,
        closed: true,
        threshold: subproblems_only(inst),
    }
}

fn hybrid_closed(inst: &Instance) -> Flags {
    Flags {
        hybrid: true,
        closed: true,
        threshold: subproblems_only(inst),
    }
}

fn hybrid_only(inst: &Instance) -> Flags {
    Flags {
        hybrid: true,
        closed: false,
        threshold: subproblems_only(inst),
    }
}

/// The headline claim: on deep deceptive instances, proving every proper
/// subproblem instead of enumerating it certifies at strictly fewer playouts
/// than the closed bit alone. With the root itself above the threshold, what
/// is left for the playouts to realize is the root's own actions, so the knee
/// lands at the root's action count instead of at `sum A(v)`.
#[test]
fn hybrid_certifies_earlier_than_closed_alone() {
    let mut report = String::new();
    for burial_depth in [5, 8, 12, 16] {
        for decoys in [1, 2, 4] {
            let inst = deceptive(burial_depth, decoys);
            let (budget, capped) = sum_actions(&inst);
            assert!(!capped, "the census capped on a deceptive instance");
            let closed_knee =
                knee(&inst, closed(&inst)).expect("the closed bit certifies within the ladder");
            let hybrid_knee = knee(&inst, hybrid_closed(&inst))
                .expect("hybrid + the closed bit certifies within the ladder");
            let at = run(&inst, hybrid_knee, hybrid_closed(&inst));
            report.push_str(&format!(
                "  depth {burial_depth} decoys {decoys}: root est {}, sum A(v) {budget}, \
                 knee {closed_knee} -> {hybrid_knee}, {} exact calls ({} proved) in {:.3} ms of \
                 {:.3} ms\n",
                root_estimate(&inst),
                at.calls,
                at.proved,
                at.hybrid_ms,
                at.ms
            ));
            assert!(
                at.calls > 0,
                "depth {burial_depth} decoys {decoys}: the trigger never fired"
            );
            assert!(
                hybrid_knee < closed_knee,
                "depth {burial_depth} decoys {decoys}: hybrid certified at {hybrid_knee} \
                 playouts against the closed bit's {closed_knee}; proving every proper \
                 subproblem has to leave less to realize, not more"
            );
        }
    }
    println!("hybrid_certifies_earlier_than_closed_alone:\n{report}");
}

/// Soundness and the gap curve over acyclic (deceptive) and cyclic (mixed)
/// graphs at every rung, for hybrid alone and hybrid with the closed bit: MCGS
/// never beats the exact optimum, a certificate implies the exact quality
/// tuple, and no budget's answer is worse than the flag-off run's.
#[test]
fn hybrid_never_costs_quality() {
    let mut instances: Vec<(String, Instance)> = Vec::new();
    for burial_depth in [3, 8] {
        for decoys in [1, 2] {
            instances.push((
                format!("dec d{burial_depth} k{decoys}"),
                deceptive(burial_depth, decoys),
            ));
        }
    }
    for seed in 0..4 {
        instances.push((format!("mixed s{seed}"), mixed(seed, 3, 1)));
        instances.push((format!("rand s{seed}"), mixed(seed, 3, 0)));
    }

    let mut checked = 0usize;
    let mut improved = 0usize;
    let mut certified_earlier = 0usize;
    for (id, inst) in &instances {
        let (exact_size, exact_vmass) = exact(inst);
        let off = Flags {
            hybrid: false,
            closed: false,
            threshold: 0,
        };
        // Both regimes: the trigger restricted to proper subproblems, and the
        // shipped default, which on instances this small absorbs the root too.
        let default_threshold = Flags {
            hybrid: true,
            closed: true,
            threshold: AuConfig::default().hybrid_threshold,
        };
        let configs = [
            ("hybrid", hybrid_only(inst)),
            ("hybrid+closed", hybrid_closed(inst)),
            ("hybrid+closed default T", default_threshold),
        ];
        for k in 0..=LADDER_TOP {
            let playouts = 1u64 << k;
            let base = run(inst, playouts, off);
            for (label, flags) in configs {
                let on = run(inst, playouts, flags);
                checked += 1;
                assert!(
                    on.size >= exact_size,
                    "{id} {label} at {playouts} playouts: size {} beats the exact optimum \
                     {exact_size}",
                    on.size
                );
                if on.certified {
                    assert_eq!(
                        (on.size, on.vmass),
                        (exact_size, exact_vmass),
                        "{id} {label} at {playouts} playouts: Completion::Exact off the exact \
                         optimum"
                    );
                }
                assert!(
                    on.size <= base.size,
                    "{id} {label} at {playouts} playouts: size {} against the flag-off run's \
                     {}; a proved subproblem must not cost quality",
                    on.size,
                    base.size
                );
                assert!(
                    !base.certified || on.certified,
                    "{id} {label} at {playouts} playouts: the flag-off run certified and this \
                     one did not"
                );
                if on.size < base.size {
                    improved += 1;
                }
                if on.certified && !base.certified {
                    certified_earlier += 1;
                }
            }
        }
    }
    println!(
        "hybrid_never_costs_quality: {checked} (instance, budget, flags) triples, {improved} \
         strictly better, {certified_earlier} certified earlier"
    );
}

/// A proof is a proof regardless of which solver produced it: on a graph that
/// certifies both ways, the certified answers agree.
#[test]
fn hybrid_certified_answers_agree() {
    let mut eg = Eg::new();
    let int = eg.intern_sort("Int");
    let a_op = eg.register_op0("a", int);
    let b_op = eg.register_op0("b", int);
    let c_op = eg.register_op0("c", int);
    let f_op = eg.register_op2("f", int, int, int);
    let g_op = eg.register_op1("g", int, int);

    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let ga = eg.add(g_op, &[a]);
    let left = eg.add(f_op, &[ga, b]);
    let right = eg.add(f_op, &[ga, c]);
    eg.merge(b, ga);
    eg.rebuild();
    let inst = Instance { eg, left, right };

    let (exact_size, exact_vmass) = exact(&inst);
    for flags in [closed(&inst), hybrid_only(&inst), hybrid_closed(&inst)] {
        let got = run(&inst, 4096, flags);
        assert!(got.certified);
        assert_eq!((got.size, got.vmass), (exact_size, exact_vmass));
    }
}

/// The proof is written through to the session's result table, so a second run
/// on the same session inherits it: the trigger fires once and the re-run
/// certifies without calling exact again.
#[test]
fn hybrid_proof_is_written_through() {
    use semi_persistent_egraph::au::mcgs::McgsConfig;
    use semi_persistent_egraph::au::session::SearchSession;

    let inst = deceptive(8, 2);
    let threshold = subproblems_only(&inst);
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let mut session = SearchSession::new(&snap, CycleMode::AncestorOnly);
    let config = McgsConfig {
        playouts: 1 << LADDER_TOP,
        closed_bit: true,
        hybrid_exact: true,
        hybrid_threshold: threshold,
        ..Default::default()
    };

    let (_, first) = session.run_uct(inst.left, inst.right, &config).unwrap();
    assert_eq!(first, Completion::Exact);
    let after_first = session.hybrid_stats();
    assert!(after_first.calls > 0, "the trigger never fired");
    assert_eq!(after_first.calls, after_first.proved);

    let (_, second) = session.run_uct(inst.left, inst.right, &config).unwrap();
    assert_eq!(second, Completion::Exact);
    assert_eq!(
        session.hybrid_stats().calls,
        after_first.calls,
        "the second run re-solved subproblems the first one had already proved"
    );
}

/// The threshold sweep behind the default. Prints, per instance and threshold,
/// the certification knee, how many exact calls it took, and what share of the
/// run's wall time went into them; and the root estimate, which is the
/// threshold above which the trigger absorbs the whole instance in one call.
#[test]
#[ignore = "threshold sweep for the hybrid trigger; prints knee and time share per threshold"]
fn hybrid_threshold_sweep() {
    let mut instances: Vec<(String, Instance)> = Vec::new();
    for burial_depth in [5, 12, 20] {
        for decoys in [1, 2, 4] {
            instances.push((
                format!("dec d{burial_depth} k{decoys}"),
                deceptive(burial_depth, decoys),
            ));
        }
    }
    for cycles in [6, 8, 10] {
        for seed in 0..2 {
            instances.push((format!("mixed c{cycles} s{seed}"), mixed(seed, cycles, 1)));
            instances.push((format!("rand c{cycles} s{seed}"), mixed(seed, cycles, 0)));
        }
    }

    let thresholds = [0u64, 4, 16, 64, 256, 1024, 4096, 16384, 65536];
    println!(
        "{:<18} {:>10} {:>9} {:>7} {:>7} {:>8} {:>9} {:>8}",
        "instance", "threshold", "root est", "sum_A", "knee", "calls", "hybrid ms", "run ms"
    );
    for (id, inst) in &instances {
        let root = root_estimate(inst);
        let (budget, capped) = sum_actions(inst);
        let budget = if capped {
            format!("{budget}+")
        } else {
            budget.to_string()
        };
        for &threshold in &thresholds {
            let flags = Flags {
                hybrid: threshold > 0,
                closed: true,
                threshold,
            };
            let knee = knee(inst, flags);
            let at = run(inst, knee.unwrap_or(1 << LADDER_TOP), flags);
            println!(
                "{id:<18} {threshold:>10} {root:>9} {budget:>7} {:>7} {:>8} {:>9.3} {:>8.3}",
                knee.map_or("past".to_string(), |k| k.to_string()),
                at.calls,
                at.hybrid_ms,
                at.ms
            );
        }
    }
}
