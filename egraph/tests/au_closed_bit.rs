// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The MCTS-solver closed bit.
//!
//! The action census predicts that MCGS certifies wide, shallow search graphs within a factor
//! of 2 of `sum A(v)` and misses on deep, narrow ones by a factor that grows
//! with the burial depth, because UCB1 gives a worse-looking arm only
//! logarithmically many visits and MCGS keeps descending into subgraphs that
//! are already fully realized (doc/benchmarks/records/au/anytime-corpus.md). The closed bit
//! excludes those subgraphs from selection. This suite is where the claim is
//! asserted rather than measured: the knee has to move, the certificate has to
//! stay sound, and the answer at a fixed budget must not get worse.
//!
//! Every run here also exercises the flag's own oracle: with `closed_bit` on,
//! `run_mcgs_in` asserts in debug builds that the root's bit agrees with
//! `is_structurally_complete`, the exhaustive walk the flag-off path uses. The
//! corpus below covers acyclic, shared-DAG, and cyclic search graphs, so a
//! propagation bug on any of those shapes fails the suite in debug.
//!
//! Budgets are the corpus ladder (powers of two), so a knee reported at `b`
//! means the certificate appeared in `(b/2, b]`.

use std::time::Instant;

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::census::certification_budget;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::au::space::CycleMode;
use semi_persistent_egraph::literal::NiraLitVal;

#[path = "au_deceptive.rs"]
#[allow(dead_code)]
mod families;

use families::{DeceptiveParams, Instance, MixedParams, build_deceptive, build_mixed, case_seed};

type Eg = EGraph31<NiraLitVal, false, false>;

/// Top of the ladder. The flag-off deep-family knee is past 2^18 on the
/// committed corpus, so the ladder is not what this suite measures: a
/// flag-off instance that does not certify by 2^14 is reported as "past the
/// ladder", exactly as the corpus tables do.
const LADDER_TOP: u32 = 14;

struct Run {
    size: u32,
    vmass: u32,
    certified: bool,
}

fn run(inst: &Instance, playouts: u64, closed_bit: bool) -> Run {
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let result = anti_unify(
        &snap,
        inst.left,
        inst.right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts,
            closed_bit,
            ..Default::default()
        },
    )
    .unwrap();
    Run {
        size: result.size,
        vmass: result.pool.variant_mass(result.term_id),
        certified: result.completion == Completion::Exact,
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

/// `sum A(v)`, the census-based certification budget, computed without running
/// either solver.
fn sum_actions(inst: &Instance) -> u128 {
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
    assert!(!census.capped, "the census capped on a suite instance");
    census.sum_actions
}

/// The smallest ladder budget that certifies, or `None` past the ladder.
fn knee(inst: &Instance, closed_bit: bool) -> Option<u64> {
    (0..=LADDER_TOP)
        .map(|k| 1u64 << k)
        .find(|&playouts| run(inst, playouts, closed_bit).certified)
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

/// The headline claim: on the deceptive family the flag-on certification knee
/// tracks `sum A(v)` instead of growing with the burial depth. `sum A(v)` is a
/// lower bound on any certificate (one playout realizes at most one action),
/// so the assertion is two-sided: at or above `sum A(v)`, and within a small
/// multiple of it at every depth the flag-off run cannot pay for.
#[test]
fn closed_bit_certification_knee_tracks_sum_actions() {
    let mut report = String::new();
    for burial_depth in [3, 5, 8, 12] {
        for decoys in [1, 4] {
            let inst = deceptive(burial_depth, decoys);
            let budget = sum_actions(&inst);
            let before = knee(&inst, false);
            let after = knee(&inst, true).unwrap_or_else(|| {
                panic!(
                    "depth {burial_depth} decoys {decoys}: the closed bit did not certify \
                     within 2^{LADDER_TOP} playouts, sum A(v) = {budget}"
                )
            });
            report.push_str(&format!(
                "  depth {burial_depth} decoys {decoys}: sum A(v) {budget}, knee {} -> {after} \
                 ({:.2}x sum A(v))\n",
                before.map_or("past 2^14".to_string(), |b| b.to_string()),
                after as f64 / budget as f64,
            ));

            assert!(
                u128::from(after) >= budget,
                "depth {burial_depth} decoys {decoys}: certified at {after} playouts, below \
                 sum A(v) = {budget}; a certificate cannot cost less than the actions it has \
                 to realize"
            );
            // Factor 4 of `sum A(v)`, which is two ladder rungs: the corpus's
            // wide families sit at 1.0-2.0 and the ladder's own granularity is
            // a factor of 2.
            assert!(
                u128::from(after) <= 4 * budget,
                "depth {burial_depth} decoys {decoys}: certified at {after} playouts against \
                 sum A(v) = {budget}, past the factor-4 band the closed bit is supposed to \
                 hold on deep graphs"
            );
            if let Some(before) = before {
                assert!(
                    after <= before,
                    "depth {burial_depth} decoys {decoys}: the closed bit certified later \
                     ({after}) than the flag-off run ({before})"
                );
            }
        }
    }
    println!("closed_bit_certification_knee_tracks_sum_actions:\n{report}");
}

/// Soundness and the gap curve, over acyclic (deceptive) and cyclic (mixed)
/// search graphs at every rung of the ladder: MCGS never beats the exact
/// optimum, a certificate implies the exact quality tuple, and the answer at a
/// fixed budget is never worse than the flag-off run's.
#[test]
fn closed_bit_never_costs_quality() {
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

    let mut improved = 0usize;
    let mut certified_earlier = 0usize;
    let mut checked = 0usize;
    for (id, inst) in &instances {
        let (exact_size, exact_vmass) = exact(inst);
        for k in 0..=LADDER_TOP {
            let playouts = 1u64 << k;
            let off = run(inst, playouts, false);
            let on = run(inst, playouts, true);
            checked += 1;

            assert!(
                on.size >= exact_size,
                "{id} at {playouts} playouts: the closed bit reports size {} against the exact \
                 optimum {exact_size}",
                on.size
            );
            if on.certified {
                assert_eq!(
                    (on.size, on.vmass),
                    (exact_size, exact_vmass),
                    "{id} at {playouts} playouts: Completion::Exact off the exact optimum"
                );
            }
            assert!(
                on.size <= off.size,
                "{id} at {playouts} playouts: the closed bit returns size {} where the \
                 flag-off run returns {}; skipping resolved subgraphs must not cost quality",
                on.size,
                off.size
            );
            if on.size < off.size {
                improved += 1;
            }
            if on.certified && !off.certified {
                certified_earlier += 1;
            }
            assert!(
                !off.certified || on.certified,
                "{id} at {playouts} playouts: the flag-off run certified and the closed bit \
                 did not"
            );
        }
    }
    println!(
        "closed_bit_never_costs_quality: {checked} (instance, budget) pairs, {improved} \
         strictly better, {certified_earlier} certified earlier"
    );
}

/// The bit is a search-order change, not a semantic one: on a graph both
/// settings certify, the certified answers are the same term quality, and the
/// early stop the flag adds does not change it.
#[test]
fn closed_bit_certified_answers_agree() {
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
    let off = run(&inst, 4096, false);
    let on = run(&inst, 4096, true);
    assert!(off.certified && on.certified);
    assert_eq!((on.size, on.vmass), (exact_size, exact_vmass));
    assert_eq!((on.size, on.vmass), (off.size, off.vmass));
}
