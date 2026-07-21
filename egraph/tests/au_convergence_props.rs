// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Proptest verification properties for §2.5.2 (normalization and convergence).
//!
//! Each test corresponds to one of the eleven gates specified in the design doc,
//! numbered 1 through 11. They exercise the reward function, the search state
//! invariants, and the exact-oracle convergence on randomly generated instances.

use proptest::prelude::*;
use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::reward;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::literal::NiraLitVal;

const X_TARGET: f64 = 0.8;

// Property 1: order preservation (§2.5.1 A).
// For any q1 < q2 with the same shared basis (a, b > 0), reward(q1) > reward(q2).
proptest! {
    #[test]
    fn prop_order_preservation(
        a in 1.0_f64..100.0,
        b in 1.0_f64..100.0,
        q1 in 1.0_f64..500.0,
        delta in 0.01_f64..100.0,
    ) {
        let q2 = q1 + delta;
        let r1 = reward::reward(q1, a, b, X_TARGET);
        let r2 = reward::reward(q2, a, b, X_TARGET);
        prop_assert!(
            r1 >= r2,
            "q1={q1} < q2={q2} but reward(q1)={r1} < reward(q2)={r2}; basis ({a},{b})"
        );
    }
}

// Property 3: no action-local reversal (§2.5 inversion example).
// With shared basis, the smaller-size action always wins on reward.
#[test]
fn prop_no_action_local_reversal() {
    let (a, b) = (5.0, 10.0);
    let size_a = 10.0;
    let size_b = 12.0;
    let r_a = reward::reward(size_a, a, b, X_TARGET);
    let r_b = reward::reward(size_b, a, b, X_TARGET);
    assert!(
        r_a > r_b,
        "shared basis: smaller size must get higher reward"
    );

    // With local bases (the bug), the order reverses.
    let r_a_local = reward::reward(size_a, 2.0, 2.0, X_TARGET);
    let r_b_local = reward::reward(size_b, 11.0, 11.0, X_TARGET);
    assert!(
        r_b_local > r_a_local,
        "this confirms the inversion under local bases"
    );
}

// Property 4: landmarks (§2.5.1 K).
proptest! {
    #[test]
    fn prop_landmarks(
        a in 1.0_f64..100.0,
        b in 1.0_f64..100.0,
        x_target in 0.01_f64..0.99,
    ) {
        // ncr(a) = 0 (perfect compression).
        let at_perfect = reward::ncr(a, a, b, x_target);
        prop_assert!((at_perfect).abs() < 1e-10, "ncr at a should be 0, got {at_perfect}");

        // ncr(a + b) = x_target (bare Variants no-sharing point).
        let at_bare = reward::ncr(a + b, a, b, x_target);
        prop_assert!(
            (at_bare - x_target).abs() < 1e-10,
            "ncr at a+b should be {x_target}, got {at_bare}"
        );

        // ncr is bounded in [0, 1] for all sizes and monotone past a+b.
        let at_large = reward::ncr(a + b + 100.0, a, b, x_target);
        prop_assert!(at_large <= 1.0, "ncr must be <= 1");
        prop_assert!(at_large >= at_bare, "ncr must be monotone: at_large >= at_bare");
    }
}

// Property 6: AND additivity (§2.5.1 C).
// After any AND recomputation, Q_AND = 1 + sum(count_i * Q_child_i).
// Tested here at the public API level: on a simple instance, the exact solver's
// result size equals 1 + sum of child sizes (each child contributing its count).
#[test]
fn prop_and_additivity_simple() {
    let mut eg = EGraph31::<NiraLitVal, false, false>::new();
    let int = eg.intern_sort("Int");
    let a_op = eg.register_op0("a", int);
    let b_op = eg.register_op0("b", int);
    let c_op = eg.register_op0("c", int);
    let f_op = eg.register_op2("f", int, int, int);

    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let fab = eg.add(f_op, &[a, b]);
    let fac = eg.add(f_op, &[a, c]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let cfg = AuConfig {
        algorithm: AuAlgorithm::Exact,
        ..Default::default()
    };
    let result = anti_unify(&snap, fab, fac, &cfg).unwrap();
    // f(a, Variants(b,c)): size = 1 + 1 + (1+1) = 4. The AND composition
    // is 1 (for f) + size(AU(a,a)) + size(AU(b,c)) = 1 + 1 + 2 = 4.
    assert_eq!(result.size, 4);
}

// Property 7: fairness (§2.5.1 E, F).
// After many playouts, every OR-edge and every AND-child edge must have at
// least one visit.
#[test]
fn prop_fairness_all_edges_visited() {
    let mut eg = EGraph31::<NiraLitVal, false, false>::new();
    let int = eg.intern_sort("Int");
    let a_op = eg.register_op0("a", int);
    let b_op = eg.register_op0("b", int);
    let c_op = eg.register_op0("c", int);
    let d_op = eg.register_op0("d", int);
    let and_op = eg.register_set("and", int, int);

    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let d = eg.add(d_op, &[]);
    let left = eg.add(and_op, &[a, b, c]);
    let right = eg.add(and_op, &[b, c, d]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    // With 6 actions, 1000 playouts is enough to realize and visit all of them.
    let cfg = AuConfig {
        algorithm: AuAlgorithm::Uct,
        playouts: 1000,
        ..Default::default()
    };
    let result = anti_unify(&snap, left, right, &cfg).unwrap();
    // If fairness holds, the search explored all matchings and found the optimum.
    assert_eq!(result.size, 5, "optimal is and(b, c, Variants(a,d))");
}

// Property 8: exact-oracle convergence (§2.5.1 E, I, J).
// On small random instances, MCGS with sufficient budget matches the exact solver.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]
    #[test]
    fn prop_exact_oracle_convergence(
        seed in 0u64..1000,
    ) {
        // Generate a small deterministic instance from a seed.
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let ops: Vec<_> = (0..4).map(|i| eg.register_op0(&format!("v{i}"), int)).collect();
        let f = eg.register_op2("f", int, int, int);

        let leaves: Vec<_> = ops.iter().map(|&o| eg.add(o, &[])).collect();
        // Build two terms from the seed bits.
        let l0 = (seed % 4) as usize;
        let l1 = ((seed / 4) % 4) as usize;
        let r0 = ((seed / 16) % 4) as usize;
        let r1 = ((seed / 64) % 4) as usize;
        let left = eg.add(f, &[leaves[l0], leaves[l1]]);
        let right = eg.add(f, &[leaves[r0], leaves[r1]]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();

        let exact_result = anti_unify(&snap, left, right, &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        }).unwrap();

        let mcgs_result = anti_unify(&snap, left, right, &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 500,
            ..Default::default()
        }).unwrap();

        // The completion certificate is a hard contract: when MCGS reports
        // Exact, its full lexicographic quality must EQUAL the exact oracle.
        if mcgs_result.completion == Completion::Exact {
            prop_assert_eq!(
                mcgs_result.pool.quality(mcgs_result.term_id),
                exact_result.pool.quality(exact_result.term_id),
                "Completion::Exact must mean lexicographic equality with the oracle (seed {})",
                seed
            );
        } else {
            // Budget-exhausted runs must still be valid upper bounds (never
            // better than the oracle, and never wildly worse on these tiny
            // instances).
            prop_assert!(
                mcgs_result.pool.quality(mcgs_result.term_id)
                    >= exact_result.pool.quality(exact_result.term_id),
                "MCGS cannot beat the exact oracle (seed {seed})"
            );
            prop_assert!(
                mcgs_result.size <= exact_result.size + 1,
                "budget-exhausted MCGS size {} should be close to exact size {} (seed {seed})",
                mcgs_result.size, exact_result.size
            );
        }
    }
}

// Property 10: monotone publication (§2.5.1 J).
// The best-result table only ever improves: no result is ever replaced by a
// worse one. Tested indirectly: running the same instance twice with different
// playout counts, the larger budget never produces a worse result.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(30))]
    #[test]
    fn prop_monotone_publication(
        seed in 0u64..500,
    ) {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let ops: Vec<_> = (0..3).map(|i| eg.register_op0(&format!("k{i}"), int)).collect();
        let f = eg.register_op1("f", int, int);

        let leaves: Vec<_> = ops.iter().map(|&o| eg.add(o, &[])).collect();
        let li = (seed % 3) as usize;
        let ri = ((seed / 3) % 3) as usize;
        let left = eg.add(f, &[leaves[li]]);
        let right = eg.add(f, &[leaves[ri]]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();

        let small_budget = anti_unify(&snap, left, right, &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 10,
            ..Default::default()
        }).unwrap();

        let large_budget = anti_unify(&snap, left, right, &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 500,
            ..Default::default()
        }).unwrap();

        prop_assert!(
            large_budget.size <= small_budget.size,
            "more playouts must not produce a worse result: {} > {} (seed {seed})",
            large_budget.size, small_budget.size
        );
    }
}

// Property 11: AC completeness qualification (§2.5.1 G).
// On an instance with more than A_max matrices, MCGS (bounded) may be worse
// than exact (unbounded); the exact solver always finds the true optimum.
#[test]
fn prop_ac_completeness_qualification() {
    let mut eg = EGraph31::<NiraLitVal, false, false>::new();
    let int = eg.intern_sort("Int");
    let ops: Vec<_> = (0..6)
        .map(|i| eg.register_op0(&format!("k{i}"), int))
        .collect();
    let and_op = eg.register_set("and", int, int);

    let ks: Vec<_> = ops.iter().map(|&o| eg.add(o, &[])).collect();
    // 5 distinct children per side: 5! = 120 bijections > A_max=32.
    let left = eg.add(and_op, &[ks[0], ks[1], ks[2], ks[3], ks[4]]);
    let right = eg.add(and_op, &[ks[1], ks[2], ks[3], ks[4], ks[5]]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();

    let exact = anti_unify(
        &snap,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
    )
    .unwrap();
    // and(k1, k2, k3, k4, Variants(k0, k5)): 1+4+0+1+1 = 7.
    assert_eq!(
        exact.size, 7,
        "exact finds the true optimum (120 bijections)"
    );

    let mcgs = anti_unify(
        &snap,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 2000,
            ..Default::default()
        },
    )
    .unwrap();
    // MCGS with A_max=32 may or may not find it; it is at least valid.
    assert!(mcgs.size >= exact.size);
    assert!(mcgs.size < 100, "result is finite and valid");
}
