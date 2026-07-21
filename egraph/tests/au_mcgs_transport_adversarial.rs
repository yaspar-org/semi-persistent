// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Desired-contract regressions for confirmed MCGS transport-node defects.
//!
//! These tests are ignored while the defects remain. Run one directly with:
//! `cargo test -p semi-persistent-egraph --test au_mcgs_transport_adversarial \
//! <test-name> -- --ignored --exact --nocapture`.

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::au::space::CycleMode;
use semi_persistent_egraph::au::terms::TermOp;
use semi_persistent_egraph::literal::NiraLitVal;

type Eg = EGraph31<NiraLitVal, false, false>;

/// A transport improvement below an ordered parent must preserve the parent's
/// positional child order. The current fixed-AND expansion marks every operator
/// commutative, so backpropagation sorts `wrap(ac_result, k)` into
/// `wrap(k, ac_result)` and returns projections outside the two root classes.
#[test]
fn mcgs_transport_improvement_preserves_ordered_parent_positions() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let v1_op = eg.register_op0("v1", sort);
    let v2_op = eg.register_op0("v2", sort);
    let k_op = eg.register_op0("k", sort);
    let f_op = eg.register_op2("f", sort, sort, sort);
    let g_op = eg.register_op2("g", sort, sort, sort);
    let ac_op = eg.register_mset("ac", sort, sort);
    let wrap_op = eg.register_op2("wrap", sort, sort, sort);

    let v1 = eg.add(v1_op, &[]);
    let v2 = eg.add(v2_op, &[]);
    let k = eg.add(k_op, &[]);
    let x_f = eg.add(f_op, &[v1, v1]);
    let x_g = eg.add(g_op, &[v1, v1]);
    eg.merge(x_f, x_g);
    let y = eg.add(f_op, &[v1, v2]);
    let z = eg.add(g_op, &[v1, v2]);
    let left_ac = eg.add(ac_op, &[x_f, y]);
    let right_ac = eg.add(ac_op, &[x_f, z]);
    let left = eg.add(wrap_op, &[left_ac, k]);
    let right = eg.add(wrap_op, &[right_ac, k]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let result = anti_unify(
        &snap,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 1_000,
            ..Default::default()
        },
    )
    .unwrap();

    assert_eq!(*result.root_op(), TermOp::EGraph(wrap_op));
    let children = result.root_children();
    assert_eq!(children.len(), 2);
    assert_eq!(
        *result.pool.op(children[0]),
        TermOp::EGraph(ac_op),
        "ordered position 0 must remain the AC anti-unifier"
    );
    assert_eq!(
        *result.pool.op(children[1]),
        TermOp::EGraph(k_op),
        "ordered position 1 must remain k"
    );
}

/// CurrentInclusive blocks every transport cell whose left child is the current
/// left root. Exact therefore has no feasible structural transport and returns
/// the terminal generalize action. MCGS must obey that same blocked-cell mask so
/// both algorithms search the same action space under the same CycleMode.
#[test]
fn mcgs_transport_respects_current_inclusive_blocked_cells() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let p_op = eg.register_op0("p", sort);
    let q_op = eg.register_op0("q", sort);
    let a_op = eg.register_op0("a", sort);
    let c_op = eg.register_op0("c", sort);
    let f_op = eg.register_op2("f", sort, sort, sort);
    let ac_op = eg.register_mset("ac", sort, sort);

    let p = eg.add(p_op, &[]);
    let q = eg.add(q_op, &[]);
    let a = eg.add(a_op, &[]);
    let c = eg.add(c_op, &[]);
    let x = eg.add(f_op, &[p, q]);
    let x_cycle = eg.add(ac_op, &[x, a]);
    eg.merge(x, x_cycle); // X = f(p,q) = ac(X,a)
    eg.rebuild();
    let right = eg.add(ac_op, &[x, c]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let run = |algorithm| {
        anti_unify(
            &snap,
            x,
            right,
            &AuConfig {
                algorithm,
                cycle_mode: CycleMode::CurrentInclusive,
                playouts: 1_000,
                ..Default::default()
            },
        )
        .unwrap()
    };

    let exact = run(AuAlgorithm::Exact);
    let mcgs = run(AuAlgorithm::Uct);
    let exact_quality = exact.pool.quality(exact.term_id);
    let mcgs_quality = mcgs.pool.quality(mcgs.term_id);

    assert_eq!(
        exact_quality,
        (8, 8),
        "fixture must exercise the generalize action"
    );
    assert_eq!(
        mcgs_quality, exact_quality,
        "MCGS must obey the same cycle-filtered transport space as Exact"
    );
}

/// MCGS performs one mandatory action-aware initialization rollout even with a
/// zero playout budget. For an identity-padded AC singleton, static transport
/// selection and its chosen flow immediately expose
/// `combine(f(x), Variants(a,e))` at (5,2), rather than leaving only whole-term
/// generalization at (6,6).
#[test]
fn mcgs_initial_rollout_uses_identity_padded_transport() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let e_op = eg.register_op0("e", sort);
    let a_op = eg.register_op0("a", sort);
    let x_op = eg.register_op0("x", sort);
    let f_op = eg.register_op1("f", sort, sort);
    let combine = eg.register_mset("combine", sort, sort);

    let e = eg.add(e_op, &[]);
    eg.set_unit_node(combine, e);
    let a = eg.add(a_op, &[]);
    let x = eg.add(x_op, &[]);
    let fx = eg.add(f_op, &[x]);
    let left = eg.add(combine, &[a, fx]);
    let right = eg.add(combine, &[fx]);
    assert_eq!(right, fx, "singleton AC application must canonicalize away");
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let mut result = anti_unify(
        &snap,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 0,
            ..Default::default()
        },
    )
    .unwrap();

    assert_eq!(
        result.pool.quality(result.term_id),
        (5, 2),
        "the permanent first estimate must be the greedy identity-padded transport rollout"
    );
    assert_eq!(
        result.completion,
        Completion::BudgetExhausted { playouts_used: 0 }
    );
    let left_projection = result.pool.project(result.term_id, 0);
    let right_projection = result.pool.project(result.term_id, 1);
    assert!(!result.pool.has_variants(left_projection));
    assert!(!result.pool.has_variants(right_projection));
}

/// A fully cycle-blocked representation pair is not an action. This guards
/// against publishing a nullary AC term or selecting an empty AND node.
#[test]
fn mcgs_skips_fully_blocked_transport_representation() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let p_op = eg.register_op0("p", sort);
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let ac_op = eg.register_mset("ac", sort, sort);

    let p = eg.add(p_op, &[]);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let cycle = eg.add(ac_op, &[p, p]);
    eg.merge(p, cycle); // P = p = ac(P,P)
    eg.rebuild();
    let right = eg.add(ac_op, &[a, b]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let run = |algorithm, playouts| {
        anti_unify(
            &snap,
            p,
            right,
            &AuConfig {
                algorithm,
                cycle_mode: CycleMode::CurrentInclusive,
                playouts,
                ..Default::default()
            },
        )
        .unwrap()
    };

    let exact = run(AuAlgorithm::Exact, 0);
    let exact_quality = exact.pool.quality(exact.term_id);
    for playouts in [1, 2] {
        let mcgs = run(AuAlgorithm::Uct, playouts);
        assert_eq!(mcgs.pool.quality(mcgs.term_id), exact_quality);
    }
}

/// Having at least one legal cell does not make a transport network feasible.
/// Here the blocked P row has positive supply, while only the `a` row remains;
/// no flow can satisfy both right-hand columns. The representation pair must be
/// omitted before action counting so a zero-playout search is already complete.
#[test]
fn mcgs_skips_partially_allowed_hall_infeasible_transport() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let p_op = eg.register_op0("p", sort);
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let c_op = eg.register_op0("c", sort);
    let ac_op = eg.register_mset("ac", sort, sort);

    let p = eg.add(p_op, &[]);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let cycle = eg.add(ac_op, &[p, a]);
    eg.merge(p, cycle); // P = p = ac(P,a)
    eg.rebuild();
    let right = eg.add(ac_op, &[b, c]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let run = |algorithm| {
        anti_unify(
            &snap,
            p,
            right,
            &AuConfig {
                algorithm,
                cycle_mode: CycleMode::CurrentInclusive,
                playouts: 0,
                ..Default::default()
            },
        )
        .unwrap()
    };

    let exact = run(AuAlgorithm::Exact);
    let mcgs = run(AuAlgorithm::Uct);
    assert_eq!(
        mcgs.pool.quality(mcgs.term_id),
        exact.pool.quality(exact.term_id)
    );
    assert_eq!(
        mcgs.completion,
        semi_persistent_egraph::au::session::Completion::Exact,
        "an infeasible representation pair must not consume an MCGS action"
    );
}
