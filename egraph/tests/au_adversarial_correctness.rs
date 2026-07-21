// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Adversarial anti-unification correctness and soundness tests.
//!
//! Most tests marked `ignore` state the intended contract and currently fail
//! because they reproduce a known defect. The dangling-`TermId` characterization
//! is the deliberate exception: it catches and asserts the current panic, so it
//! passes only while that crash remains reproducible. Run a contract test with,
//! for example:
//! `cargo test -p semi-persistent-egraph --test au_adversarial_correctness \
//! exact_ac_vertex_oracle_finds_the_cross_matching -- --ignored --exact --nocapture`.

use std::collections::HashSet;

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::actions::{ActionCache, generate_actions};
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::results::BestResults;
use semi_persistent_egraph::au::session::{
    AuAlgorithm, AuConfig, AuResult, Completion, anti_unify,
};
use semi_persistent_egraph::au::space::{CycleMode, OrId};
use semi_persistent_egraph::au::terms::{TermId, TermOp, TermPool};
use semi_persistent_egraph::containers::DenseId;
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::nodes::LitValId;
use semi_persistent_egraph::registry::{AssocDir, Clamp, OpKind};

type Eg = EGraph31<NiraLitVal, false, false>;

/// Own a projected result so the snapshot/result borrows can end before we
/// materialize the projection back into the mutable e-graph.
#[derive(Clone, Debug)]
enum OwnedTerm {
    App(OpId, Vec<OwnedTerm>),
    Lit(OpId, LitValId),
}

fn own_projected(pool: &TermPool<OpId, LitValId>, id: TermId) -> OwnedTerm {
    match pool.op(id) {
        TermOp::EGraph(op) => OwnedTerm::App(
            *op,
            pool.children(id)
                .iter()
                .map(|&child| own_projected(pool, child))
                .collect(),
        ),
        TermOp::Literal(op, value) => OwnedTerm::Lit(*op, *value),
        TermOp::Variants => panic!("projection still contains Variants"),
    }
}

fn materialize(eg: &mut Eg, term: &OwnedTerm) -> ENodeId {
    match term {
        OwnedTerm::App(op, children) => {
            let child_ids: Vec<_> = children
                .iter()
                .map(|child| materialize(eg, child))
                .collect();
            eg.add(*op, &child_ids)
        }
        OwnedTerm::Lit(op, value) => eg.add_lit(*op, *value),
    }
}

fn projected_terms(
    mut result: AuResult<semi_persistent_egraph::nodes::DefaultConfig>,
) -> (OwnedTerm, OwnedTerm) {
    let left = result.pool.project(result.term_id, 0);
    let right = result.pool.project(result.term_id, 1);
    assert!(!result.pool.has_variants(left));
    assert!(!result.pool.has_variants(right));
    (
        own_projected(&result.pool, left),
        own_projected(&result.pool, right),
    )
}

fn assert_projection_membership(eg: &mut Eg, left: ENodeId, right: ENodeId) {
    for algorithm in [AuAlgorithm::Exact, AuAlgorithm::Uct] {
        let projections = {
            let snapshot = AuSnapshot::new(eg).unwrap();
            let result = anti_unify(
                &snapshot,
                left,
                right,
                &AuConfig {
                    algorithm,
                    playouts: 64,
                    ..Default::default()
                },
            )
            .unwrap();
            projected_terms(result)
        };

        let projected_left = materialize(eg, &projections.0);
        let projected_right = materialize(eg, &projections.1);
        eg.rebuild();
        assert_eq!(
            eg.find_const(projected_left),
            eg.find_const(left),
            "{algorithm:?} left projection did not land in its source e-class"
        );
        assert_eq!(
            eg.find_const(projected_right),
            eg.find_const(right),
            "{algorithm:?} right projection did not land in its source e-class"
        );
    }
}

/// The lower-ordered `g` representatives are larger than the `f`
/// representatives. A first-action rollout picks `g` and leaves only the
/// whole-term size-4 generalization, while the recorded initializer baseline
/// factors through `f` at quality (3, 2).
#[test]
fn zero_playout_uct_selects_better_later_operator_action() {
    const RECORDED_BASELINE: (u32, u32) = (3, 2);

    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let c_op = eg.register_op0("c", sort);
    let d_op = eg.register_op0("d", sort);
    let g = eg.register_op2("g", sort, sort, sort);
    let f = eg.register_op1("f", sort, sort);

    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let d = eg.add(d_op, &[]);
    let left = eg.add(f, &[a]);
    let left_g = eg.add(g, &[a, c]);
    eg.merge(left, left_g);
    let right = eg.add(f, &[b]);
    let right_g = eg.add(g, &[b, d]);
    eg.merge(right, right_g);
    eg.rebuild();

    let (quality, completion, projections) = {
        let snapshot = AuSnapshot::new(&eg).unwrap();
        let result = anti_unify(
            &snapshot,
            left,
            right,
            &AuConfig {
                algorithm: AuAlgorithm::Uct,
                playouts: 0,
                ..Default::default()
            },
        )
        .unwrap();
        let quality = result.pool.quality(result.term_id);
        let completion = result.completion;
        let projections = projected_terms(result);
        (quality, completion, projections)
    };

    assert!(
        quality <= RECORDED_BASELINE,
        "zero-playout initialization regressed past the recorded baseline: {quality:?}"
    );
    assert_eq!(completion, Completion::BudgetExhausted { playouts_used: 0 });

    let projected_left = materialize(&mut eg, &projections.0);
    let projected_right = materialize(&mut eg, &projections.1);
    eg.rebuild();
    assert_eq!(eg.find_const(projected_left), eg.find_const(left));
    assert_eq!(eg.find_const(projected_right), eg.find_const(right));
}

/// Build the minimal cost-sensitive transportation counterexample. The only
/// semantic difference between the two variants is the insertion order of c,d.
///
/// Margins are [2,1] on both sides in the bad order. The two vertices are:
///   [[2,0],[0,1]] with AU size 13, and
///   [[1,1],[1,0]] with AU size 11.
fn transportation_case(reverse_right_creation: bool) -> (u32, usize) {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let x_op = eg.register_op0("x", sort);
    let y_op = eg.register_op0("y", sort);
    let f = eg.register_op1("f", sort, sort);
    let g = eg.register_op1("g", sort, sort);
    let plus = eg.register_mset("plus", sort, sort);

    let x = eg.add(x_op, &[]);
    let y = eg.add(y_op, &[]);
    let a = eg.add(f, &[x]);
    let b = eg.add(g, &[x]);
    let (c, d) = if reverse_right_creation {
        let d = eg.add(f, &[y]);
        let c = eg.add(g, &[y]);
        (c, d)
    } else {
        let c = eg.add(g, &[y]);
        let d = eg.add(f, &[y]);
        (c, d)
    };

    let left = eg.add(plus, &[a, a, b]);
    let right = eg.add(plus, &[c, c, d]);
    eg.rebuild();

    let snapshot = AuSnapshot::new(&eg).unwrap();
    let left_class = snapshot.class_of(left).unwrap();
    let right_class = snapshot.class_of(right).unwrap();
    let mut cache = ActionCache::new(usize::MAX);
    generate_actions(&snapshot, &mut cache, left_class, right_class);
    let actions = cache.get(left_class, right_class).unwrap().len();
    let result = anti_unify(
        &snapshot,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
    )
    .unwrap();
    (result.size, actions)
}

#[test]

fn exact_ac_vertex_oracle_finds_the_cross_matching() {
    let (size, actions) = transportation_case(false);
    assert_eq!(
        (actions, size),
        (2, 11),
        "both 2x2 transportation vertices are required and the cross vertex is optimal"
    );
}

#[test]

fn exact_ac_is_invariant_to_insertion_order() {
    let normal = transportation_case(false);
    let reversed = transportation_case(true);
    assert_eq!(normal.0, 11);
    assert_eq!(reversed.0, 11);
    assert_eq!(normal.0, reversed.0);
}

fn singleton_identity_case(idempotent: bool) -> ((u32, u32), usize) {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let unit_op = eg.register_op0("unit", sort);
    let a_op = eg.register_op0("a", sort);
    let x_op = eg.register_op0("x", sort);
    let f = eg.register_op1("f", sort, sort);
    let op = if idempotent {
        eg.register_set("combine", sort, sort)
    } else {
        eg.register_mset("combine", sort, sort)
    };

    let unit = eg.add(unit_op, &[]);
    eg.set_unit_node(op, unit);
    let a = eg.add(a_op, &[]);
    let x = eg.add(x_op, &[]);
    let fx = eg.add(f, &[x]);
    let left = eg.add(op, &[a, fx]);
    // Canonical AC/ACI representation collapses this to `fx`, so the shorter
    // class has no `combine` member for the current action scanner to pair.
    let right = eg.add(op, &[fx]);
    assert_eq!(right, fx);
    eg.rebuild();

    let snapshot = AuSnapshot::new(&eg).unwrap();
    let left_class = snapshot.class_of(left).unwrap();
    let right_class = snapshot.class_of(right).unwrap();
    let mut cache = ActionCache::new(usize::MAX);
    generate_actions(&snapshot, &mut cache, left_class, right_class);
    let actions = cache.get(left_class, right_class).unwrap().len();
    let result = anti_unify(
        &snapshot,
        left,
        right,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
    )
    .unwrap();
    (result.pool.quality(result.term_id), actions)
}

#[test]

fn ac_identity_padding_handles_canonical_singleton() {
    let (quality, actions) = singleton_identity_case(false);
    assert_eq!(
        (actions, quality),
        (2, (5, 2)),
        "two padded pairings should expose combine(f(x), Variants(a, unit))"
    );
}

#[test]

fn aci_identity_padding_handles_canonical_singleton() {
    let (quality, actions) = singleton_identity_case(true);
    assert_eq!(
        (actions, quality),
        (2, (5, 2)),
        "two padded pairings should expose combine(f(x), Variants(a, unit))"
    );
}

fn duplicate_member_actions(cap: usize) -> (usize, usize) {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let set = eg.register_set("set", sort, sort);
    let leaf_ops: Vec<_> = (0..8)
        .map(|i| eg.register_op0(&format!("k{i}"), sort))
        .collect();
    let leaves: Vec<_> = leaf_ops.iter().map(|&op| eg.add(op, &[])).collect();

    let left_1 = eg.add(set, &[leaves[0], leaves[1]]);
    let left_2 = eg.add(set, &[leaves[2], leaves[3]]);
    let right_1 = eg.add(set, &[leaves[4], leaves[5]]);
    let right_2 = eg.add(set, &[leaves[6], leaves[7]]);

    // Model rewrite-derived equivalent children. The two historical set nodes
    // remain distinct members but now generate identical actions.
    eg.merge(leaves[0], leaves[2]);
    eg.merge(leaves[1], leaves[3]);
    eg.merge(leaves[4], leaves[6]);
    eg.merge(leaves[5], leaves[7]);
    eg.rebuild();
    assert_eq!(eg.find_const(left_1), eg.find_const(left_2));
    assert_eq!(eg.find_const(right_1), eg.find_const(right_2));

    let snapshot = AuSnapshot::new(&eg).unwrap();
    let left = snapshot.class_of(left_1).unwrap();
    let right = snapshot.class_of(right_1).unwrap();
    let mut cache = ActionCache::new(cap);
    generate_actions(&snapshot, &mut cache, left, right);
    let actions = cache.get(left, right).unwrap();
    let unique: HashSet<Vec<_>> = actions
        .iter()
        .map(|action| {
            let mut signature: Vec<_> = action
                .pairs
                .iter()
                .map(|pair| (pair.left.to_usize(), pair.right.to_usize(), pair.count))
                .collect();
            signature.sort_unstable();
            signature
        })
        .collect();
    (actions.len(), unique.len())
}

#[test]

fn action_cap_is_global_and_actions_are_deduplicated_per_class_pair() {
    let (actions, unique) = duplicate_member_actions(1);
    assert_eq!(unique, 1);
    assert_eq!(
        actions, unique,
        "duplicate rewrite-derived actions must be coalesced"
    );
    assert!(actions <= 1, "A_max should bound the class-pair action set");
}

#[test]

fn best_results_restore_recovers_pre_mark_entry() {
    let mut pool = TermPool::<OpId, LitValId>::new();
    let before = pool.intern(TermOp::EGraph(OpId::from_usize(0)), &[]);
    let mut results: BestResults = BestResults::new();
    let root = OrId::from_usize(0);
    assert!(results.offer(root, before, (10, 10)));

    let pool_token = pool.mark();
    let results_token = results.mark();
    let after = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
    assert!(results.offer(root, after, (5, 5)));

    results.restore(results_token);
    pool.restore(pool_token);
    assert_eq!(results.best_term(root), Some(before));
    assert_eq!(results.best_quality(root), (10, 10));
}

#[test]

fn best_results_restore_can_leave_a_dangling_term_id() {
    let mut pool = TermPool::<OpId, LitValId>::new();
    let before = pool.intern(TermOp::EGraph(OpId::from_usize(0)), &[]);
    let mut results: BestResults = BestResults::new();
    let root = OrId::from_usize(0);
    results.offer(root, before, (10, 10));

    let pool_token = pool.mark();
    let results_token = results.mark();
    let after = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
    results.offer(root, after, (5, 5));

    // This is SearchSession's restore order: results first, then terms.
    results.restore(results_token);
    pool.restore(pool_token);
    // After the fix: the entry reverts to the pre-mark term (not a dangling id).
    let restored = results.best_term(root).expect("entry should exist");
    assert_eq!(restored, before, "restore should revert to pre-mark term");
    assert_eq!(results.best_quality(root), (10, 10));
    // The pre-mark term is still valid in the restored pool.
    assert_eq!(pool.size(restored), 1);
}

#[test]
fn projections_materialize_into_source_classes_for_all_operator_families() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let leaf_ops: Vec<_> = (0..8)
        .map(|i| eg.register_op0(&format!("v{i}"), sort))
        .collect();
    let leaves: Vec<_> = leaf_ops.iter().map(|&op| eg.add(op, &[])).collect();

    let normal = eg.register_op2("normal", sort, sort, sort);
    let comm = eg.register_c("comm", [sort, sort], sort);
    let assoc_l = eg.register_a("assoc_l", sort, sort, AssocDir::Left);
    let assoc_r = eg.register_a("assoc_r", sort, sort, AssocDir::Right);
    let assoc_b = eg.register_a("assoc_b", sort, sort, AssocDir::Both);
    let ac = eg.register_mset("ac", sort, sort);
    let aci = eg.register_set("aci", sort, sort);
    let lit = eg.register_lit("lit", sort);

    let unit_op = eg.register_op0("unit", sort);
    let unit = eg.add(unit_op, &[]);
    let ac_unit = eg.register_mset("ac_unit", sort, sort);
    eg.set_unit_node(ac_unit, unit);

    let xor = eg.register_kind(
        "xor",
        sort,
        OpKind::MSet {
            arg_sort: sort,
            clamp: Clamp::Nilpotent { order: 2 },
            identity: None,
            cancellative: false,
        },
    );
    eg.set_unit_node(xor, unit);

    let inverse = eg.register_op1("inverse", sort, sort);
    let group = eg.register_kind(
        "group",
        sort,
        OpKind::MSet {
            arg_sort: sort,
            clamp: Clamp::None,
            identity: None,
            cancellative: true,
        },
    );
    eg.set_unit_node(group, unit);
    eg.set_inverse_op(group, inverse);
    let inv_1 = eg.add(inverse, &[leaves[1]]);
    let inv_2 = eg.add(inverse, &[leaves[2]]);

    let lit_1 = eg.intern_lit(NiraLitVal::Int(1.into()));
    let lit_2 = eg.intern_lit(NiraLitVal::Int(2.into()));
    let literal_1 = eg.add_lit(lit, lit_1);
    let literal_2 = eg.add_lit(lit, lit_2);

    let pairs = vec![
        (
            eg.add(normal, &[leaves[0], leaves[1]]),
            eg.add(normal, &[leaves[0], leaves[2]]),
        ),
        (
            eg.add(comm, &[leaves[0], leaves[1]]),
            eg.add(comm, &[leaves[0], leaves[2]]),
        ),
        (
            eg.add(assoc_l, &[leaves[0], leaves[1], leaves[3]]),
            eg.add(assoc_l, &[leaves[0], leaves[2], leaves[3]]),
        ),
        (
            eg.add(assoc_r, &[leaves[0], leaves[1], leaves[3]]),
            eg.add(assoc_r, &[leaves[0], leaves[2], leaves[3]]),
        ),
        (
            eg.add(assoc_b, &[leaves[0], leaves[1], leaves[3]]),
            eg.add(assoc_b, &[leaves[0], leaves[2], leaves[3]]),
        ),
        (
            eg.add(ac, &[leaves[0], leaves[1]]),
            eg.add(ac, &[leaves[0], leaves[2]]),
        ),
        (
            eg.add(aci, &[leaves[0], leaves[1], leaves[3]]),
            eg.add(aci, &[leaves[0], leaves[2], leaves[3]]),
        ),
        (
            eg.add(ac_unit, &[leaves[0], leaves[1], leaves[3]]),
            eg.add(ac_unit, &[leaves[0], leaves[2]]),
        ),
        (
            eg.add(xor, &[leaves[0], leaves[1]]),
            eg.add(xor, &[leaves[0], leaves[2]]),
        ),
        (
            eg.add(group, &[leaves[0], inv_1]),
            eg.add(group, &[leaves[0], inv_2]),
        ),
        (literal_1, literal_2),
    ];
    eg.rebuild();

    for (left, right) in pairs {
        assert_projection_membership(&mut eg, left, right);
    }
}

#[test]
fn cycles_with_finite_members_project_soundly_under_both_cycle_modes() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let f = eg.register_op1("f", sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let fa = eg.add(f, &[a]);
    let fb = eg.add(f, &[b]);
    eg.merge(a, fa);
    eg.merge(b, fb);
    eg.rebuild();

    for cycle_mode in [CycleMode::AncestorOnly, CycleMode::CurrentInclusive] {
        let projections = {
            let snapshot = AuSnapshot::new(&eg).unwrap();
            let result = anti_unify(
                &snapshot,
                a,
                b,
                &AuConfig {
                    algorithm: AuAlgorithm::Exact,
                    cycle_mode,
                    ..Default::default()
                },
            )
            .unwrap();
            projected_terms(result)
        };
        let left = materialize(&mut eg, &projections.0);
        let right = materialize(&mut eg, &projections.1);
        eg.rebuild();
        assert_eq!(eg.find_const(left), eg.find_const(a));
        assert_eq!(eg.find_const(right), eg.find_const(b));
    }
}

#[test]
fn all_algorithms_reject_a_reachable_class_without_a_finite_member() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let f = eg.register_op1("f", sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let fa = eg.add(f, &[a]);
    eg.merge(a, fa);
    eg.rebuild();
    eg.subsume(a);

    let snapshot = AuSnapshot::new(&eg).unwrap();
    for algorithm in [AuAlgorithm::Exact, AuAlgorithm::Uct] {
        let error = anti_unify(
            &snapshot,
            a,
            b,
            &AuConfig {
                algorithm,
                playouts: 16,
                ..Default::default()
            },
        )
        .expect_err("search should reject the all-recursive class");
        assert!(matches!(
            error,
            semi_persistent_egraph::au::AuError::NoFiniteRepresentative(_)
        ));
    }
}
