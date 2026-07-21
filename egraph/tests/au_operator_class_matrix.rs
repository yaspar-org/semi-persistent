// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Systematic operator-class matrix for anti-unification.
//!
//! One test per (operator class × structural relation) cell. Every case runs
//! BOTH algorithms — the exact DP solver and UCT with enough playouts to
//! structurally certify on these small fixtures — and asserts:
//!
//! 1. the exact `(size, variant_mass)` quality, computed by hand in a comment
//!    next to each assertion;
//! 2. UCT certified equality (`Completion::Exact`) with the same quality; and
//! 3. projection validity: both projections of the anti-unifier materialize
//!    back into their source e-classes (the helper pattern from
//!    `au_adversarial_correctness.rs`).
//!
//! Quality arithmetic reminder (see `au/terms.rs`): a concrete node costs
//! `1 + Σ children`; a `Variants` node is free itself but both arms count
//! (`size = Σ children`) and its whole subtree is variant mass
//! (`vmass = Σ child sizes`). For concrete nodes `vmass = Σ child vmasses`.
//!
//! Identity elements are declared with `eg.set_unit_node(op, unit_node)`
//! (`registry`/`egraph.rs`); the AU action generator reads them back through
//! `snap.op_identity_class(op)` (`au/actions.rs`).

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::actions::{ActionCache, generate_actions};
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{
    AuAlgorithm, AuConfig, AuResult, Completion, anti_unify,
};
use semi_persistent_egraph::au::terms::{TermId, TermOp, TermPool};
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::nodes::LitValId;
use semi_persistent_egraph::registry::AssocDir;

type Eg = EGraph31<NiraLitVal, false, false>;

/// Playout budget for UCT on these fixtures. All fixtures here are tiny
/// (single-digit class counts), so the children-first closure pass certifies
/// long before this budget expires.
const CERTIFY_PLAYOUTS: u64 = 512;

// ─── Projection helpers (pattern from au_adversarial_correctness.rs) ───

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

/// The matrix driver: run BOTH algorithms, assert the hand-computed quality,
/// certified completion, and projection membership in the source classes.
fn check_case(eg: &mut Eg, left: ENodeId, right: ENodeId, expected: (u32, u32), label: &str) {
    for algorithm in [AuAlgorithm::Exact, AuAlgorithm::Uct] {
        let (quality, completion, projections) = {
            let snapshot = AuSnapshot::new(eg).unwrap();
            let result = anti_unify(
                &snapshot,
                left,
                right,
                &AuConfig {
                    algorithm,
                    playouts: CERTIFY_PLAYOUTS,
                    ..Default::default()
                },
            )
            .unwrap();
            (
                result.pool.quality(result.term_id),
                result.completion,
                projected_terms(result),
            )
        };

        assert_eq!(
            quality, expected,
            "{label}: {algorithm:?} quality mismatch (expected {expected:?}, got {quality:?})"
        );
        assert_eq!(
            completion,
            Completion::Exact,
            "{label}: {algorithm:?} did not certify on a small fixture"
        );

        let projected_left = materialize(eg, &projections.0);
        let projected_right = materialize(eg, &projections.1);
        eg.rebuild();
        assert_eq!(
            eg.find_const(projected_left),
            eg.find_const(left),
            "{label}: {algorithm:?} left projection did not land in its source e-class"
        );
        assert_eq!(
            eg.find_const(projected_right),
            eg.find_const(right),
            "{label}: {algorithm:?} right projection did not land in its source e-class"
        );
    }
}

/// Count the deduplicated non-AC/matrix actions the generator materializes for
/// a class pair (matrix-enumeration cache, as in au_adversarial_correctness.rs).
fn count_actions(eg: &Eg, left: ENodeId, right: ENodeId) -> usize {
    let snapshot = AuSnapshot::new(eg).unwrap();
    let l = snapshot.class_of(left).unwrap();
    let r = snapshot.class_of(right).unwrap();
    let mut cache = ActionCache::new(usize::MAX);
    generate_actions(&snapshot, &mut cache, l, r);
    cache.get(l, r).unwrap().len()
}

// ═══════════════════════════════ Plain0 ═══════════════════════════════

/// Same nullary op: identical e-class, AU is the leaf itself.
/// size = 1 (a), vmass = 0 → (1, 0).
#[test]
fn plain0_same_op() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let a1 = eg.add(a_op, &[]);
    let a2 = eg.add(a_op, &[]);
    eg.rebuild();
    check_case(&mut eg, a1, a2, (1, 0), "plain0 same op");
}

/// Different nullary ops: only the generalize action exists.
/// Variants(a, b): size = 1 + 1 = 2, vmass = 2 → (2, 2).
#[test]
fn plain0_different_ops() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    eg.rebuild();
    check_case(&mut eg, a, b, (2, 2), "plain0 different ops");
}

// ═══════════════════════════ Plain1/2/3/N ═════════════════════════════

/// Plain1, same op: f(a) vs f(b) factors through f.
/// f(Variants(a,b)): size = 1 + (1+1) = 3, vmass = 2 → (3, 2).
#[test]
fn plain1_same_op() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let f = eg.register_op1("f", sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let fa = eg.add(f, &[a]);
    let fb = eg.add(f, &[b]);
    eg.rebuild();
    check_case(&mut eg, fa, fb, (3, 2), "plain1 same op");
}

/// Plain2, same op: g(a,x) vs g(b,x) — positional zip pairs (a,b) and (x,x).
/// g(Variants(a,b), x): size = 1 + 2 + 1 = 4, vmass = 2 → (4, 2).
#[test]
fn plain2_same_op() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let g = eg.register_op2("g", sort, sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let left = eg.add(g, &[a, x]);
    let right = eg.add(g, &[b, x]);
    eg.rebuild();
    check_case(&mut eg, left, right, (4, 2), "plain2 same op");
}

/// Plain3, same op: g3(a,x,y) vs g3(b,x,y).
/// g3(Variants(a,b), x, y): size = 1 + 2 + 1 + 1 = 5, vmass = 2 → (5, 2).
#[test]
fn plain3_same_op() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let y_op = eg.register_op0("y", sort);
    let g3 = eg.register_op3("g3", sort, sort, sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let y = eg.add(y_op, &[]);
    let left = eg.add(g3, &[a, x, y]);
    let right = eg.add(g3, &[b, x, y]);
    eg.rebuild();
    check_case(&mut eg, left, right, (5, 2), "plain3 same op");
}

/// PlainN (arity 5), same op, same arity.
/// g5(Variants(a,b), x, y, z, w): size = 1 + 2 + 4 = 7, vmass = 2 → (7, 2).
#[test]
fn plainn_same_op_same_arity() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let leaf_ops: Vec<_> = ["a", "b", "x", "y", "z", "w"]
        .iter()
        .map(|n| eg.register_op0(n, sort))
        .collect();
    let leaves: Vec<_> = leaf_ops.iter().map(|&op| eg.add(op, &[])).collect();
    let g5 = eg.register_opn("g5", &[sort; 5], sort);
    let left = eg.add(g5, &[leaves[0], leaves[2], leaves[3], leaves[4], leaves[5]]);
    let right = eg.add(g5, &[leaves[1], leaves[2], leaves[3], leaves[4], leaves[5]]);
    eg.rebuild();
    check_case(&mut eg, left, right, (7, 2), "plainN same op same arity");
}

/// PlainN, same NAME but different arity. A plain (Normal) operator has a
/// fixed arity: the registry rejects re-registering a name (`insert` asserts
/// uniqueness) and `EGraph::add` debug-asserts the child count, so a single
/// OpId with two arities is unrepresentable through the public API. The
/// nearest representable cell is two distinct ops of the same name shape and
/// different arity — which yields no shared-op action, so only generalize:
/// Variants(p3(a,x,y), p4(a,x,y,z)): size = 4 + 5 = 9, vmass = 9 → (9, 9).
#[test]
fn plainn_same_name_different_arity_is_generalize() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let x_op = eg.register_op0("x", sort);
    let y_op = eg.register_op0("y", sort);
    let z_op = eg.register_op0("z", sort);
    let p3 = eg.register_opn("p_arity3", &[sort; 3], sort);
    let p4 = eg.register_opn("p_arity4", &[sort; 4], sort);
    let a = eg.add(a_op, &[]);
    let x = eg.add(x_op, &[]);
    let y = eg.add(y_op, &[]);
    let z = eg.add(z_op, &[]);
    let left = eg.add(p3, &[a, x, y]);
    let right = eg.add(p4, &[a, x, y, z]);
    eg.rebuild();
    // No structural action at all across different ops.
    assert_eq!(count_actions(&eg, left, right), 0);
    check_case(
        &mut eg,
        left,
        right,
        (9, 9),
        "plainN same name different arity",
    );
}

/// Different plain ops of the same arity: children coincide but the operator
/// differs, so there is no structural action.
/// Variants(f(a), g(a)): size = 2 + 2 = 4, vmass = 4 → (4, 4).
#[test]
fn plain_different_ops_same_arity() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let f = eg.register_op1("f", sort, sort);
    let g = eg.register_op1("g", sort, sort);
    let a = eg.add(a_op, &[]);
    let fa = eg.add(f, &[a]);
    let ga = eg.add(g, &[a]);
    eg.rebuild();
    assert_eq!(count_actions(&eg, fa, ga), 0);
    check_case(&mut eg, fa, ga, (4, 4), "plain different ops");
}

// ═══════════════════════════════ Seq (A) ══════════════════════════════

/// Associative sequences of equal length: one positional zip action.
/// s(Variants(a,b), x): size = 1 + 2 + 1 = 4, vmass = 2 → (4, 2).
#[test]
fn seq_equal_length_zip() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let s = eg.register_a("s", sort, sort, AssocDir::Both);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let left = eg.add(s, &[a, x]);
    let right = eg.add(s, &[b, x]);
    eg.rebuild();
    assert_eq!(count_actions(&eg, left, right), 1);
    check_case(&mut eg, left, right, (4, 2), "seq equal length");
}

/// Associative sequences of unequal length: no structural action at all
/// (the zip requires equal lengths, and A ops have no identity padding),
/// so the exact optimum is the generalize action.
/// Variants(s(a,x), s(b,x,y)): size = 3 + 4 = 7, vmass = 7 → (7, 7).
#[test]
fn seq_unequal_length_generalizes() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let y_op = eg.register_op0("y", sort);
    let s = eg.register_a("s", sort, sort, AssocDir::Both);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let y = eg.add(y_op, &[]);
    let left = eg.add(s, &[a, x]);
    let right = eg.add(s, &[b, x, y]);
    eg.rebuild();
    // No structural action: unequal lengths cannot zip.
    assert_eq!(count_actions(&eg, left, right), 0);
    check_case(&mut eg, left, right, (7, 7), "seq unequal length");
}

// ═══════════════════════════ SPair (C) ════════════════════════════════

/// Commutative pair where the aligned orientation is optimal. Both
/// orientations are generated (2 actions); the optimum pairs x with x.
/// c(Variants(a,b), x): size = 1 + 2 + 1 = 4, vmass = 2 → (4, 2).
#[test]
fn spair_aligned_orientation() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let c = eg.register_c("c", [sort, sort], sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let left = eg.add(c, &[a, x]);
    let right = eg.add(c, &[b, x]);
    eg.rebuild();
    assert_eq!(count_actions(&eg, left, right), 2);
    check_case(&mut eg, left, right, (4, 2), "spair aligned");
}

/// Commutative pair where the optimum needs the crossed orientation
/// relative to canonical child order (whichever way the children sort, only
/// one of the two orientations pairs the two f-terms).
/// Pairings: {f(p)↔f(s), q↔r} → c(f(Variants(p,s)), Variants(q,r)):
///   size = 1 + (1+2) + 2 = 6, vmass = 2 + 2 = 4 → (6, 4).
/// The other orientation {f(p)↔r, q↔f(s)} costs 1 + 3 + 3 = 7. → (6, 4) wins.
#[test]
fn spair_crossed_orientation() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let p_op = eg.register_op0("p", sort);
    let q_op = eg.register_op0("q", sort);
    let r_op = eg.register_op0("r", sort);
    let s_op = eg.register_op0("sx", sort);
    let f = eg.register_op1("f", sort, sort);
    let c = eg.register_c("c", [sort, sort], sort);
    let p = eg.add(p_op, &[]);
    let q = eg.add(q_op, &[]);
    let r = eg.add(r_op, &[]);
    let s = eg.add(s_op, &[]);
    let fp = eg.add(f, &[p]);
    let fs = eg.add(f, &[s]);
    let left = eg.add(c, &[fp, q]);
    let right = eg.add(c, &[r, fs]);
    eg.rebuild();
    // Both orientations must be generated: neither side has equal children.
    assert_eq!(count_actions(&eg, left, right), 2);
    check_case(&mut eg, left, right, (6, 4), "spair crossed");
}

/// Symmetric-orientation dedup: when one member's children are equal, the
/// crossed orientation is identical to the positional one and must be skipped
/// (exactly 1 action). c(a,a) vs c(b,x):
/// c(Variants(a,b), Variants(a,x)): size = 1 + 2 + 2 = 5, vmass = 4 → (5, 4).
#[test]
fn spair_symmetric_orientation_dedup_left() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let c = eg.register_c("c", [sort, sort], sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let left = eg.add(c, &[a, a]);
    let right = eg.add(c, &[b, x]);
    eg.rebuild();
    assert_eq!(
        count_actions(&eg, left, right),
        1,
        "equal left children must suppress the crossed orientation"
    );
    check_case(&mut eg, left, right, (5, 4), "spair dedup left");
}

/// Same dedup with the equal children on the right side.
/// c(b,x) vs c(a,a) → c(Variants(b,a), Variants(x,a)): (5, 4), 1 action.
#[test]
fn spair_symmetric_orientation_dedup_right() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let c = eg.register_c("c", [sort, sort], sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let left = eg.add(c, &[b, x]);
    let right = eg.add(c, &[a, a]);
    eg.rebuild();
    assert_eq!(
        count_actions(&eg, left, right),
        1,
        "equal right children must suppress the crossed orientation"
    );
    check_case(&mut eg, left, right, (5, 4), "spair dedup right");
}

// ═══════════════════════════ MSet (AC) ════════════════════════════════

/// AC multisets with equal totals: transport matches x↔x and a↔b.
/// m(Variants(a,b), x): size = 1 + 2 + 1 = 4, vmass = 2 → (4, 2).
#[test]
fn mset_equal_totals() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let m = eg.register_mset("m", sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let left = eg.add(m, &[a, x]);
    let right = eg.add(m, &[b, x]);
    eg.rebuild();
    check_case(&mut eg, left, right, (4, 2), "mset equal totals");
}

/// AC multisets with unequal totals and a DECLARED identity: the shorter side
/// is padded with the neutral element; the padded optimum matches x↔x, a↔b,
/// e↔y. m(x, Variants(a,b), Variants(e,y)):
///   size = 1 + 1 + 2 + 2 = 6, vmass = 2 + 2 = 4 → (6, 4).
/// (Any matching has one identical pair and two Variants pairs at best; a
/// mismatch on x costs 7.) The unpadded generalize would be 3 + 4 = (7, 7).
#[test]
fn mset_unequal_totals_with_identity() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let e_op = eg.register_op0("e", sort);
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let y_op = eg.register_op0("y", sort);
    let m = eg.register_mset("m", sort, sort);
    let e = eg.add(e_op, &[]);
    eg.set_unit_node(m, e);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let y = eg.add(y_op, &[]);
    let left = eg.add(m, &[a, x]);
    let right = eg.add(m, &[b, x, y]);
    eg.rebuild();
    check_case(&mut eg, left, right, (6, 4), "mset identity pad left");
    // And with the longer monomial on the left (padding the right side).
    check_case(&mut eg, right, left, (6, 4), "mset identity pad right");
}

/// AC multisets with unequal totals and NO identity: no padded representation
/// exists, so the optimum is the generalize action.
/// Variants(m(a,x), m(b,x,y)): size = 3 + 4 = 7, vmass = 7 → (7, 7).
#[test]
fn mset_unequal_totals_without_identity() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let y_op = eg.register_op0("y", sort);
    let m = eg.register_mset("m", sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let y = eg.add(y_op, &[]);
    let left = eg.add(m, &[a, x]);
    let right = eg.add(m, &[b, x, y]);
    eg.rebuild();
    check_case(&mut eg, left, right, (7, 7), "mset no identity");
}

/// Singleton-canonized class vs an AC member (identity expansion). The
/// canonical AC representation collapses `combine(fx)` to `fx`, so the right
/// class has NO combine member; with a declared identity, the action
/// generator expands the singleton as {fx, e^(n-1)} (actions.rs, the
/// left-has-op identity-expansion block). Optimum pairs fx↔fx and a↔e:
/// combine(f(x), Variants(a, e)): size = 1 + 2 + 2 = 5, vmass = 2 → (5, 2).
#[test]
fn mset_singleton_canonized_identity_expansion_left_op() {
    let (mut eg, left, right) = singleton_fixture(false);
    // Two padded pairings for the (combine-member, virtual-singleton) pair.
    assert_eq!(count_actions(&eg, left, right), 2);
    check_case(&mut eg, left, right, (5, 2), "mset singleton left-op");
}

/// Mirror orientation: the op member is on the RIGHT and the singleton on the
/// left — this drives the symmetric right-has-op identity-expansion block in
/// actions.rs (the MSet arm of the `// Symmetric: right has the op` section).
#[test]
fn mset_singleton_canonized_identity_expansion_right_op() {
    let (mut eg, left, right) = singleton_fixture(false);
    assert_eq!(count_actions(&eg, right, left), 2);
    check_case(&mut eg, right, left, (5, 2), "mset singleton right-op");
}

/// Builds the canonical-singleton fixture from au_adversarial_correctness.rs:
/// left = combine{a, f(x)}, right = combine{f(x)} which canonizes to f(x).
/// `idempotent` selects Set (ACI) vs MSet (AC).
fn singleton_fixture(idempotent: bool) -> (Eg, ENodeId, ENodeId) {
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
    let right = eg.add(op, &[fx]);
    // Canonical AC/ACI representation collapses the singleton application.
    assert_eq!(right, fx);
    eg.rebuild();
    (eg, left, right)
}

/// Repeated children with multiplicity > 1: m{a,a,x} vs m{b,b,x}.
/// Margins are {a:2, x:1} vs {b:2, x:1}; the diagonal vertex a↔b (×2), x↔x
/// gives m(Variants(a,b), Variants(a,b), x):
///   size = 1 + 2·2 + 1 = 6, vmass = 2·2 = 4 → (6, 4).
/// The cross vertex {a↔b ×1, a↔x ×1, x↔b ×1} costs 1 + 2 + 2 + 2 = 7.
#[test]
fn mset_repeated_children_multiplicities() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let m = eg.register_mset("m", sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let left = eg.add(m, &[a, a, x]);
    let right = eg.add(m, &[b, b, x]);
    eg.rebuild();
    check_case(&mut eg, left, right, (6, 4), "mset multiplicities");
}

// ═══════════════════════════ Set (ACI) ════════════════════════════════

/// ACI sets of equal cardinality: bijection matches x↔x and a↔b.
/// s(Variants(a,b), x): size = 1 + 2 + 1 = 4, vmass = 2 → (4, 2).
#[test]
fn set_equal_cardinality_bijection() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let s = eg.register_set("s", sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let left = eg.add(s, &[a, x]);
    let right = eg.add(s, &[b, x]);
    eg.rebuild();
    check_case(&mut eg, left, right, (4, 2), "set equal cardinality");
}

/// ACI sets of unequal cardinality with a declared identity, both padding
/// directions. Optimum matches x↔x, a↔b, e↔y:
/// s(x, Variants(a,b), Variants(e,y)): size = 1+1+2+2 = 6, vmass = 4 → (6, 4).
#[test]
fn set_unequal_cardinality_with_identity_both_directions() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let e_op = eg.register_op0("e", sort);
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let y_op = eg.register_op0("y", sort);
    let s = eg.register_set("s", sort, sort);
    let e = eg.add(e_op, &[]);
    eg.set_unit_node(s, e);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let y = eg.add(y_op, &[]);
    let left = eg.add(s, &[a, x]);
    let right = eg.add(s, &[b, x, y]);
    eg.rebuild();
    check_case(&mut eg, left, right, (6, 4), "set identity pad left");
    check_case(&mut eg, right, left, (6, 4), "set identity pad right");
}

/// ACI sets of unequal cardinality WITHOUT identity: generalize only.
/// Variants(s(a,x), s(b,x,y)): size = 3 + 4 = 7, vmass = 7 → (7, 7).
#[test]
fn set_unequal_cardinality_without_identity() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let x_op = eg.register_op0("x", sort);
    let y_op = eg.register_op0("y", sort);
    let s = eg.register_set("s", sort, sort);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let x = eg.add(x_op, &[]);
    let y = eg.add(y_op, &[]);
    let left = eg.add(s, &[a, x]);
    let right = eg.add(s, &[b, x, y]);
    eg.rebuild();
    check_case(&mut eg, left, right, (7, 7), "set no identity");
}

/// ACI singleton-canonized class vs a Set member (identity expansion,
/// op member on the left). Same arithmetic as the MSet case:
/// combine(f(x), Variants(a, unit)): (5, 2), 2 padded actions.
#[test]
fn set_singleton_canonized_identity_expansion_left_op() {
    let (mut eg, left, right) = singleton_fixture(true);
    assert_eq!(count_actions(&eg, left, right), 2);
    check_case(&mut eg, left, right, (5, 2), "set singleton left-op");
}

/// Mirror orientation for ACI: op member on the RIGHT, singleton on the left
/// (the Set arm of the symmetric right-has-op block in actions.rs).
#[test]
fn set_singleton_canonized_identity_expansion_right_op() {
    let (mut eg, left, right) = singleton_fixture(true);
    assert_eq!(count_actions(&eg, right, left), 2);
    check_case(&mut eg, right, left, (5, 2), "set singleton right-op");
}

// ═══════════════════════════════ Lit ══════════════════════════════════

/// Equal literal values are hash-consed into one class: AU is the literal.
/// size = 1, vmass = 0 → (1, 0).
#[test]
fn lit_equal_value_identical_class() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let lit = eg.register_lit("lit", sort);
    let v5 = eg.intern_lit(NiraLitVal::Int(5.into()));
    let l1 = eg.add_lit(lit, v5);
    let l2 = eg.add_lit(lit, v5);
    eg.rebuild();
    check_case(&mut eg, l1, l2, (1, 0), "lit equal value");
}

/// Equal literal values factor into the shared backbone under an operator.
/// h(5, Variants(x,y)): size = 1 + 1 + 2 = 4, vmass = 2 → (4, 2).
#[test]
fn lit_equal_value_factoring_under_op() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let x_op = eg.register_op0("x", sort);
    let y_op = eg.register_op0("y", sort);
    let h = eg.register_op2("h", sort, sort, sort);
    let lit = eg.register_lit("lit", sort);
    let v5 = eg.intern_lit(NiraLitVal::Int(5.into()));
    let l5 = eg.add_lit(lit, v5);
    let x = eg.add(x_op, &[]);
    let y = eg.add(y_op, &[]);
    let left = eg.add(h, &[l5, x]);
    let right = eg.add(h, &[l5, y]);
    eg.rebuild();
    check_case(&mut eg, left, right, (4, 2), "lit factoring");
}

/// Unequal literal values: distinct classes, no shared structural action
/// (a literal member has no children to zip), so generalize.
/// Variants(5, 7): size = 1 + 1 = 2, vmass = 2 → (2, 2).
#[test]
fn lit_unequal_values() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let lit = eg.register_lit("lit", sort);
    let v5 = eg.intern_lit(NiraLitVal::Int(5.into()));
    let v7 = eg.intern_lit(NiraLitVal::Int(7.into()));
    let l5 = eg.add_lit(lit, v5);
    let l7 = eg.add_lit(lit, v7);
    eg.rebuild();
    check_case(&mut eg, l5, l7, (2, 2), "lit unequal values");
}

/// Literal vs a non-literal member: no shared op, generalize only.
/// Variants(5, f(a)): size = 1 + 2 = 3, vmass = 3 → (3, 3).
#[test]
fn lit_vs_non_literal_member() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let f = eg.register_op1("f", sort, sort);
    let lit = eg.register_lit("lit", sort);
    let v5 = eg.intern_lit(NiraLitVal::Int(5.into()));
    let l5 = eg.add_lit(lit, v5);
    let a = eg.add(a_op, &[]);
    let fa = eg.add(f, &[a]);
    eg.rebuild();
    check_case(&mut eg, l5, fa, (3, 3), "lit vs non-literal");
}

/// A class holding BOTH a literal and a non-literal member, against a plain
/// literal: the generalize action uses the smallest member (the literal), so
/// Variants(5, 7): size = 2, vmass = 2 → (2, 2).
#[test]
fn lit_class_with_mixed_members() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let a_op = eg.register_op0("a", sort);
    let g = eg.register_op1("g", sort, sort);
    let lit = eg.register_lit("lit", sort);
    let v5 = eg.intern_lit(NiraLitVal::Int(5.into()));
    let v7 = eg.intern_lit(NiraLitVal::Int(7.into()));
    let l5 = eg.add_lit(lit, v5);
    let l7 = eg.add_lit(lit, v7);
    let a = eg.add(a_op, &[]);
    let ga = eg.add(g, &[a]);
    eg.merge(l7, ga); // right class = {7, g(a)}
    eg.rebuild();
    check_case(&mut eg, l5, l7, (2, 2), "lit mixed-member class");
}
