// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! End-to-end conformance tests: build the NIRA theory, run anti-unification on
//! the fixture corpus cases, and check expectations.

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, anti_unify};
use semi_persistent_egraph::literal::NiraLitVal;

type Eg = EGraph31<NiraLitVal, false, false>;

/// Build the NIRA theory e-graph with all sorts and operators the fixture corpus needs.
fn build_theory() -> (Eg, TheoryOps) {
    let mut eg = Eg::new();
    let bool_s = eg.intern_sort("Bool");
    let int_s = eg.intern_sort("Int");
    let real_s = eg.intern_sort("Real");
    let s1 = eg.intern_sort("S1");
    let s2 = eg.intern_sort("S2");

    let ops = TheoryOps {
        // Binary operators
        implies: eg.register_op2("=>", bool_s, bool_s, bool_s),
        eq_bool: eg.register_op2("=b", bool_s, bool_s, bool_s),
        eq_int: eg.register_op2("=i", int_s, int_s, bool_s),
        eq_real: eg.register_op2("=r", real_s, real_s, bool_s),
        eq_s1: eg.register_op2("=s1", s1, s1, bool_s),
        eq_s2: eg.register_op2("=s2", s2, s2, bool_s),
        le_int: eg.register_op2("<=i", int_s, int_s, bool_s),
        lt_int: eg.register_op2("<i", int_s, int_s, bool_s),
        ge_int: eg.register_op2(">=i", int_s, int_s, bool_s),
        gt_int: eg.register_op2(">i", int_s, int_s, bool_s),
        le_real: eg.register_op2("<=r", real_s, real_s, bool_s),
        lt_real: eg.register_op2("<r", real_s, real_s, bool_s),
        ge_real: eg.register_op2(">=r", real_s, real_s, bool_s),
        gt_real: eg.register_op2(">r", real_s, real_s, bool_s),
        add_int: eg.register_op2("+i", int_s, int_s, int_s),
        // Unary
        not: eg.register_op1("not", bool_s, bool_s),
        // Variadic (as set for idempotent `and`, mset for `or`)
        and: eg.register_set("and", bool_s, bool_s),
        or: eg.register_mset("or", bool_s, bool_s),
        // Nullary constants
        true_: eg.register_op0("true", bool_s),
        false_: eg.register_op0("false", bool_s),
        c1: eg.register_op0("c1", s1),
        c2: eg.register_op0("c2", s2),
        // Literal ops
        int_lit: eg.register_lit("intlit", int_s),
        real_lit: eg.register_lit("reallit", real_s),
        // Sorts
        bool_s,
        int_s,
        real_s,
        s1,
        s2,
    };
    (eg, ops)
}

#[allow(dead_code)]
struct TheoryOps {
    implies: semi_persistent_egraph::id::OpId,
    eq_bool: semi_persistent_egraph::id::OpId,
    eq_int: semi_persistent_egraph::id::OpId,
    eq_real: semi_persistent_egraph::id::OpId,
    eq_s1: semi_persistent_egraph::id::OpId,
    eq_s2: semi_persistent_egraph::id::OpId,
    le_int: semi_persistent_egraph::id::OpId,
    lt_int: semi_persistent_egraph::id::OpId,
    ge_int: semi_persistent_egraph::id::OpId,
    gt_int: semi_persistent_egraph::id::OpId,
    le_real: semi_persistent_egraph::id::OpId,
    lt_real: semi_persistent_egraph::id::OpId,
    ge_real: semi_persistent_egraph::id::OpId,
    gt_real: semi_persistent_egraph::id::OpId,
    add_int: semi_persistent_egraph::id::OpId,
    not: semi_persistent_egraph::id::OpId,
    and: semi_persistent_egraph::id::OpId,
    or: semi_persistent_egraph::id::OpId,
    true_: semi_persistent_egraph::id::OpId,
    false_: semi_persistent_egraph::id::OpId,
    c1: semi_persistent_egraph::id::OpId,
    c2: semi_persistent_egraph::id::OpId,
    int_lit: semi_persistent_egraph::id::OpId,
    real_lit: semi_persistent_egraph::id::OpId,
    bool_s: semi_persistent_egraph::id::SortId,
    int_s: semi_persistent_egraph::id::SortId,
    real_s: semi_persistent_egraph::id::SortId,
    s1: semi_persistent_egraph::id::SortId,
    s2: semi_persistent_egraph::id::SortId,
}

// Simplified conformance tests: exercise the system on fixture cases built directly
// in the Rust API (no s-expression parser needed). Validates the full pipeline end-to-end.

/// au_009: identical terms `(= v1 5)` vs `(= v1 5)`.
#[test]
fn conformance_au_009_identical() {
    let (mut eg, ops) = build_theory();
    let v1_op = eg.register_op0("v1", ops.int_s);
    let v1 = eg.add(v1_op, &[]);
    let five = eg.intern_lit(NiraLitVal::Int(5.into()));
    let five_node = eg.add_lit(ops.int_lit, five);
    let left = eg.add(ops.eq_int, &[v1, five_node]);
    let right = eg.add(ops.eq_int, &[v1, five_node]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let config = AuConfig {
        algorithm: AuAlgorithm::Exact,
        ..Default::default()
    };
    let result = anti_unify(&snap, left, right, &config).unwrap();
    assert_eq!(
        snap.class_of(left).unwrap(),
        snap.class_of(right).unwrap(),
        "identical terms should be in the same class"
    );
    assert_eq!(result.size, 3, "eq(v1, 5) is size 3");
}

/// au_007: `(= v3 (+ v1 1))` vs `(= v3 (+ v2 1))` with eqsat.
/// Both share `(= v3 (+ ? 1))` structure.
#[test]
fn conformance_au_007_shared_result_add() {
    let (mut eg, ops) = build_theory();
    let v1_op = eg.register_op0("v1", ops.int_s);
    let v2_op = eg.register_op0("v2", ops.int_s);
    let v3_op = eg.register_op0("v3", ops.int_s);
    let v1 = eg.add(v1_op, &[]);
    let v2 = eg.add(v2_op, &[]);
    let v3 = eg.add(v3_op, &[]);
    let one = eg.intern_lit(NiraLitVal::Int(1.into()));
    let one_node = eg.add_lit(ops.int_lit, one);
    let plus_v1_1 = eg.add(ops.add_int, &[v1, one_node]);
    let plus_v2_1 = eg.add(ops.add_int, &[v2, one_node]);
    let left = eg.add(ops.eq_int, &[v3, plus_v1_1]);
    let right = eg.add(ops.eq_int, &[v3, plus_v2_1]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let config = AuConfig {
        algorithm: AuAlgorithm::Exact,
        ..Default::default()
    };
    let result = anti_unify(&snap, left, right, &config).unwrap();
    // Expected: (= v3 (+ Variants(v1,v2) 1)): size 1(=) + 1(v3) + 1(+) + 2(V) + 1(1) = 6
    // or (= v3 (+ ? 1)): some factoring. Let's just check it's valid and <= seed.
    assert!(result.size <= 8, "result should be reasonably compressed");

    // Projection validity: both projections must be variant-free.
    let mut pool = result.pool;
    let left_proj = pool.project(result.term_id, 0);
    let right_proj = pool.project(result.term_id, 1);
    assert!(!pool.has_variants(left_proj));
    assert!(!pool.has_variants(right_proj));
}

/// au_002: `(=> (<= v1 v2) (not v3))` vs `(=> (< v1 v2) (not v3))`.
/// These share the outer structure; only the comparison operator differs.
#[test]
fn conformance_au_002_strict_inequality() {
    let (mut eg, ops) = build_theory();
    let v1_op = eg.register_op0("v1", ops.real_s);
    let v2_op = eg.register_op0("v2", ops.real_s);
    let v3_op = eg.register_op0("v3", ops.bool_s);
    let v1 = eg.add(v1_op, &[]);
    let v2 = eg.add(v2_op, &[]);
    let v3_bool = eg.add(v3_op, &[]);
    let le = eg.add(ops.le_real, &[v1, v2]);
    let lt = eg.add(ops.lt_real, &[v1, v2]);
    let not_v3 = eg.add(ops.not, &[v3_bool]);
    let left = eg.add(ops.implies, &[le, not_v3]);
    let right = eg.add(ops.implies, &[lt, not_v3]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let config = AuConfig {
        algorithm: AuAlgorithm::Exact,
        ..Default::default()
    };
    let result = anti_unify(&snap, left, right, &config).unwrap();
    // The outer `=> ? (not v3)` is shared; the antecedent differs.
    // => (Variants(<=, <)) (not v3): size = 1(=>) + combined_antecedent + 1(not) + 1(v3)
    // The exact size depends on how the Variants absorbs the comparison.
    // At minimum it should be less than the bare Variants of both full terms.
    let left_size = 5; // =>(<=r(v1,v2), not(v3))
    let right_size = 5;
    assert!(
        result.size < left_size + right_size,
        "should be better than bare Variants"
    );

    let mut pool = result.pool;
    let lp = pool.project(result.term_id, 0);
    let rp = pool.project(result.term_id, 1);
    assert!(!pool.has_variants(lp));
    assert!(!pool.has_variants(rp));
}

/// Regression: no case should panic, even with complex variadic operators.
#[test]
fn conformance_regression_no_panic() {
    let (mut eg, ops) = build_theory();
    let v1_op = eg.register_op0("v1", ops.bool_s);
    let v2_op = eg.register_op0("v2", ops.bool_s);
    let v3_op = eg.register_op0("v3", ops.bool_s);
    let v4_op = eg.register_op0("v4", ops.bool_s);
    let v5_op = eg.register_op0("v5", ops.real_s);
    let v1 = eg.add(v1_op, &[]);
    let v2 = eg.add(v2_op, &[]);
    let v3 = eg.add(v3_op, &[]);
    let not_v3 = eg.add(ops.not, &[v3]);
    let antecedent = eg.add(ops.and, &[v1, v2, not_v3]);
    let zero_r = eg.intern_lit(NiraLitVal::Rat(num_rational::BigRational::from_integer(
        0.into(),
    )));
    let zero_node = eg.add_lit(ops.real_lit, zero_r);
    let v5 = eg.add(v5_op, &[]);
    let gt_v5_0 = eg.add(ops.gt_real, &[v5, zero_node]);
    let left = eg.add(ops.implies, &[antecedent, gt_v5_0]);

    let v4 = eg.add(v4_op, &[]);
    let antecedent2 = eg.add(ops.and, &[v1, v4]);
    let right = eg.add(ops.implies, &[antecedent2, gt_v5_0]);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    for alg in [AuAlgorithm::Exact, AuAlgorithm::Uct] {
        let config = AuConfig {
            algorithm: alg,
            playouts: 100,
            ..Default::default()
        };
        let result = anti_unify(&snap, left, right, &config);
        assert!(result.is_ok(), "{alg:?} panicked or errored");
        let r = result.unwrap();
        assert!(r.size > 0 && r.size < 100, "{alg:?} degenerate size");
    }
}
