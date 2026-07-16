// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Anti-unification demo: builds a series of e-graph pairs and prints the
//! anti-unifiers found by the syntactic baseline, the exact solver, and MCGS.
//!
//! Run with: `cargo run --example au_demo -p semi-persistent-egraph`

use num_bigint::BigInt;
use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, AuResult, anti_unify};
use semi_persistent_egraph::au::terms::TermOp;
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::nodes::LitValId;

type Eg = EGraph31<NiraLitVal, false, false>;

/// Render a result term using the e-graph's operator names and literal values.
fn render(eg: &Eg, result: &AuResult<OpId, LitValId>) -> String {
    result.to_string_with(|op| match op {
        TermOp::EGraph(o) => eg.ops().info(*o).name.clone(),
        TermOp::Literal(_, v) => format!("{}", eg.lits().get(*v)),
        TermOp::Variants => "Variants".to_string(),
    })
}

/// Run all three algorithms on one class pair and print the results.
fn run_case(title: &str, eg: &Eg, left: ENodeId, right: ENodeId) {
    println!("=== {title} ===");

    let snap = AuSnapshot::new(eg).expect("snapshot construction failed");

    for (name, algorithm, playouts) in [
        ("syntactic", AuAlgorithm::Syntactic, 0),
        ("exact     ", AuAlgorithm::Exact, 0),
        ("uct       ", AuAlgorithm::Uct, 2000),
    ] {
        let config = AuConfig {
            algorithm,
            playouts,
            ..Default::default()
        };
        match anti_unify(&snap, left, right, &config) {
            Ok(result) => {
                println!("  {name}  size {:>3}  {}", result.size, render(eg, &result));
            }
            Err(e) => println!("  {name}  ERROR: {e}"),
        }
    }
    println!();
}

/// Example 1: identical terms — the anti-unifier is the term itself.
fn example_identical() {
    let mut eg = Eg::new();
    let int = eg.intern_sort("Int");
    let x = eg.register_op0("x", int);
    let f = eg.register_op1("f", int, int);

    let xv = eg.add(x, &[]);
    let fx = eg.add(f, &[xv]);
    let fx2 = eg.add(f, &[xv]);
    eg.rebuild();

    run_case("identical terms: f(x) vs f(x)", &eg, fx, fx2);
}

/// Example 2: one differing leaf — the classic anti-unification textbook case.
fn example_one_hole() {
    let mut eg = Eg::new();
    let int = eg.intern_sort("Int");
    let a = eg.register_op0("a", int);
    let b = eg.register_op0("b", int);
    let c = eg.register_op0("c", int);
    let g = eg.register_op2("g", int, int, int);

    let av = eg.add(a, &[]);
    let bv = eg.add(b, &[]);
    let cv = eg.add(c, &[]);
    let gab = eg.add(g, &[av, bv]);
    let gac = eg.add(g, &[av, cv]);
    eg.rebuild();

    run_case("one hole: g(a,b) vs g(a,c)", &eg, gab, gac);
}

/// Example 3: nested structure with two holes.
fn example_nested() {
    let mut eg = Eg::new();
    let int = eg.intern_sort("Int");
    let a = eg.register_op0("a", int);
    let b = eg.register_op0("b", int);
    let c = eg.register_op0("c", int);
    let d = eg.register_op0("d", int);
    let f = eg.register_op1("f", int, int);
    let g = eg.register_op2("g", int, int, int);

    let av = eg.add(a, &[]);
    let bv = eg.add(b, &[]);
    let cv = eg.add(c, &[]);
    let dv = eg.add(d, &[]);
    let fa = eg.add(f, &[av]);
    let fc = eg.add(f, &[cv]);
    let left = eg.add(g, &[fa, bv]); // g(f(a), b)
    let right = eg.add(g, &[fc, dv]); // g(f(c), d)
    eg.rebuild();

    run_case("nested: g(f(a),b) vs g(f(c),d)", &eg, left, right);
}

/// Example 4: literals — same value pairs, different values become Variants.
fn example_literals() {
    let mut eg = Eg::new();
    let int = eg.intern_sort("Int");
    let lit = eg.register_lit("intlit", int);
    let plus = eg.register_mset("plus", int, int);

    let n10 = eg.intern_lit(NiraLitVal::Int(BigInt::from(10)));
    let n20 = eg.intern_lit(NiraLitVal::Int(BigInt::from(20)));
    let n30 = eg.intern_lit(NiraLitVal::Int(BigInt::from(30)));

    let v10 = eg.add_lit(lit, n10);
    let v20 = eg.add_lit(lit, n20);
    let v30 = eg.add_lit(lit, n30);

    let left = eg.add(plus, &[v10, v20]); // 10 + 20
    let right = eg.add(plus, &[v10, v30]); // 10 + 30
    eg.rebuild();

    run_case("literals: (+ 10 20) vs (+ 10 30)", &eg, left, right);
}

/// Example 5: commutative operator — the crossed orientation can win.
fn example_commutative() {
    let mut eg = Eg::new();
    let int = eg.intern_sort("Int");
    let a = eg.register_op0("a", int);
    let b = eg.register_op0("b", int);
    let eq = eg.register_c("eq", [int, int], int);

    let av = eg.add(a, &[]);
    let bv = eg.add(b, &[]);
    let eq_ab = eg.add(eq, &[av, bv]); // stored sorted: eq(a,b)
    let eq_ba = eg.add(eq, &[bv, av]); // canonizes to the same node
    eg.rebuild();

    run_case("commutative: eq(a,b) vs eq(b,a)", &eg, eq_ab, eq_ba);
}

/// Example 6: AC multiset — Appendix B's worked example.
fn example_ac() {
    let mut eg = Eg::new();
    let bool_s = eg.intern_sort("Bool");
    let a = eg.register_op0("a", bool_s);
    let b = eg.register_op0("b", bool_s);
    let c = eg.register_op0("c", bool_s);
    let d = eg.register_op0("d", bool_s);
    let and = eg.register_set("and", bool_s, bool_s);

    let av = eg.add(a, &[]);
    let bv = eg.add(b, &[]);
    let cv = eg.add(c, &[]);
    let dv = eg.add(d, &[]);
    let left = eg.add(and, &[av, bv, cv]); // and{a,b,c}
    let right = eg.add(and, &[bv, cv, dv]); // and{b,c,d}
    eg.rebuild();

    run_case(
        "AC (Appendix B): and{a,b,c} vs and{b,c,d}",
        &eg,
        left,
        right,
    );
}

/// Example 7: AC with repeated children — multiplicities compress the matrix space.
fn example_ac_multiplicity() {
    let mut eg = Eg::new();
    let int = eg.intern_sort("Int");
    let a = eg.register_op0("a", int);
    let b = eg.register_op0("b", int);
    let plus = eg.register_mset("plus", int, int);

    let av = eg.add(a, &[]);
    let bv = eg.add(b, &[]);
    let left = eg.add(plus, &[av, av, bv]); // plus{a,a,b}
    let right = eg.add(plus, &[av, bv, bv]); // plus{a,b,b}
    eg.rebuild();

    run_case(
        "AC multiplicities: plus{a,a,b} vs plus{a,b,b}",
        &eg,
        left,
        right,
    );
}

/// Example 8: equivalence helps — a merge lets the e-graph find shared structure
/// that no syntactic comparison of the original terms could find.
fn example_saturation_helps() {
    let mut eg = Eg::new();
    let int = eg.intern_sort("Int");
    let a = eg.register_op0("a", int);
    let b = eg.register_op0("b", int);
    let c = eg.register_op0("c", int);
    let f = eg.register_op1("f", int, int);
    let g = eg.register_op2("g", int, int, int);

    let av = eg.add(a, &[]);
    let bv = eg.add(b, &[]);
    let cv = eg.add(c, &[]);

    // left = g(a, b); right = g(f(c), b).
    // Then we assert a = f(c) (as a rewrite would during saturation):
    // now AU can factor g(<a=f(c)>, b) with zero Variants.
    let fc = eg.add(f, &[cv]);
    let left = eg.add(g, &[av, bv]);
    let right = eg.add(g, &[fc, bv]);
    eg.merge(av, fc);
    eg.rebuild();

    run_case(
        "equivalence: g(a,b) vs g(f(c),b) with a = f(c) merged",
        &eg,
        left,
        right,
    );
}

/// Example 9: cyclic e-graph — x = f(x) on one side; cycle contexts keep it finite.
fn example_cyclic() {
    let mut eg = Eg::new();
    let int = eg.intern_sort("Int");
    let x = eg.register_op0("x", int);
    let y = eg.register_op0("y", int);
    let f = eg.register_op1("f", int, int);

    let xv = eg.add(x, &[]);
    let fx = eg.add(f, &[xv]);
    let yv = eg.add(y, &[]);
    let fy = eg.add(f, &[yv]);
    // Cycle: x = f(x).
    eg.merge(xv, fx);
    eg.rebuild();

    run_case("cyclic: class{x, f(x), ...} vs f(y)", &eg, xv, fy);
}

/// Example 10: completely disjoint terms — the anti-unifier is a bare Variants.
fn example_disjoint() {
    let mut eg = Eg::new();
    let int = eg.intern_sort("Int");
    let a = eg.register_op0("a", int);
    let f = eg.register_op1("f", int, int);
    let g2 = eg.register_op2("g", int, int, int);
    let b = eg.register_op0("b", int);

    let av = eg.add(a, &[]);
    let bv = eg.add(b, &[]);
    let fa = eg.add(f, &[av]);
    let gbb = eg.add(g2, &[bv, bv]);
    eg.rebuild();

    run_case("disjoint: f(a) vs g(b,b)", &eg, fa, gbb);
}

fn main() {
    println!("Anti-unification demo: three algorithms on ten e-graph pairs.");
    println!("Sizes count 1 per node; Variants nodes are free (children counted).\n");

    example_identical();
    example_one_hole();
    example_nested();
    example_literals();
    example_commutative();
    example_ac();
    example_ac_multiplicity();
    example_saturation_helps();
    example_cyclic();
    example_disjoint();
}
