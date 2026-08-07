// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Direct tests for `extract::extract_best`.
//!
//! The `.egg` fixtures in `tests/egg/` reach extraction through the
//! interpreter, which only prints the result — so they check that extraction
//! runs, not what it returns. These call it directly and assert the term.
//!
//! The cases are chosen around what `extract_best` can get wrong independently
//! of the rest of the system: which node it picks when a class holds several
//! (the fixpoint), how a shared class is reproduced (`reconstruct`), and that a
//! cycle does not defeat the reachability test — which is a sentinel comparison
//! on the cost table, so it has to keep "cost not yet known" distinct from a
//! real cost.
//!
//! There is no test for `extract_best` returning `None`. That needs a class
//! whose every member depends on an unreachable class, and `add` cannot build
//! one: a node's children are ids that already exist, so every class is grounded
//! through the leaves it was built from. The `None` arm is defensive.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::extract::extract_best;
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;

fn eg() -> EG {
    EG::from_model(&NiraModel)
}

#[test]
fn leaf_extracts_itself() {
    let mut eg = eg();
    let e = eg.intern_sort("E");
    let a = eg.register_op0("a", e);
    let id = eg.add(a, &[]);
    eg.rebuild();
    assert_eq!(extract_best(&eg, id).unwrap().to_string(), "(a)");
}

#[test]
fn picks_the_cheaper_of_two_nodes_in_one_class() {
    let mut eg = eg();
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    let a = eg.register_op0("a", e);
    let b = eg.register_op0("b", e);
    let f = eg.ops().id_by_name("f").unwrap();

    let ia = eg.add(a, &[]);
    let ib = eg.add(b, &[]);
    let big = eg.add(f, &[ia, ib]);
    eg.merge(big, ib);
    eg.rebuild();

    // The class holds both `(f a b)` (cost 3) and `b` (cost 1).
    assert_eq!(extract_best(&eg, big).unwrap().to_string(), "(b)");
}

#[test]
fn cheaper_child_propagates_to_the_parent() {
    let mut eg = eg();
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    eg.register_op1("g", e, e);
    let a = eg.register_op0("a", e);
    let b = eg.register_op0("b", e);
    let f = eg.ops().id_by_name("f").unwrap();
    let g = eg.ops().id_by_name("g").unwrap();

    let ia = eg.add(a, &[]);
    let ib = eg.add(b, &[]);
    let ga = eg.add(g, &[ia]);
    eg.merge(ga, ib);
    let root = eg.add(f, &[ga, ia]);
    eg.rebuild();

    // `g(a) = b`, so the root's cheapest form substitutes `b` for `g(a)`. This
    // is the case that needs more than one fixpoint pass to be wrong-free: the
    // child's improvement has to be visible when the parent is costed.
    assert_eq!(extract_best(&eg, root).unwrap().to_string(), "(f (b) (a))");
}

#[test]
fn shared_subterm_is_reproduced_at_each_occurrence() {
    let mut eg = eg();
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    let a = eg.register_op0("a", e);
    let f = eg.ops().id_by_name("f").unwrap();

    let ia = eg.add(a, &[]);
    let x1 = eg.add(f, &[ia, ia]);
    let x2 = eg.add(f, &[x1, x1]);
    eg.rebuild();

    // One class per level, but the term is a full binary tree: the DAG-sharing
    // case, and the shape `extract_bench`'s `dag` workload scales up.
    assert_eq!(
        extract_best(&eg, x2).unwrap().to_string(),
        "(f (f (a) (a)) (f (a) (a)))"
    );
}

#[test]
fn cyclic_class_extracts_through_its_grounded_member() {
    let mut eg = eg();
    let e = eg.intern_sort("E");
    eg.register_op1("g", e, e);
    let a = eg.register_op0("a", e);
    let g = eg.ops().id_by_name("g").unwrap();

    let ia = eg.add(a, &[]);
    let ga = eg.add(g, &[ia]);
    let gga = eg.add(g, &[ga]);
    // Merge the leaf into `g(g(a))`, so the merged class's members are `a`,
    // `g(g(a))` -- still grounded through `a`. This asserts the *positive* side
    // of the reachability test under a cycle, which is the case the cost table's
    // sentinel has to keep distinct from "no cost yet".
    eg.merge(ia, gga);
    eg.rebuild();

    let t = extract_best(&eg, gga).expect("class is grounded through the leaf");
    assert_eq!(t.to_string(), "(a)");
}
