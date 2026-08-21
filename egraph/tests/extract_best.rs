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
//! Both extraction failure variants are reachable. A class can contain only
//! `:unextractable` nodes, and an otherwise extractable parent can depend on
//! such a class and therefore have no fully extractable child set.

use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::extract::{ExtractError, extract_best};
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::node_types::FLAG_CONSTRUCTOR;
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::registry::{OpKind, OpMeta};

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

#[test]
fn multiset_multiplicity_is_reproduced_exactly() {
    let mut eg = eg();
    let e = eg.intern_sort("E");
    eg.register_mset("add", e, e);
    let a = eg.register_op0("a", e);
    let b = eg.register_op0("b", e);
    let add = eg.ops().id_by_name("add").unwrap();

    let ia = eg.add(a, &[]);
    let ib = eg.add(b, &[]);
    // `add` is a multiset op, so this is the one path where `for_each_child`
    // reports a multiplicity above 1. `reconstruct` emits `mult` copies of the
    // child term, and the count is the thing that can silently go wrong: an
    // off-by-one there changes the extracted term without failing any other test.
    let s = eg.add(add, &[ia, ia, ia, ib]);
    eg.rebuild();

    let t = extract_best(&eg, s).expect("grounded");
    let printed = t.to_string();
    assert_eq!(printed.matches("(a)").count(), 3, "in {printed}");
    assert_eq!(printed.matches("(b)").count(), 1, "in {printed}");
}

// ── Per-op cost and extractability (`:cost`, `:unextractable`) ──────────────

/// Register a nullary op with explicit metadata (the `(constructor …)` surface form's
/// registration, minus the parser).
fn ctor0(
    eg: &mut EG,
    name: &str,
    sort: <DefaultConfig as semi_persistent_egraph::config::EGraphConfig>::S,
    meta: OpMeta,
) -> <DefaultConfig as semi_persistent_egraph::config::EGraphConfig>::O {
    eg.register_kind_meta(name, sort, OpKind::Normal { arg_sorts: vec![] }, meta)
}

#[test]
fn undeclared_cost_is_one() {
    // The default `OpMeta` has to keep the historical model exactly: a program that
    // declares no `:cost` extracts the same term it did before per-op costs existed.
    let mut eg = eg();
    let e = eg.intern_sort("E");
    eg.register_op1("g", e, e);
    let a = eg.register_op0("a", e);
    let b = ctor0(&mut eg, "b", e, OpMeta::default());
    let g = eg.ops().id_by_name("g").unwrap();

    let ia = eg.add(a, &[]);
    let ga = eg.add(g, &[ia]);
    let ib = eg.add(b, &[]);
    eg.merge(ga, ib);
    eg.rebuild();

    // `(b)` costs 1, `(g (a))` costs 2.
    assert_eq!(extract_best(&eg, ga).unwrap().to_string(), "(b)");
}

#[test]
fn op_cost_changes_the_extracted_winner() {
    let mut eg = eg();
    let e = eg.intern_sort("E");
    eg.register_op1("g", e, e);
    let a = eg.register_op0("a", e);
    // Same graph as `undeclared_cost_is_one`, with one tag changed: the single-node term
    // is now dearer than the two-node one, so the winner flips to the *larger* term. Nothing
    // but the cost model can produce that answer.
    let b = ctor0(
        &mut eg,
        "b",
        e,
        OpMeta {
            cost: 5,
            ..OpMeta::default()
        },
    );
    let g = eg.ops().id_by_name("g").unwrap();

    let ia = eg.add(a, &[]);
    let ga = eg.add(g, &[ia]);
    let ib = eg.add(b, &[]);
    eg.merge(ga, ib);
    eg.rebuild();

    assert_eq!(extract_best(&eg, ga).unwrap().to_string(), "(g (a))");
}

#[test]
fn unextractable_op_is_never_selected() {
    let mut eg = eg();
    let e = eg.intern_sort("E");
    eg.register_op1("g", e, e);
    let a = eg.register_op0("a", e);
    // `(b)` is the cheapest node in the class by cost, and still not selected: the tag is a
    // filter on candidates, not a large cost.
    let b = ctor0(
        &mut eg,
        "b",
        e,
        OpMeta {
            unextractable: true,
            ..OpMeta::default()
        },
    );
    let g = eg.ops().id_by_name("g").unwrap();

    let ia = eg.add(a, &[]);
    let ga = eg.add(g, &[ia]);
    let ib = eg.add(b, &[]);
    eg.merge(ga, ib);
    eg.rebuild();

    assert_eq!(extract_best(&eg, ga).unwrap().to_string(), "(g (a))");
}

#[test]
fn class_of_only_unextractable_nodes_reports_the_class() {
    let mut eg = eg();
    let e = eg.intern_sort("E");
    let hidden = ctor0(
        &mut eg,
        "hidden",
        e,
        OpMeta {
            unextractable: true,
            ..OpMeta::default()
        },
    );
    let id = eg.add(hidden, &[]);
    eg.rebuild();

    // A clean error naming the class and the ops that excluded it — not a panic, and not a
    // silent "no term".
    match extract_best(&eg, id) {
        Err(ExtractError::AllUnextractable { class, ops }) => {
            assert_eq!(class, eg.find_const(id).to_usize());
            assert_eq!(ops, vec!["hidden".to_string()]);
        }
        other => panic!("expected AllUnextractable, got {other:?}"),
    }
}

#[test]
fn parent_of_an_unextractable_class_reports_no_ground_term() {
    let mut eg = eg();
    let e = eg.intern_sort("E");
    let hidden = ctor0(
        &mut eg,
        "hidden",
        e,
        OpMeta {
            unextractable: true,
            ..OpMeta::default()
        },
    );
    let parent = eg.register_op1("parent", e, e);
    let child = eg.add(hidden, &[]);
    let root = eg.add(parent, &[child]);
    eg.rebuild();

    assert_eq!(
        extract_best(&eg, root),
        Err(ExtractError::NoGroundTerm {
            class: eg.find_const(root).to_usize(),
        })
    );
}

#[test]
fn subsumed_node_is_still_extractable() {
    // Documents current behavior, which `:unextractable` deliberately does not change:
    // `(subsume …)` hides a node from *matching* only, and the extractor still selects it.
    // This is why `:unextractable` cannot be faked with subsumption, and why extraction had
    // to grow its own filter. See doc/design/16-extraction.md.
    let mut eg = eg();
    let e = eg.intern_sort("E");
    eg.register_op1("g", e, e);
    let a = eg.register_op0("a", e);
    let b = eg.register_op0("b", e);
    let g = eg.ops().id_by_name("g").unwrap();

    let ia = eg.add(a, &[]);
    let ga = eg.add(g, &[ia]);
    let ib = eg.add(b, &[]);
    eg.merge(ga, ib);
    eg.rebuild();
    eg.subsume(eg.find_const(ib));

    assert_eq!(extract_best(&eg, ga).unwrap().to_string(), "(b)");
}

#[test]
fn constructor_flag_is_stamped_on_nodes() {
    // `FLAG_CONSTRUCTOR` is written at node creation from the op's registration metadata,
    // and only for constructors.
    let mut eg = eg();
    let e = eg.intern_sort("E");
    let c = ctor0(
        &mut eg,
        "c",
        e,
        OpMeta {
            is_constructor: true,
            ..OpMeta::default()
        },
    );
    let f = ctor0(&mut eg, "f", e, OpMeta::default());
    let ic = eg.add(c, &[]);
    let if_ = eg.add(f, &[]);
    eg.rebuild();

    assert_ne!(eg.node_flags(ic) & FLAG_CONSTRUCTOR, 0, "constructor node");
    assert_eq!(eg.node_flags(if_) & FLAG_CONSTRUCTOR, 0, "function node");
}
