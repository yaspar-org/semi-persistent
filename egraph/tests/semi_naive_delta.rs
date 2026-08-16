// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-naive tests B4-V1 / B4-V2 (see doc/design/future/semi-naive-tasks.md).
//!
//! B4-V1 — touched completeness: every node whose canonical (op, child-reprs)
//!         form changed during a round is present in the touched log.
//! B4-V2 — delta correctness: `IndexStore::build_delta(eg, touched)` equals
//!         `IndexStore::build(eg)` restricted to the touched node set, per key.

use std::collections::HashSet;

use proptest::prelude::*;
use semi_persistent_egraph::EGraph;
use semi_persistent_egraph::containers::DenseId;
use semi_persistent_egraph::index::IndexStore;
use semi_persistent_egraph::literal::{NiraLitVal, NiraModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::span_proto::{self, Family};

type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;
type G = semi_persistent_egraph::id::ENodeId;

/// Canonical `(op, [child class-reprs])` form of every node id in `0..n`.
fn canonical_forms(eg: &EG, n: usize) -> Vec<(usize, Vec<usize>)> {
    (0..n)
        .map(|i| {
            let g = G::from_usize(i);
            let op = eg.node_op(g).to_usize();
            let mut children = Vec::new();
            eg.for_each_child(g, |c, _mult| children.push(eg.class_repr(c).to_usize()));
            (op, children)
        })
        .collect()
}

/// Build a, b, c (consts), f(a,b), f(c,b), g(a); rebuild. Returns the egraph
/// and the op ids needed to drive a round.
fn setup() -> EG {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    eg.register_op1("g", e, e);
    eg.register_op0("a", e);
    eg.register_op0("b", e);
    eg.register_op0("c", e);
    let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
    let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
    let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
    let _fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
    let _fcb = eg.add(eg.ops().id_by_name("f").unwrap(), &[c, b]);
    let _ga = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
    eg.rebuild();
    eg
}

/// Run one round: merge a~c, add a fresh node g(c), rebuild. This both
/// recanonicalizes existing parents (f(c,b) → f(a,b)-form, congruent with
/// f(a,b); g(c) → g(a)-form) and creates a fresh node.
fn run_round(eg: &mut EG) {
    eg.clear_touched();
    let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
    let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
    eg.merge(a, c);
    // fresh node introduced this round
    let _gc = eg.add(eg.ops().id_by_name("g").unwrap(), &[c]);
    eg.rebuild();
}

#[test]
fn b4_v1_touched_superset_of_changed() {
    let mut eg = setup();
    let n = eg.node_count(); // freeze the pre-round id range

    let before = canonical_forms(&eg, n);
    run_round(&mut eg);
    let after = canonical_forms(&eg, n);

    let changed: HashSet<usize> = (0..n).filter(|&i| before[i] != after[i]).collect();
    let touched: HashSet<usize> = eg.touched().iter().map(|g| g.to_usize()).collect();

    assert!(
        !changed.is_empty(),
        "test scenario should change at least one node's canonical form"
    );
    for c in &changed {
        assert!(
            touched.contains(c),
            "node {c} changed canonical form but is absent from the touched log\n\
             before={:?} after={:?}\n touched={:?}",
            before[*c],
            after[*c],
            touched
        );
    }
}

/// Assert `delta` equals `full` restricted to the touched node set, exactly:
/// every key's delta bucket is that key's full bucket filtered to touched.
///
/// The families are dense span maps, so a key is an integer and "absent" is the
/// empty slice. The delta's span table may be shorter than the full's, because
/// it is sized to the largest key its own stream carried, and every key past its
/// end must have an empty full bucket after filtering.
fn assert_delta_is_full_restricted(
    family: &str,
    full: &Family<G>,
    delta: &Family<G>,
    tset: &HashSet<usize>,
) {
    let n = span_proto::num_keys(full).max(span_proto::num_keys(delta));
    for k in 0..n {
        let expected: Vec<usize> = span_proto::get(full, k)
            .iter()
            .map(|g| g.to_usize())
            .filter(|x| tset.contains(x))
            .collect();
        let got: Vec<usize> = span_proto::get(delta, k)
            .iter()
            .map(|g| g.to_usize())
            .collect();
        assert_eq!(
            got, expected,
            "{family}: bucket {k} differs from full∩touched"
        );
    }
}

#[test]
fn b4_v2_delta_equals_full_restricted_to_touched() {
    let mut eg = setup();
    run_round(&mut eg);

    let touched: Vec<G> = eg.touched().to_vec();
    let tset: HashSet<usize> = touched.iter().map(|g| g.to_usize()).collect();

    let full = IndexStore::<DefaultConfig>::build(&eg);
    let delta = IndexStore::<DefaultConfig>::build_delta(&eg, &touched);

    assert!(!tset.is_empty(), "round should have touched some nodes");
    // Both indices are built at the same node bound, so their `by_child_pos`
    // keys mean the same `(position, class)` pair.
    assert_eq!(full.child_pos_stride, delta.child_pos_stride);
    assert_delta_is_full_restricted("by_op", &full.by_op, &delta.by_op, &tset);
    assert_delta_is_full_restricted("by_repr", &full.by_repr, &delta.by_repr, &tset);
    assert_delta_is_full_restricted(
        "by_child_pos",
        &full.by_child_pos,
        &delta.by_child_pos,
        &tset,
    );
    assert_delta_is_full_restricted("by_contains", &full.by_contains, &delta.by_contains, &tset);
}

/// Build a graph of random fixed-arity nodes (a/b/c consts, g/1, f/2) from a
/// spec list. Each node references earlier nodes as children, so the graph is
/// a DAG. Returns the egraph and the list of node ids in creation order.
fn build_random(specs: &[u8]) -> (EG, Vec<G>) {
    let mut eg = EG::from_model(&NiraModel);
    let e = eg.intern_sort("E");
    eg.register_op2("f", e, e, e);
    eg.register_op1("g", e, e);
    eg.register_op0("a", e);
    eg.register_op0("b", e);
    eg.register_op0("c", e);
    let of = eg.ops().id_by_name("f").unwrap();
    let og = eg.ops().id_by_name("g").unwrap();
    let oa = eg.ops().id_by_name("a").unwrap();
    let ob = eg.ops().id_by_name("b").unwrap();
    let oc = eg.ops().id_by_name("c").unwrap();

    let mut nodes: Vec<G> = Vec::new();
    for &s in specs {
        let id = match s % 5 {
            0 => eg.add(oa, &[]),
            1 => eg.add(ob, &[]),
            2 => eg.add(oc, &[]),
            3 => {
                let c = *nodes.last().unwrap_or(&eg.add(oa, &[]));
                eg.add(og, &[c])
            }
            _ => {
                let c1 = nodes.first().copied().unwrap_or_else(|| eg.add(oa, &[]));
                let c2 = nodes.last().copied().unwrap_or_else(|| eg.add(ob, &[]));
                eg.add(of, &[c1, c2])
            }
        };
        nodes.push(id);
    }
    eg.rebuild();
    (eg, nodes)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(400))]

    /// B4-V1 generalized: across a random graph and a random sequence of
    /// merges in one round, EVERY node whose canonical (op, child-reprs) form
    /// changed must appear in the touched log. A missed push here is a silent
    /// soundness failure (subset delta → dropped matches), which the
    /// final-state differential tests can mask if the dropped match happens to
    /// be rediscovered later. This targets the `recanonize_node` push site
    /// directly.
    #[test]
    fn touched_superset_random(
        specs in proptest::collection::vec(0u8..5, 2..12),
        merges in proptest::collection::vec((0usize..12, 0usize..12), 0..6),
    ) {
        let (mut eg, nodes) = build_random(&specs);
        prop_assume!(!nodes.is_empty());
        let n = eg.node_count();

        let before = canonical_forms(&eg, n);
        eg.clear_touched();

        // Apply random merges between existing nodes, then rebuild once.
        for (i, j) in merges {
            let a = nodes[i % nodes.len()];
            let b = nodes[j % nodes.len()];
            eg.merge(a, b);
        }
        eg.rebuild();

        let after = canonical_forms(&eg, n);
        let changed: Vec<usize> = (0..n).filter(|&i| before[i] != after[i]).collect();
        let touched: HashSet<usize> = eg.touched().iter().map(|g| g.to_usize()).collect();

        for c in changed {
            prop_assert!(
                touched.contains(&c),
                "node {c} changed canonical form ({:?} -> {:?}) but is absent from touched {:?}",
                before[c], after[c], touched
            );
        }
    }
}
