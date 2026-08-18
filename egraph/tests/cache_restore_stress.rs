// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Hash-cons cache consistency after restore, exercised past the dirty-list
//! budget. When more pre-mark entries are rewritten than the budget records,
//! restore must fall back to a full index rebuild; these tests assert the
//! observable contract in release builds, where the debug_assert comparing the
//! index against a rebuild is compiled out: after restore, re-adding a term
//! that existed before the mark returns its original id and creates no node.

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::literal::NiraLitVal;

type Eg = EGraph31<NiraLitVal, true, false>;

const K: usize = 64;

/// Leaves plus one layer of nodes over them, using `build` to construct each
/// parent from its leaf. Merging every leaf into leaves[0] then rebuilding
/// rewrites every parent's cache entry: K pre-mark writes against a dirty
/// budget of saved_len / 4, so the budget overflows and restore must rebuild.
fn overflow_scenario(
    eg: &mut Eg,
    build: impl Fn(&mut Eg, semi_persistent_egraph::id::ENodeId) -> semi_persistent_egraph::id::ENodeId,
) {
    let sort = eg.intern_sort("E");
    let leaf_ops: Vec<_> = (0..K)
        .map(|i| eg.register_op0(&format!("a{i}"), sort))
        .collect();
    let leaves: Vec<_> = leaf_ops.iter().map(|&op| eg.add(op, &[])).collect();
    let parents: Vec<_> = leaves.iter().map(|&leaf| build(eg, leaf)).collect();
    let nodes_before = eg.node_count();

    let token = eg.mark(ShrinkPolicy::Never);

    for &leaf in &leaves[1..] {
        eg.merge(leaves[0], leaf);
    }
    eg.rebuild();
    assert_eq!(
        eg.find(parents[0]),
        eg.find(parents[K - 1]),
        "congruence: all parents collapse once the leaves merge"
    );

    eg.restore(token);

    assert_eq!(eg.node_count(), nodes_before, "restore drops the frame's nodes");
    assert_ne!(
        eg.find(leaves[0]),
        eg.find(leaves[1]),
        "restore rolls the merges back"
    );
    for i in 0..K {
        let again = build(eg, leaves[i]);
        assert_eq!(
            again, parents[i],
            "re-adding a pre-mark term must hit the restored cache index"
        );
    }
    assert_eq!(
        eg.node_count(),
        nodes_before,
        "the re-adds must not create nodes: the index still covers them"
    );
}

#[test]
fn fixed_arity_cache_survives_budget_overflow() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let f = eg.register_op1("f", sort, sort);
    overflow_scenario(&mut eg, move |eg, leaf| eg.add(f, &[leaf]));
}

#[test]
fn pool_cache_survives_budget_overflow() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let f = eg.register_opn("f", &[sort; 5], sort);
    overflow_scenario(&mut eg, move |eg, leaf| eg.add(f, &[leaf; 5]));
}

/// Two nested frames, the inner one overflowing its budget, restored straight
/// to the outer token. The inner frame's saved_len is at least the outer's,
/// so the outer restore sees the overflow too and must rebuild.
#[test]
fn nested_marks_outer_restore_after_inner_overflow() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("E");
    let f = eg.register_op1("f", sort, sort);
    let leaf_ops: Vec<_> = (0..K)
        .map(|i| eg.register_op0(&format!("a{i}"), sort))
        .collect();
    let leaves: Vec<_> = leaf_ops.iter().map(|&op| eg.add(op, &[])).collect();
    let parents: Vec<_> = leaves.iter().map(|&leaf| eg.add(f, &[leaf])).collect();
    let nodes_before = eg.node_count();

    let outer = eg.mark(ShrinkPolicy::Never);
    let extra_op = eg.register_op0("extra", sort);
    let extra = eg.add(extra_op, &[]);
    let _extra_parent = eg.add(f, &[extra]);
    let _inner = eg.mark(ShrinkPolicy::Never);

    for &leaf in &leaves[1..] {
        eg.merge(leaves[0], leaf);
    }
    eg.rebuild();

    eg.restore(outer);

    assert_eq!(eg.node_count(), nodes_before, "outer restore drops both frames");
    for i in 0..K {
        assert_eq!(
            eg.add(f, &[leaves[i]]),
            parents[i],
            "pre-outer terms must resolve through the rebuilt index"
        );
    }
    assert_eq!(eg.node_count(), nodes_before);
}

/// Literal store: interning after a mark and restoring must leave the
/// value-to-id index in step with the log. Re-interning a pre-mark literal
/// returns its original id; a rolled-back literal re-interns fresh at the
/// old position instead of resolving to a stale id.
#[test]
fn literal_store_index_consistent_after_restore() {
    let mut eg = Eg::new();
    let before: Vec<_> = (0..K as i64)
        .map(|i| eg.intern_lit(NiraLitVal::Int(i.into())))
        .collect();

    let token = eg.mark(ShrinkPolicy::Never);
    let inside: Vec<_> = (0..K as i64)
        .map(|i| eg.intern_lit(NiraLitVal::Int((1000 + i).into())))
        .collect();
    eg.restore(token);

    for (i, &id) in before.iter().enumerate() {
        assert_eq!(
            eg.intern_lit(NiraLitVal::Int((i as i64).into())),
            id,
            "pre-mark literal must keep its id across restore"
        );
    }
    let refreshed = eg.intern_lit(NiraLitVal::Int(1000.into()));
    assert_eq!(
        refreshed, inside[0],
        "a re-interned rolled-back literal reuses the first free log position"
    );
}
