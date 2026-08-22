// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::panic::{AssertUnwindSafe, catch_unwind};

use semi_persistent_traversals::rec_family;

rec_family! {
    family MarkContracts => MarkStore;
    enum Root { One(Node) }
    enum Node {
        Leaf(i64),
        Link(Node),
        Many(Variadic<Node>),
    }
}

fn assert_panics(f: impl FnOnce()) {
    assert!(catch_unwind(AssertUnwindSafe(f)).is_err());
}

#[test]
fn restore_rejects_a_mark_from_another_store() {
    let mut first = MarkStore::new();
    first.push_node(NodeNode::Leaf(1));
    let mark = first.mark();

    let mut second = MarkStore::new();
    second.push_node(NodeNode::Leaf(2));

    assert_panics(|| second.restore(&mark));
}

#[test]
fn restore_rejects_a_mark_invalidated_by_in_place_mutation() {
    let mut store = MarkStore::new();
    let original = store.push_node(NodeNode::Leaf(1));
    let parent = store.push_node(NodeNode::Link(original));
    let mark = store.mark();

    let speculative = store.push_node(NodeNode::Leaf(2));
    store.set_node(parent, NodeNode::Link(speculative));

    // Truncating to this mark without undoing the mutation would leave
    // `parent` pointing at the discarded `speculative` node.
    assert_panics(|| store.restore(&mark));
}

#[test]
fn restore_rejects_a_mark_ahead_of_the_current_store() {
    let mut store = MarkStore::new();
    let empty = store.mark();
    store.push_node(NodeNode::Leaf(1));
    let future = store.mark();

    store.restore(&empty);
    assert_panics(|| store.restore(&future));
}

#[test]
fn restore_checks_variadic_pool_positions_in_a_mark() {
    let mut store = MarkStore::new();
    let leaf = store.push_node(NodeNode::Leaf(1));
    let before_allocation = store.mark();
    let _span = store.alloc_node_node(&[leaf]);
    let after_allocation = store.mark();

    store.restore(&before_allocation);
    assert_panics(|| store.restore(&after_allocation));
}
