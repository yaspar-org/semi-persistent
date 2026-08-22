// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::panic::{AssertUnwindSafe, catch_unwind};

use semi_persistent_traversals::{DenseMapping, MappingOps, rec_family};

rec_family! {
    family MappingContracts => MappingStore;
    enum Root { One(Node) }
    enum Node {
        Leaf(i64),
        Link(Node),
        Pair(Node, Node),
    }
}

fn assert_panics(f: impl FnOnce()) {
    assert!(catch_unwind(AssertUnwindSafe(f)).is_err());
}

#[test]
fn dense_mapping_rejects_reads_before_assignment() {
    let mapping = <DenseMapping as MappingOps>::new(1);
    assert_panics(|| {
        let _ = mapping.get(0);
    });
}

#[test]
fn rewrite_rejects_an_id_outside_the_output_arena() {
    let mut store = MappingStore::new();
    let leaf = store.push_node(NodeNode::Leaf(1));

    assert_panics(|| {
        let _ = store.rewrite(
            MappingStoreRoot::Node(leaf),
            |node, output| output.push_root(node),
            |_node, _output| NodeId(17),
        );
    });
}

fn graph_with_a_safe_sibling() -> (MappingStore, NodeId, NodeId) {
    let mut store = MappingStore::new();
    let safe = store.push_node(NodeNode::Leaf(1));
    let focus = store.push_node(NodeNode::Leaf(2));
    let ancestor = store.push_node(NodeNode::Link(focus));
    let root = store.push_node(NodeNode::Pair(safe, ancestor));
    (store, ancestor, root)
}

#[test]
fn rewrite_down_rejects_a_cycle_introduced_by_the_rule() {
    let (store, ancestor, root) = graph_with_a_safe_sibling();

    assert_panics(|| {
        let _ = store.rewrite_down(
            MappingStoreRoot::Node(root),
            |node| node,
            |node| match node {
                NodeNode::Leaf(2) => NodeNode::Link(ancestor),
                other => other,
            },
        );
    });
}

#[test]
fn zipper_cow_rejects_a_cycle_introduced_by_the_replacement() {
    let (store, ancestor, root) = graph_with_a_safe_sibling();
    let mut zipper = MappingStoreZipperCow::new(&store, MappingStoreRoot::Node(root));
    assert!(zipper.down(1));
    assert!(zipper.down(0));

    assert_panics(|| {
        let _ = zipper.set_focus_node(NodeNode::Link(ancestor));
    });
}
