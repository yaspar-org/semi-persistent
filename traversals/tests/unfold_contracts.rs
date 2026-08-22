// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::panic::{AssertUnwindSafe, catch_unwind};

use semi_persistent_traversals::{Variadic, rec_family};

rec_family! {
    family UnfoldContracts => UnfoldStore;
    enum Root { One(Node) }
    enum Node {
        Leaf(i64),
        Many(Variadic<Node>),
    }
}

fn assert_panics(f: impl FnOnce()) {
    assert!(catch_unwind(AssertUnwindSafe(f)).is_err());
}

fn unfold_layer(seed: UnfoldStoreSeed<u8>) -> UnfoldStoreLayer<u8> {
    match seed {
        UnfoldStoreSeed::Node(1) => {
            UnfoldStoreLayer::Node(NodeNode::Leaf(1), vec![UnfoldStoreSeed::Node(0)])
        }
        UnfoldStoreSeed::Node(0) => UnfoldStoreLayer::Node(NodeNode::Leaf(0), Vec::new()),
        UnfoldStoreSeed::Root(_) | UnfoldStoreSeed::Node(_) => unreachable!(),
    }
}

#[test]
fn unfold_rejects_more_child_seeds_than_the_node_has_holes() {
    let mut store = UnfoldStore::new();
    assert_panics(|| {
        let _ = store.unfold(UnfoldStoreSeed::Node(1), unfold_layer);
    });
}

#[test]
fn unfold_counts_variadic_child_holes() {
    let mut store = UnfoldStore::new();
    assert_panics(|| {
        let _ = store.unfold(UnfoldStoreSeed::Node(1), |seed| match seed {
            UnfoldStoreSeed::Node(1) => UnfoldStoreLayer::Node(
                NodeNode::Many(Variadic::Resolved(vec![NodeId(0), NodeId(0)].into())),
                vec![UnfoldStoreSeed::Node(0)],
            ),
            UnfoldStoreSeed::Node(0) => UnfoldStoreLayer::Node(NodeNode::Leaf(0), Vec::new()),
            UnfoldStoreSeed::Root(_) | UnfoldStoreSeed::Node(_) => unreachable!(),
        });
    });
}

#[test]
fn postunfold_rejects_more_child_seeds_than_the_node_has_holes() {
    let mut store = UnfoldStore::new();
    assert_panics(|| {
        let _ = store.postunfold(
            UnfoldStoreSeed::Node(1),
            |node| node,
            |node| node,
            unfold_layer,
        );
    });
}

fn apo_layer(seed: UnfoldStoreSeed<u8>) -> UnfoldStoreApoLayer<u8> {
    match seed {
        UnfoldStoreSeed::Node(1) => UnfoldStoreApoLayer::Node(
            NodeNode::Leaf(1),
            vec![UnfoldStoreApoSeed::Continue(UnfoldStoreSeed::Node(0))],
        ),
        UnfoldStoreSeed::Node(0) => UnfoldStoreApoLayer::Node(NodeNode::Leaf(0), Vec::new()),
        UnfoldStoreSeed::Root(_) | UnfoldStoreSeed::Node(_) => unreachable!(),
    }
}

#[test]
fn unfold_short_rejects_more_child_seeds_than_the_node_has_holes() {
    let mut store = UnfoldStore::new();
    assert_panics(|| {
        let _ = store.unfold_short(UnfoldStoreSeed::Node(1), apo_layer);
    });
}
