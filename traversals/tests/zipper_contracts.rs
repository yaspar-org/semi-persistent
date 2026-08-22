// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use semi_persistent_traversals::rec_family;

rec_family! {
    family ZipperContracts => ZipperStore;
    enum Root { One(Node) }
    enum Node {
        Leaf(i64),
        Pair(Node, Node),
    }
}

#[test]
fn failed_sibling_navigation_preserves_the_cursor() {
    let mut store = ZipperStore::new();
    let left = store.push_node(NodeNode::Leaf(1));
    let right = store.push_node(NodeNode::Leaf(2));
    let root = store.push_node(NodeNode::Pair(left, right));
    let mut zipper = ZipperStoreZipper::new(&store, ZipperStoreRoot::Node(root));
    assert!(zipper.down(0));
    let focus = zipper.focus();
    let depth = zipper.depth();

    assert!(!zipper.sibling(usize::MAX));
    assert_eq!(zipper.focus(), focus);
    assert_eq!(zipper.depth(), depth);
}
