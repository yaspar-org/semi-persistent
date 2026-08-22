// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::panic::{AssertUnwindSafe, catch_unwind};

use semi_persistent_traversals::{Variadic, rec_family};

rec_family! {
    family Acyclic => AcyclicStore;
    enum Node {
        Link(Node),
        FromOther(Other),
        Many(Variadic<Node>),
        Leaf,
    }
    enum Other { Wrap(Node) }
}

#[test]
fn push_rejects_forward_references_without_inserting_a_node() {
    let mut store = AcyclicStore::new();

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            store.push_node(NodeNode::Link(NodeId(0)));
        }))
        .is_err()
    );
    assert_eq!(store.len_node(), 0);

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            store.push_other(OtherNode::Wrap(NodeId(0)));
        }))
        .is_err()
    );
    assert_eq!(store.len_other(), 0);

    let children = store.alloc_node_node(&[NodeId(0)]);
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            store.push_node(NodeNode::Many(children));
        }))
        .is_err()
    );
    assert_eq!(store.len_node(), 0);
}

#[test]
fn set_rejects_direct_indirect_and_cross_sort_cycles() {
    let mut store = AcyclicStore::new();
    let leaf = store.push_node(NodeNode::Leaf);
    let link = store.push_node(NodeNode::Link(leaf));
    let other = store.push_other(OtherNode::Wrap(leaf));

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            store.set_node(leaf, NodeNode::Link(link));
        }))
        .is_err()
    );
    assert!(matches!(store.get_node(leaf), NodeNode::Leaf));

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            store.set_node(link, NodeNode::Link(link));
        }))
        .is_err()
    );
    assert!(matches!(store.get_node(link), NodeNode::Link(id) if *id == leaf));

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            store.set_node(leaf, NodeNode::FromOther(other));
        }))
        .is_err()
    );
    assert!(matches!(store.get_node(leaf), NodeNode::Leaf));

    let many = store.push_node(NodeNode::Leaf);
    store.set_node(
        many,
        NodeNode::Many(Variadic::Resolved([leaf, link].into_iter().collect())),
    );
    assert!(matches!(
        store.get_node(many),
        NodeNode::Many(Variadic::Span { len: 2, .. })
    ));
}
