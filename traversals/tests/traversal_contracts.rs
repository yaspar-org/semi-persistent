// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::cell::{Cell, RefCell};

use semi_persistent_traversals::{Ann, rec_family};

rec_family! {
    family ShortCircuit => ShortCircuitStore;
    enum Control { If(Value, Value, Value) }
    enum Value { Bool(bool), Work }
}

#[test]
fn fold_short_terminates_postorder_but_does_not_prune_parent_branches() {
    let mut store = ShortCircuitStore::new();
    let condition = store.push_value(ValueNode::Bool(false));
    let then_branch = store.push_value(ValueNode::Work);
    let else_branch = store.push_value(ValueNode::Work);
    let root = store.push_control(ControlNode::If(condition, then_branch, else_branch));
    let work_visits = Cell::new(0);

    let result = store.fold_short(
        ShortCircuitStoreRoot::Control(root),
        |node: ControlNodeMapped<bool>| match node {
            ControlNodeMapped::If(false, _, _) => Err(true),
            ControlNodeMapped::If(true, _, _) => Ok(false),
        },
        |node: ValueNodeMapped| match node {
            ValueNodeMapped::Bool(value) => Ok(value),
            ValueNodeMapped::Work => {
                work_visits.set(work_visits.get() + 1);
                Ok(true)
            }
        },
    );

    assert!(result.unwrap_control());
    assert_eq!(work_visits.get(), 2);
}

rec_family! {
    family HistoryShape => HistoryShapeStore;
    enum Parent { Root(Mixed) }
    enum Mixed { Pair(Left, Right) }
    enum Left { Leaf }
    enum Right { Leaf }
}

#[test]
fn fold_history_exposes_one_generation_of_untyped_child_indices() {
    let mut store = HistoryShapeStore::new();
    let left = store.push_left(LeftNode::Leaf);
    let right = store.push_right(RightNode::Leaf);
    let mixed = store.push_mixed(MixedNode::Pair(left, right));
    let root = store.push_parent(ParentNode::Root(mixed));
    let observed = RefCell::new(Vec::new());

    let result = store.fold_with_history(
        HistoryShapeStoreRoot::Parent(root),
        |node: ParentNodeMapped<Ann<usize>>| match node {
            ParentNodeMapped::Root(child) => {
                observed.borrow_mut().extend(child.children);
                child.value
            }
        },
        |node: MixedNodeMapped<Ann<usize>, Ann<usize>>| match node {
            MixedNodeMapped::Pair(left, right) => left.value + right.value,
        },
        |_: LeftNodeMapped| 1usize,
        |_: RightNodeMapped| 1usize,
    );

    assert_eq!(result.unwrap_parent(), 2);
    assert_eq!(
        observed.into_inner(),
        vec![0, 0],
        "LeftId(0) and RightId(0) are intentionally untyped in Ann"
    );
}
