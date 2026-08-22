// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use semi_persistent_traversals::*;
use semi_persistent_traversals_derive::rec_family;
use std::panic::{AssertUnwindSafe, catch_unwind};

rec_family! {
    #[smart_constructors]
    family VLang => VStore;
    enum Root { Program(Variadic<Expr>) }
    enum Expr { Lit(i64), Add(Variadic<Expr>), Neg(Expr) }
}

fn eval<const DEDUP: bool>(store: &VStore<DEDUP>, root: ExprId) -> i64 {
    store
        .fold(
            VStoreRoot::Expr(root),
            |node: RootNodeMapped<i64>| match node {
                RootNodeMapped::Program(xs) => xs.iter().sum::<i64>(),
            },
            |node: ExprNodeMapped<i64>| match node {
                ExprNodeMapped::Lit(n) => n,
                ExprNodeMapped::Add(xs) => xs.iter().sum(),
                ExprNodeMapped::Neg(x) => -x,
            },
        )
        .unwrap_expr()
}

#[test]
fn allocator_and_smart_constructor_spans_are_traversable() {
    let mut store = VStore::new();
    let one = store.lit(1);
    let two = store.lit(2);
    let three = store.lit(3);

    let direct_children = store.alloc_expr_expr(&[one, two, three]);
    let direct = store.push_expr(ExprNode::Add(direct_children));
    let smart = store.add(&[one, two, three]);

    assert!(matches!(
        store.get_expr(direct),
        ExprNode::Add(Variadic::Span { len: 3, .. })
    ));
    assert!(matches!(
        store.get_expr(smart),
        ExprNode::Add(Variadic::Span { len: 3, .. })
    ));
    assert_eq!(eval(&store, direct), 6);
    assert_eq!(eval(&store, smart), 6);
}

#[test]
fn dedup_compares_variadic_children_by_value() {
    let mut store = VStore::new_dedup();
    let one = store.lit(1);
    let two = store.lit(2);

    let first_children = store.alloc_expr_expr(&[one, two]);
    let first_start = match &first_children {
        Variadic::Span { start, .. } => *start,
        Variadic::Resolved(_) => panic!("allocator must return a pool span"),
    };
    let first = store.push_expr(ExprNode::Add(first_children));

    let second_children = store.alloc_expr_expr(&[one, two]);
    let second_start = match &second_children {
        Variadic::Span { start, .. } => *start,
        Variadic::Resolved(_) => panic!("allocator must return a pool span"),
    };
    let second = store.push_expr(ExprNode::Add(second_children));

    let resolved = store.push_expr(ExprNode::Add(Variadic::Resolved(
        [one, two].into_iter().collect(),
    )));
    let reversed = store.add(&[two, one]);

    assert_ne!(first_start, second_start);
    assert_eq!(first, second);
    assert_eq!(first, resolved);
    assert_ne!(first, reversed);
    assert_eq!(store.len_expr(), 4);
    assert!(matches!(
        store.get_expr(first),
        ExprNode::Add(Variadic::Span { start, len: 2, .. }) if *start == first_start
    ));
}

rec_family! {
    family Ownership => OwnershipStore;
    enum Left { Items(Variadic<Item>) }
    enum Right { Items(Variadic<Item>) }
    enum Item { Value(i64) }
}

#[test]
fn spans_are_rejected_by_other_pools_and_stores() {
    let mut store = OwnershipStore::new();
    let one = store.push_item(ItemNode::Value(1));
    let two = store.push_item(ItemNode::Value(2));
    let nine = store.push_item(ItemNode::Value(9));
    let ten = store.push_item(ItemNode::Value(10));

    let left_span = store.alloc_left_item(&[one, two]);
    let right_span = store.alloc_right_item(&[nine, ten]);
    let right = store.push_right(RightNode::Items(right_span));

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            store.push_right(RightNode::Items(left_span));
        }))
        .is_err()
    );

    let mut other = OwnershipStore::new();
    let other_one = other.push_item(ItemNode::Value(1));
    let other_two = other.push_item(ItemNode::Value(2));
    let other_span = other.alloc_right_item(&[other_one, other_two]);
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            store.push_right(RightNode::Items(other_span));
        }))
        .is_err()
    );

    let sum = store
        .fold(
            OwnershipStoreRoot::Right(right),
            |node: LeftNodeMapped<i64>| match node {
                LeftNodeMapped::Items(values) => values.iter().sum::<i64>(),
            },
            |node: RightNodeMapped<i64>| match node {
                RightNodeMapped::Items(values) => values.iter().sum::<i64>(),
            },
            |node: ItemNodeMapped| match node {
                ItemNodeMapped::Value(value) => value,
            },
        )
        .unwrap_right();
    assert_eq!(sum, 19);
}

#[test]
fn cloned_stores_rebrand_spans() {
    let mut original = OwnershipStore::new();
    let one = original.push_item(ItemNode::Value(1));
    let two = original.push_item(ItemNode::Value(2));
    let node = original.alloc_right_item(&[one, two]);
    let root = original.push_right(RightNode::Items(node));

    let mut cloned = original.clone();
    let original_span = original.alloc_right_item(&[one, two]);
    let cloned_span = cloned.alloc_right_item(&[one, two]);

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            original.push_right(RightNode::Items(cloned_span));
        }))
        .is_err()
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            cloned.push_right(RightNode::Items(original_span));
        }))
        .is_err()
    );

    let cloned_sum = cloned
        .fold(
            OwnershipStoreRoot::Right(root),
            |node: LeftNodeMapped<i64>| match node {
                LeftNodeMapped::Items(values) => values.iter().sum::<i64>(),
            },
            |node: RightNodeMapped<i64>| match node {
                RightNodeMapped::Items(values) => values.iter().sum::<i64>(),
            },
            |node: ItemNodeMapped| match node {
                ItemNodeMapped::Value(value) => value,
            },
        )
        .unwrap_right();
    assert_eq!(cloned_sum, 3);
}

#[test]
fn deduplicating_smart_constructors_do_not_grow_the_pool() {
    let mut store = VStore::new_dedup();
    let one = store.lit(1);
    let two = store.lit(2);
    let first = store.add(&[one, two]);

    for _ in 0..100 {
        assert_eq!(store.add(&[one, two]), first);
    }

    let end = store.alloc_expr_expr(&[]);
    assert!(matches!(
        end,
        Variadic::Span {
            start: 2,
            len: 0,
            ..
        }
    ));
    assert_eq!(store.len_expr(), 3);
}

#[test]
fn insertion_and_transform_canonicalize_resolved_variadics() {
    let mut store = VStore::new();
    let one = store.lit(1);
    let two = store.lit(2);
    let sum = store.push_expr(ExprNode::Add(Variadic::Resolved(
        [one, two].into_iter().collect(),
    )));

    assert!(matches!(
        store.get_expr(sum),
        ExprNode::Add(Variadic::Span { len: 2, .. })
    ));
    let resolved = store.get_expr_resolved(sum);
    assert!(matches!(
        &resolved,
        ExprNode::Add(Variadic::Resolved(values))
            if values.as_slice() == [one, two]
    ));
    let mapped = store.map_expr_children(sum, &mut |id: &ExprId| id.0);
    assert!(matches!(
        mapped,
        ExprNodeMapped::Add(Variadic::Resolved(values))
            if values.as_slice() == [one.0, two.0]
    ));

    let (transformed, transformed_root) =
        store.transform(VStoreRoot::Expr(sum), |node| node, |node| node);
    let transformed_sum = match transformed_root {
        VStoreRoot::Expr(id) => id,
        VStoreRoot::Root(_) => panic!("unexpected root sort"),
    };
    assert!(matches!(
        transformed.get_expr(transformed_sum),
        ExprNode::Add(Variadic::Span { len: 2, .. })
    ));
    assert_eq!(
        store.get_expr_resolved(sum),
        transformed.get_expr_resolved(transformed_sum)
    );
    assert_eq!(eval(&transformed, transformed_sum), 3);
}

#[test]
fn restore_prunes_variadic_dedup_buckets() {
    let mut store = VStore::new_dedup();
    let one = store.lit(1);
    let two = store.lit(2);
    let mark = store.mark();

    let discarded = store.add(&[one, two]);
    assert_eq!(store.len_expr(), 3);
    store.restore(&mark);
    assert_eq!(store.len_expr(), 2);

    let replacement = store.add(&[one, two]);
    assert_eq!(replacement, discarded);
    assert_eq!(store.len_expr(), 3);
    assert_eq!(eval(&store, replacement), 3);
}

#[test]
fn pool_backed_variadics_work_in_rewrites_and_zippers() {
    let mut store = VStore::new();
    let one = store.lit(1);
    let two = store.lit(2);
    let three = store.lit(3);
    let sum = store.add(&[one, two, three]);
    let root = VStoreRoot::Expr(sum);

    let original_count = store
        .fold_with_original(
            root,
            |original, _: RootNodeMapped<usize>| match original {
                RootNode::Program(xs) => xs.iter().count(),
            },
            |original, mapped: ExprNodeMapped<usize>| match (original, mapped) {
                (ExprNode::Add(xs), ExprNodeMapped::Add(_)) => xs.iter().count(),
                _ => 0,
            },
        )
        .unwrap_expr();
    assert_eq!(original_count, 3);

    let (rewritten, rewritten_root) = store.rewrite(
        root,
        |node, out| out.push_root(node),
        |node, out| match node {
            ExprNode::Lit(n) => out.push_expr(ExprNode::Lit(n * 2)),
            other => out.push_expr(other),
        },
    );
    let rewritten_sum = match rewritten_root {
        VStoreRoot::Expr(id) => id,
        VStoreRoot::Root(_) => panic!("unexpected root sort"),
    };
    assert_eq!(eval(&rewritten, rewritten_sum), 12);

    let (transformed, transformed_root) = store.transform(
        root,
        |node| node,
        |node| match node {
            ExprNode::Lit(n) => ExprNode::Lit(n + 1),
            other => other,
        },
    );
    let transformed_sum = match transformed_root {
        VStoreRoot::Expr(id) => id,
        VStoreRoot::Root(_) => panic!("unexpected root sort"),
    };
    assert_eq!(eval(&transformed, transformed_sum), 9);

    let (top_down, top_down_root) = store.rewrite_down(
        root,
        |node| node,
        |node| {
            if let ExprNode::Add(xs) = &node {
                assert_eq!(xs.iter().count(), 3);
            }
            node
        },
    );
    let top_down_sum = match top_down_root {
        VStoreRoot::Expr(id) => id,
        VStoreRoot::Root(_) => panic!("unexpected root sort"),
    };
    assert_eq!(eval(&top_down, top_down_sum), 6);

    let mut zipper = VStoreZipper::new(&store, root);
    assert_eq!(zipper.child_count(), 3);
    assert!(zipper.down(1));
    assert_eq!(zipper.focus(), VStoreRoot::Expr(two));
}
