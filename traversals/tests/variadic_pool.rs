// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use proptest::prelude::*;
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

fn unwrap_expr(root: VStoreRoot) -> ExprId {
    match root {
        VStoreRoot::Expr(id) => id,
        VStoreRoot::Root(_) => panic!("unexpected root sort"),
    }
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

#[test]
fn resolved_nodes_compare_variadic_children_by_value() {
    let mut store = VStore::new();
    let one = store.lit(1);
    let two = store.lit(2);
    let first = store.add(&[one, two]);
    let second = store.add(&[one, two]);

    assert_ne!(first, second);
    assert_eq!(
        store.get_expr_resolved(first),
        store.get_expr_resolved(second)
    );
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
fn smart_constructor_deduplicates_against_generic_push_without_growing_the_pool() {
    let mut store = VStore::new_dedup();
    let one = store.lit(1);
    let two = store.lit(2);
    let children = store.alloc_expr_expr(&[one, two]);
    let generic = store.push_expr(ExprNode::Add(children));

    assert_eq!(store.add(&[one, two]), generic);
    assert!(matches!(
        store.alloc_expr_expr(&[]),
        Variadic::Span {
            start: 2,
            len: 0,
            ..
        }
    ));
}

#[test]
fn smart_constructor_validates_all_children_before_growing_the_pool() {
    let mut store = VStore::new();
    let one = store.lit(1);

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            store.add(&[one, ExprId(usize::MAX)]);
        }))
        .is_err()
    );
    assert!(matches!(
        store.alloc_expr_expr(&[]),
        Variadic::Span {
            start: 0,
            len: 0,
            ..
        }
    ));

    let mut dedup = VStore::new_dedup();
    let one = dedup.lit(1);
    dedup.add(&[one]);
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            dedup.add(&[one, ExprId(usize::MAX)]);
        }))
        .is_err()
    );
    assert!(matches!(
        dedup.alloc_expr_expr(&[]),
        Variadic::Span {
            start: 1,
            len: 0,
            ..
        }
    ));
}

proptest! {
    #[test]
    fn wide_smart_constructor_dedup_is_content_based(
        indices in prop::collection::vec(0usize..16, 0..64),
    ) {
        let mut store = VStore::new_dedup();
        let leaves: Vec<_> = (0..16).map(|value| store.lit(value)).collect();
        let children: Vec<_> = indices.iter().map(|&index| leaves[index]).collect();

        let first = store.add(&children);
        let duplicate = store.add(&children);

        prop_assert_eq!(first, duplicate);
        let pool_end = match store.alloc_expr_expr(&[]) {
            Variadic::Span { start, len: 0, .. } => start,
            _ => unreachable!("allocator must return an empty pool span"),
        };
        prop_assert_eq!(pool_end, children.len());
        let stored = match store.get_expr_resolved(first) {
            ExprNodeResolved::Add(stored) => stored,
            _ => unreachable!("smart constructor must build an Add node"),
        };
        prop_assert_eq!(stored.as_slice(), children);
    }
}

rec_family! {
    #[smart_constructors]
    family Composite => CompositeStore;
    enum CompositeRoot {
        Bundle(
            String,
            CompositeItem,
            Variadic<CompositeItem>,
            f64,
            Variadic<CompositeItem>,
        ),
    }
    enum CompositeItem { Atom(u32) }
}

#[test]
fn borrowed_candidate_matches_generic_hash_and_all_field_kinds() {
    let mut store = CompositeStore::new_dedup();
    let one = store.atom(1);
    let two = store.atom(2);
    let three = store.atom(3);
    let nan = f64::from_bits(0x7ff8_0000_0000_0001);
    let left = store.alloc_compositeroot_compositeitem(&[one, two]);
    let right = store.alloc_compositeroot_compositeitem(&[three]);
    let generic = store.push_compositeroot(CompositeRootNode::Bundle(
        "bundle".into(),
        one,
        left,
        nan,
        right,
    ));

    let smart = store.bundle("bundle", one, &[one, two], nan, &[three]);
    assert_eq!(smart, generic);
    assert!(matches!(
        store.alloc_compositeroot_compositeitem(&[]),
        Variadic::Span {
            start: 3,
            len: 0,
            ..
        }
    ));

    let other_nan = f64::from_bits(0x7ff8_0000_0000_0002);
    let distinct = store.bundle("bundle", one, &[one, two], other_nan, &[three]);
    assert_ne!(distinct, generic);
    assert_eq!(
        distinct,
        store.bundle("bundle", one, &[one, two], other_nan, &[three])
    );
}

#[test]
fn mixed_constructor_validates_every_slice_before_allocating_any_span() {
    let mut store = CompositeStore::new();
    let one = store.atom(1);

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            store.bundle("bundle", one, &[one], 0.0, &[CompositeItemId(usize::MAX)]);
        }))
        .is_err()
    );
    assert!(matches!(
        store.alloc_compositeroot_compositeitem(&[]),
        Variadic::Span {
            start: 0,
            len: 0,
            ..
        }
    ));
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
        ExprNodeResolved::Add(values)
            if values.as_slice() == [one, two]
    ));
    let mapped = store.map_expr_children(sum, &mut |id: &ExprId| id.0);
    assert!(matches!(
        mapped,
        ExprNodeMapped::Add(values)
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
fn resolved_getters_expose_only_total_variadic_operations() {
    let mut store = VStore::new();
    let one = store.lit(1);
    let two = store.lit(2);
    let sum = store.add(&[one, two]);

    let resolved: ExprNodeResolved = store.get_expr_resolved(sum);
    let children = match resolved {
        ExprNodeResolved::Add(children) => children,
        _ => panic!("expected an add node"),
    };

    assert_eq!(children.as_slice(), [one, two]);
    assert_eq!(children[0], one);
    assert_eq!(children.iter().copied().collect::<Vec<_>>(), [one, two]);
    assert_eq!(children.clone().into_iter().collect::<Vec<_>>(), [one, two]);
    assert_eq!(
        children.clone().map_all(&mut |child| child.0).into_vec(),
        [one.0, two.0]
    );

    store.set_expr(sum, ExprNodeResolved::Add(children));
    assert_eq!(eval(&store, sum), 3);
}

#[test]
fn variadic_rewrite_callbacks_receive_total_resolved_nodes() {
    let mut store = VStore::new();
    let one = store.lit(1);
    let two = store.lit(2);
    let sum = store.add(&[one, two]);
    let root = VStoreRoot::Expr(sum);

    let (transformed, transformed_root) = store.transform(
        root,
        |node: RootNodeResolved| node,
        |node: ExprNodeResolved| {
            if let ExprNodeResolved::Add(children) = &node {
                assert_eq!(children[1], two);
            }
            node
        },
    );
    assert_eq!(
        eval(&transformed, unwrap_expr(transformed_root)),
        eval(&store, sum)
    );

    let (rewritten, rewritten_root) = store.rewrite(
        root,
        |node: RootNodeResolved, out| out.push_root(node),
        |node: ExprNodeResolved, out| out.push_expr(node),
    );
    assert_eq!(
        eval(&rewritten, unwrap_expr(rewritten_root)),
        eval(&store, sum)
    );

    let (top_down, top_down_root) = store.rewrite_down(
        root,
        |node: RootNodeResolved| node,
        |node: ExprNodeResolved| {
            if let ExprNodeResolved::Add(children) = &node {
                assert_eq!(children.iter().count(), 2);
            }
            node
        },
    );
    assert_eq!(
        eval(&top_down, unwrap_expr(top_down_root)),
        eval(&store, sum)
    );

    let observed = store
        .fold_with_original(
            root,
            |_: &RootNodeResolved, _: RootNodeMapped<usize>| 0,
            |original: &ExprNodeResolved, _: ExprNodeMapped<usize>| match original {
                ExprNodeResolved::Add(children) => children.len(),
                _ => 0,
            },
        )
        .unwrap_expr();
    assert_eq!(observed, 2);
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
                RootNodeResolved::Program(xs) => xs.iter().count(),
            },
            |original, mapped: ExprNodeMapped<usize>| match (original, mapped) {
                (ExprNodeResolved::Add(xs), ExprNodeMapped::Add(_)) => xs.iter().count(),
                _ => 0,
            },
        )
        .unwrap_expr();
    assert_eq!(original_count, 3);

    let (rewritten, rewritten_root) = store.rewrite(
        root,
        |node, out| out.push_root(node),
        |node, out| match node {
            ExprNodeResolved::Lit(n) => out.push_expr(ExprNodeResolved::Lit(n * 2)),
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
            ExprNodeResolved::Lit(n) => ExprNodeResolved::Lit(n + 1),
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
            if let ExprNodeResolved::Add(xs) = &node {
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
