// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Acceptance tests for the abstract-value pool and frozen W8 contract in
//! `doc/design/21-abstract-value-pool.md`. Entries are opaque `u64` values.

use semi_persistent_containers_verus::HotFirst;
use semi_persistent_containers_verus::dense_id::{DenseId31, DenseId63};
use semi_persistent_containers_verus::eclasses::EClasses;
use semi_persistent_containers_verus::group::{ForkHistory, Member};
use semi_persistent_containers_verus::index_like::IndexLike;
use semi_persistent_containers_verus::opt::DenseId;
use semi_persistent_containers_verus::union_find::NoJust;
use semi_persistent_containers_verus::vec::ShrinkPolicy;

semi_persistent_containers_verus::define_id31! {
    pub struct EClassKey31 / StoredEClassKey31, "ec";
}
semi_persistent_containers_verus::define_id63! {
    pub struct EClassKey63 / StoredEClassKey63, "ec64";
}

type EC =
    EClasses<DenseId31, EClassKey31, DenseId31, DenseId31, NoJust, true, false, HotFirst, u64>;
type EC64 =
    EClasses<DenseId63, EClassKey63, DenseId63, DenseId63, NoJust, true, false, HotFirst, u64>;

#[test]
fn set_value_reads_back() {
    let mut ec = EC::new();
    let (_, key) = ec.try_add_singleton();
    assert_eq!(ec.abs_handle(key), None);
    assert_eq!(ec.abs_value(key), None);
    assert_eq!(ec.abs_value_at(None), None);
    ec.set_abs_value(key, 7);
    let handle = ec.abs_handle(key).expect("first write allocates");
    assert_eq!(handle.as_usize(), 0);
    assert_eq!(ec.abs_value(key), Some(7));
    assert_eq!(ec.abs_value_at(Some(handle)), Some(7));
    ec.set_abs_value(key, 9);
    assert_eq!(ec.abs_handle(key), Some(handle));
    assert_eq!(ec.abs_value(key), Some(9));
    assert_eq!(ec.abs_value_at(Some(handle)), Some(9));
    let (_, next) = ec.try_add_singleton();
    ec.set_abs_value(next, 11);
    assert_eq!(ec.abs_handle(next).unwrap().as_usize(), 1);
}

#[test]
fn live_handles_are_distinct() {
    let mut ec = EC::new();
    let (_, ka) = ec.try_add_singleton();
    let (_, kb) = ec.try_add_singleton();
    let (_, kc) = ec.try_add_singleton();
    ec.set_abs_value(ka, 1);
    ec.set_abs_value(kb, 2);
    ec.set_abs_value(kc, 3);
    let handles = [ka, kb, kc].map(|k| ec.abs_handle(k).unwrap());
    assert_ne!(handles[0], handles[1]);
    assert_ne!(handles[0], handles[2]);
    assert_ne!(handles[1], handles[2]);
    ec.set_abs_value(kb, 20);
    assert_eq!(
        [ka, kb, kc].map(|k| ec.abs_value(k)),
        [Some(1), Some(20), Some(3)]
    );
    assert_eq!([ka, kb, kc].map(|k| ec.abs_handle(k).unwrap()), handles);
    let (_, kd) = ec.try_add_singleton();
    assert_eq!(ec.abs_handle(kd), None);
    ec.set_abs_value(kd, 4);
    assert!(!handles.contains(&ec.abs_handle(kd).unwrap()));
    assert_eq!(
        [ka, kb, kc].map(|k| ec.abs_value(k)),
        [Some(1), Some(20), Some(3)]
    );
}

#[test]
fn merge_returns_absorbed_handle() {
    let mut ec = EC::new();
    let (a, ka) = ec.try_add_singleton();
    let (b, kb) = ec.try_add_singleton();
    ec.set_abs_value(ka, 10);
    ec.set_abs_value(kb, 20);
    let ha = ec.abs_handle(ka);
    let hb = ec.abs_handle(kb);
    let mi = ec.merge(a, b).expect("distinct classes merge");
    let (survivor_handle, absorbed_handle, survivor_value, absorbed_value) =
        if mi.survivor.to_usize() == a.to_usize() {
            (ha, hb, 10, 20)
        } else {
            (hb, ha, 20, 10)
        };
    let key = ec.repr_id(mi.survivor).unwrap();
    assert_eq!(ec.abs_handle(key), survivor_handle);
    assert_eq!(ec.abs_value(key), Some(survivor_value));
    assert_eq!(mi.absorbed_abs, absorbed_handle);
    assert_eq!(ec.abs_value_at(mi.absorbed_abs), Some(absorbed_value));
    ec.set_abs_value(key, 30);
    assert_eq!(ec.abs_handle(key), survivor_handle);
    assert_eq!(ec.abs_value(key), Some(30));
    assert_eq!(ec.abs_value_at(mi.absorbed_abs), Some(absorbed_value));
}

#[test]
fn merge_without_values_returns_none() {
    let mut ec = EC::new();
    let (a, _) = ec.try_add_singleton();
    let (b, _) = ec.try_add_singleton();
    let mi = ec.merge(a, b).unwrap();
    assert_eq!(mi.absorbed_abs, None);
    assert_eq!(ec.abs_value_at(mi.absorbed_abs), None);
    let key = ec.repr_id(mi.survivor).unwrap();
    assert_eq!(ec.abs_handle(key), None);
    assert_eq!(ec.abs_value(key), None);
}

#[test]
fn restore_rolls_back_value_write() {
    let mut ec = ForkHistory::new(EC::new());
    let (_, key) = ec.try_add_singleton();
    ec.set_abs_value(key, 1);
    let handle = ec.abs_handle(key);
    let token = ec.mark(ShrinkPolicy::Never).expect("bounded mark depth");
    ec.set_abs_value(key, 2);
    assert_eq!(ec.abs_value(key), Some(2));
    assert!(ec.restore(token));
    assert_eq!(ec.abs_handle(key), handle);
    assert_eq!(ec.abs_value(key), Some(1));
    assert_eq!(ec.abs_value_at(handle), Some(1));
}

#[test]
fn restore_rolls_back_merge_and_combined_value() {
    let mut ec = ForkHistory::new(EC::new());
    let (a, ka) = ec.try_add_singleton();
    let (b, kb) = ec.try_add_singleton();
    ec.set_abs_value(ka, 10);
    ec.set_abs_value(kb, 20);
    let handles = [ec.abs_handle(ka), ec.abs_handle(kb)];
    let token = ec.mark(ShrinkPolicy::Never).expect("bounded mark depth");
    let mi = ec.merge(a, b).unwrap();
    let key = ec.repr_id(mi.survivor).unwrap();
    ec.set_abs_value(key, 30);
    assert_eq!(ec.abs_value(key), Some(30));
    assert!(ec.restore(token));
    assert_eq!(ec.num_classes().as_usize(), 2);
    assert_eq!(ec.repr_id(a), Some(ka));
    assert_eq!(ec.repr_id(b), Some(kb));
    assert_eq!([ec.abs_handle(ka), ec.abs_handle(kb)], handles);
    assert_eq!([ec.abs_value(ka), ec.abs_value(kb)], [Some(10), Some(20)]);
}

#[test]
fn restore_drops_entries_allocated_after_mark() {
    let mut ec = ForkHistory::new(EC::new());
    let (_, ka) = ec.try_add_singleton();
    let token = ec.mark(ShrinkPolicy::Never).expect("bounded mark depth");
    ec.set_abs_value(ka, 5);
    let handle = ec.abs_handle(ka);
    let (_, kb) = ec.try_add_singleton();
    ec.set_abs_value(kb, 6);
    let second = ec.abs_handle(kb);
    assert!(ec.restore(token));
    assert_eq!(ec.len().as_usize(), 1);
    assert_eq!(ec.num_classes().as_usize(), 1);
    assert_eq!(ec.abs_handle(ka), None);
    assert_eq!(ec.abs_value(ka), None);
    // Both tail entries are unallocated now, before any index can be reused.
    for h in [handle, second] {
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| { ec.abs_value_at(h) }))
                .is_err()
        );
    }
    ec.set_abs_value(ka, 7);
    assert_eq!(
        ec.abs_handle(ka),
        handle,
        "the truncated tail index is reused"
    );
    assert_eq!(ec.abs_value(ka), Some(7));
    assert_eq!(ec.abs_value_at(handle), Some(7));
}

#[test]
fn nested_marks_restore_values_in_order() {
    let mut ec = ForkHistory::new(EC::new());
    let (_, key) = ec.try_add_singleton();
    ec.set_abs_value(key, 1);
    let handle = ec.abs_handle(key);
    let t1 = ec.mark(ShrinkPolicy::Never).expect("bounded mark depth");
    ec.set_abs_value(key, 2);
    let t2 = ec.mark(ShrinkPolicy::Never).expect("bounded mark depth");
    ec.set_abs_value(key, 3);
    assert!(ec.restore(t2));
    assert_eq!(ec.abs_value(key), Some(2));
    assert_eq!(ec.abs_handle(key), handle);
    assert!(ec.restore(t1));
    assert_eq!(ec.abs_value(key), Some(1));
    assert_eq!(ec.abs_handle(key), handle);
    assert!(!ec.restore(t2), "outer restore invalidates the inner token");
    ec.set_abs_value(key, 4);
    assert!(ec.restore(t1), "ForkHistory restore retains the checkpoint");
    assert_eq!(ec.abs_value(key), Some(1));
    assert_eq!(ec.abs_handle(key), handle);
    assert!(ec.pop_scope());
    assert!(!ec.restore(t1), "pop consumes the checkpoint");
}

#[test]
fn reset_retains_frame_restore_consumes_frame() {
    let mut ec = EC::new();
    let (_, ka) = ec.try_add_singleton();
    let (_, kb) = ec.try_add_singleton();
    ec.set_abs_value(ka, 1);
    let ha = ec.abs_handle(ka);
    ec.push_frame(ShrinkPolicy::Never); // frame 0: a=1, b absent
    ec.set_abs_value(ka, 2);
    ec.set_abs_value(kb, 20);
    let hb = ec.abs_handle(kb);
    ec.push_frame(ShrinkPolicy::Never); // frame 1: a=2, b=20
    ec.set_abs_value(ka, 3);
    ec.set_abs_value(kb, 30);
    // Public Member methods delegate to the C6 frame operations.
    ec.reset_frame(1);
    assert_eq!(ec.depth_exec(), 2);
    assert_eq!([ec.abs_value(ka), ec.abs_value(kb)], [Some(2), Some(20)]);
    assert_eq!([ec.abs_handle(ka), ec.abs_handle(kb)], [ha, hb]);
    ec.set_abs_value(ka, 4);
    ec.restore_frame(1);
    assert_eq!(ec.depth_exec(), 1);
    assert_eq!([ec.abs_value(ka), ec.abs_value(kb)], [Some(2), Some(20)]);
    assert_eq!([ec.abs_handle(ka), ec.abs_handle(kb)], [ha, hb]);
    ec.reset_frame(0);
    assert_eq!(ec.depth_exec(), 1);
    assert_eq!([ec.abs_value(ka), ec.abs_value(kb)], [Some(1), None]);
    assert_eq!([ec.abs_handle(ka), ec.abs_handle(kb)], [ha, None]);
    ec.set_abs_value(ka, 5);
    ec.set_abs_value(kb, 50);
    ec.restore_frame(0);
    assert_eq!(ec.depth_exec(), 0);
    assert_eq!([ec.abs_value(ka), ec.abs_value(kb)], [Some(1), None]);
    assert_eq!([ec.abs_handle(ka), ec.abs_handle(kb)], [ha, None]);
}

fn merged_with_dead_key() -> (EC, EClassKey31) {
    let mut ec = EC::new();
    let (a, ka) = ec.try_add_singleton();
    let (b, kb) = ec.try_add_singleton();
    ec.set_abs_value(ka, 10);
    ec.set_abs_value(kb, 20);
    let mi = ec.merge_directed_with(a, b, true).unwrap();
    assert_eq!(mi.absorbed.to_usize(), b.to_usize());
    (ec, kb)
}

#[test]
#[should_panic(expected = "class key is not live")]
fn dead_key_write_refuses() {
    let (mut ec, key) = merged_with_dead_key();
    ec.set_abs_value(key, 99);
}

#[test]
#[should_panic(expected = "class key is not live")]
fn dead_key_value_read_refuses() {
    let (ec, key) = merged_with_dead_key();
    ec.abs_value(key);
}

#[test]
#[should_panic(expected = "class key is not live")]
fn dead_key_handle_read_refuses() {
    let (ec, key) = merged_with_dead_key();
    ec.abs_handle(key);
}

#[test]
#[should_panic(expected = "handle is not allocated")]
fn unallocated_handle_refuses() {
    let mut ec = EC::new();
    let (_, key) = ec.try_add_singleton();
    ec.set_abs_value(key, 7);
    let next = <DenseId31 as DenseId>::Index::try_from_usize(1).unwrap();
    ec.abs_value_at(Some(next));
}

#[test]
fn bits63_value_round_trip() {
    let mut ec = ForkHistory::new(EC64::new());
    let (a, ka) = ec.try_add_singleton();
    let (b, kb) = ec.try_add_singleton();
    assert_eq!(ec.abs_value(ka), None);
    ec.set_abs_value(ka, u64::MAX);
    ec.set_abs_value(kb, 20);
    let ha = ec.abs_handle(ka);
    let hb = ec.abs_handle(kb);
    assert_ne!(ha, hb);
    let token = ec.mark(ShrinkPolicy::Never).expect("bounded mark depth");
    let mi = ec.merge_directed_with(a, b, true).unwrap();
    assert_eq!(mi.absorbed_abs, hb);
    assert_eq!(ec.abs_value_at(hb), Some(20));
    assert_eq!(ec.abs_handle(ka), ha);
    ec.set_abs_value(ka, 30);
    assert_eq!(ec.abs_handle(ka), ha);
    assert_eq!(ec.abs_value(ka), Some(30));
    assert_eq!(ec.abs_value_at(hb), Some(20));
    assert!(ec.restore(token));
    assert_eq!(ec.num_classes().as_usize(), 2);
    assert_eq!(ec.repr_id(a), Some(ka));
    assert_eq!(ec.repr_id(b), Some(kb));
    assert_eq!([ec.abs_handle(ka), ec.abs_handle(kb)], [ha, hb]);
    assert_eq!(
        [ec.abs_value(ka), ec.abs_value(kb)],
        [Some(u64::MAX), Some(20)]
    );
}
