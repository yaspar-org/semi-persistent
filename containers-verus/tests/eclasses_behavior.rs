// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Behavioral tests of the verified `EClasses` aggregate: allocation, merge,
//! use-lists, the min-monomial pool, iteration, and mark/restore round trips
//! — plus the misuse surface (Err variants where the total API returns them,
//! refusal where the documented-panic arms fire).

use semi_persistent_containers_verus::dense_id::DenseId31;
use semi_persistent_containers_verus::eclasses::EClasses;
use semi_persistent_containers_verus::error::ContainerError;
use semi_persistent_containers_verus::index_like::IndexLike;
use semi_persistent_containers_verus::opt::DenseId;
use semi_persistent_containers_verus::vec::ShrinkPolicy;

type EC = EClasses<DenseId31, DenseId31, DenseId31, true>;

fn id(n: usize) -> DenseId31 {
    DenseId31::try_new(n).expect("test id in range")
}

#[test]
fn singletons_and_find() {
    let mut ec = EC::new();
    assert!(ec.is_empty());
    let (a, _ka) = ec.add_singleton();
    let (b, _kb) = ec.add_singleton();
    assert_eq!(a.to_usize(), 0);
    assert_eq!(b.to_usize(), 1);
    assert_eq!(ec.len().as_usize(), 2);
    assert_eq!(ec.num_classes().as_usize(), 2);
    assert_eq!(ec.find(a).to_usize(), 0);
    assert_eq!(ec.find_const(b).to_usize(), 1);
    // both are roots, both carry a live key.
    assert!(ec.repr_id(a).is_some());
    assert!(ec.repr_id(b).is_some());
}

#[test]
fn merge_absorbs_ring_and_key() {
    let mut ec = EC::new();
    let (a, _) = ec.add_singleton();
    let (b, _) = ec.add_singleton();
    let (c, _) = ec.add_singleton();
    let mi = ec.merge(a, b).expect("distinct classes merge");
    assert_eq!(ec.num_classes().as_usize(), 2);
    // one canonical root for both, and it is the survivor.
    let ra = ec.find(a);
    let rb = ec.find(b);
    assert_eq!(ra.to_usize(), rb.to_usize());
    assert_eq!(ra.to_usize(), mi.survivor.to_usize());
    // the absorbed id lost its key; the survivor kept one; c is untouched.
    assert!(ec.repr_id(mi.absorbed).is_none());
    assert!(ec.repr_id(mi.survivor).is_some());
    assert!(ec.repr_id(c).is_some());
    // re-merging the same class is a no-op.
    assert!(ec.merge(a, b).is_none());
    // the merged ring contains exactly a and b.
    let members: Vec<usize> = ec.iter_class(mi.survivor).collect_indices();
    assert_eq!(members.len(), 2);
    assert!(members.contains(&a.to_usize()) && members.contains(&b.to_usize()));
}

/// RingIter yields node ids; collect them as usizes through the iterator's
/// exec next.
trait CollectIndices {
    fn collect_indices(self) -> Vec<usize>;
}

impl<'a, const TRACK: bool> CollectIndices
    for semi_persistent_containers_verus::circular_list::RingIter<
        'a,
        semi_persistent_containers_verus::opt::Opt<DenseId31>,
        DenseId31,
        TRACK,
    >
{
    fn collect_indices(mut self) -> Vec<usize> {
        let mut out = Vec::new();
        while let Some(n) = self.next() {
            out.push(n.to_usize());
        }
        out
    }
}

#[test]
fn merge_directed_pins_survivor() {
    let mut ec = EC::new();
    let (a, _) = ec.add_singleton();
    let (b, _) = ec.add_singleton();
    let mi = ec.merge_directed(a, b, false).expect("merges");
    assert_eq!(mi.survivor.to_usize(), b.to_usize());
    assert_eq!(mi.absorbed.to_usize(), a.to_usize());
    assert_eq!(ec.find(a).to_usize(), b.to_usize());
}

#[test]
fn use_lists_append_and_splice() {
    let mut ec = EC::new();
    let (a, ka) = ec.add_singleton();
    let (b, kb) = ec.add_singleton();
    let (p, _) = ec.add_singleton(); // a "parent node"
    ec.add_use(ka, p);
    assert!(ec.atomic(ka));
    assert!(!ec.atomic(kb));
    let parents: Vec<usize> = ec.iter_uses(ka).map(|n| n.to_usize()).collect();
    assert_eq!(parents, vec![p.to_usize()]);
    // merge b into a's class, then splice b's (empty) use list onto a's.
    let mi = ec.merge_directed(a, b, true).expect("merges");
    let survivor_key = ec
        .repr_id(mi.survivor)
        .expect("survivor keeps its key");
    let survivor_list = ec.use_list_id(survivor_key);
    ec.splice_uses(survivor_list, mi.absorbed_uses);
    let parents_after: Vec<usize> = ec.iter_uses(survivor_key).map(|n| n.to_usize()).collect();
    assert_eq!(parents_after, vec![p.to_usize()]);
}

#[test]
fn min_pool_round_trip() {
    let mut ec = EC::new();
    let (a, ka) = ec.add_singleton();
    let (m, _) = ec.add_singleton(); // a monomial node id
    ec.set_min_width(3);
    assert_eq!(ec.min_width(), 3);
    assert_eq!(ec.min_monomial(ka, 1), None);
    ec.set_min_monomial(ka, 1, m);
    assert_eq!(ec.min_monomial(ka, 1).map(|n| n.to_usize()), Some(m.to_usize()));
    assert_eq!(ec.min_monomial(ka, 0), None);
    assert_eq!(ec.min_monomial(ka, 2), None);
    // a second class allocates its own row.
    let (_b, kb) = ec.add_singleton();
    ec.set_min_monomial(kb, 0, a);
    assert_eq!(ec.min_monomial(kb, 0).map(|n| n.to_usize()), Some(a.to_usize()));
    assert_eq!(ec.min_monomial(ka, 1).map(|n| n.to_usize()), Some(m.to_usize()));
}

#[test]
fn mark_restore_round_trip() {
    let mut ec = EC::new();
    let (a, _) = ec.add_singleton();
    let (b, _) = ec.add_singleton();
    let token = ec.mark(ShrinkPolicy::Never);
    // mutate: merge and allocate one more class.
    ec.merge(a, b).expect("merges");
    let (_c, _) = ec.add_singleton();
    assert_eq!(ec.len().as_usize(), 3);
    assert_eq!(ec.num_classes().as_usize(), 2);
    // restore: back to two singleton classes.
    ec.try_restore(token).expect("fresh token restores");
    assert_eq!(ec.len().as_usize(), 2);
    assert_eq!(ec.num_classes().as_usize(), 2);
    assert_ne!(ec.find(a).to_usize(), ec.find(b).to_usize());
    assert!(ec.repr_id(a).is_some() && ec.repr_id(b).is_some());
    // the token is consumed.
    assert_eq!(ec.try_restore(token).unwrap_err(), ContainerError::InvalidToken);
}

#[test]
fn nested_marks_restore_in_order() {
    let mut ec = EC::new();
    let (a, _) = ec.add_singleton();
    let (b, _) = ec.add_singleton();
    let (c, _) = ec.add_singleton();
    let t1 = ec.mark(ShrinkPolicy::Never);
    ec.merge(a, b);
    let t2 = ec.mark(ShrinkPolicy::Never);
    ec.merge(a, c);
    assert_eq!(ec.num_classes().as_usize(), 1);
    ec.try_restore(t2).expect("inner restores");
    assert_eq!(ec.num_classes().as_usize(), 2);
    assert_eq!(ec.find(a).to_usize(), ec.find(b).to_usize());
    assert_ne!(ec.find(a).to_usize(), ec.find(c).to_usize());
    ec.try_restore(t1).expect("outer restores");
    assert_eq!(ec.num_classes().as_usize(), 3);
    assert_ne!(ec.find(a).to_usize(), ec.find(b).to_usize());
}

#[test]
fn foreign_token_refuses_as_err() {
    let mut ec1 = EC::new();
    let mut ec2 = EC::new();
    let _ = ec1.add_singleton();
    let _ = ec2.add_singleton();
    let t1 = ec1.mark(ShrinkPolicy::Never);
    assert_eq!(ec2.try_restore(t1).unwrap_err(), ContainerError::InvalidToken);
}

#[test]
fn out_of_range_merge_panics() {
    let mut ec = EC::new();
    let (a, _) = ec.add_singleton();
    let bogus = id(41);
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = ec.merge(a, bogus);
    }));
    assert!(r.is_err(), "out-of-range id must refuse");
}

#[test]
fn dead_key_read_panics() {
    let mut ec = EC::new();
    let (a, _) = ec.add_singleton();
    let (b, kb) = ec.add_singleton();
    let mi = ec.merge_directed(a, b, true).expect("merges");
    assert_eq!(mi.absorbed.to_usize(), b.to_usize());
    // b's key is dead after the merge; reading through it refuses.
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = ec.atomic(kb);
    }));
    assert!(r.is_err(), "dead key must refuse");
}

#[test]
fn width_change_with_rows_panics() {
    let mut ec = EC::new();
    let (_a, ka) = ec.add_singleton();
    let (m, _) = ec.add_singleton();
    ec.set_min_width(2);
    ec.set_min_monomial(ka, 0, m);
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ec.set_min_width(3);
    }));
    assert!(r.is_err(), "width is frozen once rows exist");
}
