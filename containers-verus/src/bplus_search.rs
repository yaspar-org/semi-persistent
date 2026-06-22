// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `SearchKind`: the pluggable in-node key search, matching production's
//! `SearchKind` trait (`find_ge` / `find_gt`).
//!
//! Production is generic over `W: Copy + Ord` and searches a slice with
//! `partition_point`. In the verified model the words are
//! [`IndexLike`](crate::index_like), whose total order is `lt_spec`/`le_spec`
//! (definitionally the `as_nat` order). The contract is stated over `as_nat`,
//! and the binary-search loops reason there too — transitivity and totality are
//! free on `nat`. The only glue is `IndexLike::lemma_order_is_as_nat`, which
//! bridges the exec comparisons (`lt`/`le`, whose `ensures` speak `lt_spec`/
//! `le_spec`) to `as_nat`; Verus cannot unfold the `open` default order bodies
//! through a generic type parameter, so that lemma is supplied by the trait.
//!
//!   - `find_ge(keys, t)` = first index `i` with `keys[i] >= t` (so `[0, i)` are
//!     `< t`); production's `partition_point(|k| k < t)`.
//!   - `find_gt(keys, t)` = first index `i` with `keys[i] > t` (so `[0, i)` are
//!     `<= t`); production's `partition_point(|k| k <= t)`.
//!
//! Both require the slice sorted by `as_nat`. The result is a boundary index in
//! `[0, len]`; the tree uses `find_ge` for membership and `find_gt` to pick an
//! internal child during descent. `BinarySearch` is the verified `O(log n)`
//! impl (production's default); any `SearchKind` is substitutable.

use vstd::prelude::*;

use crate::index_like::IndexLike;

verus! {

/// A slice of words is non-strictly sorted by `as_nat`.
pub open spec fn sorted_le<W: IndexLike>(s: Seq<W>) -> bool {
    forall|i: int, j: int|
        0 <= i <= j < s.len() ==> (#[trigger] s[i].as_nat()) <= (#[trigger] s[j].as_nat())
}

/// Instantiate `sorted_le` at a concrete pair (a `proof fn` so callers get the
/// fact without fighting the quantifier trigger inside a loop body).
pub proof fn lemma_sorted_le_at<W: IndexLike>(s: Seq<W>, i: int, j: int)
    requires sorted_le(s), 0 <= i <= j < s.len(),
    ensures s[i].as_nat() <= s[j].as_nat(),
{
}

/// Pluggable in-node search. Mirrors production's `SearchKind`; the contract is
/// stated over the `as_nat` order so any impl is interchangeable.
pub trait SearchKind {
    /// First index `i` with `keys[i] >= target` (everything before is `<`).
    fn find_ge<W: IndexLike>(keys: &[W], target: W) -> (r: usize)
        requires sorted_le(keys@),
        ensures
            r <= keys.len(),
            forall|i: int| 0 <= i < r ==> (#[trigger] keys@[i].as_nat()) < target.as_nat(),
            forall|i: int| r <= i < keys.len() ==> target.as_nat() <= (#[trigger] keys@[i].as_nat());

    /// First index `i` with `keys[i] > target` (everything before is `<=`).
    fn find_gt<W: IndexLike>(keys: &[W], target: W) -> (r: usize)
        requires sorted_le(keys@),
        ensures
            r <= keys.len(),
            forall|i: int| 0 <= i < r ==> (#[trigger] keys@[i].as_nat()) <= target.as_nat(),
            forall|i: int| r <= i < keys.len() ==> target.as_nat() < (#[trigger] keys@[i].as_nat());
}

/// Branched binary search (production's default `BinarySearch`).
pub struct BinarySearch;

impl SearchKind for BinarySearch {
    fn find_ge<W: IndexLike>(keys: &[W], target: W) -> (r: usize) {
        let n = keys.len();
        let mut lo: usize = 0;
        let mut hi: usize = n;
        while lo < hi
            invariant
                lo <= hi <= n,
                n == keys.len(),
                sorted_le(keys@),
                forall|i: int| 0 <= i < lo ==> (#[trigger] keys@[i].as_nat()) < target.as_nat(),
                forall|i: int| hi <= i < n ==> target.as_nat() <= (#[trigger] keys@[i].as_nat()),
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            let km = keys[mid];
            assert(km == keys@[mid as int]);
            let is_lt = km.lt(target);
            proof { W::lemma_order_is_as_nat(km, target); }  // is_lt == (km.as_nat() < target.as_nat())
            if is_lt {
                // every i <= mid: keys[i] <= km < target.
                assert forall|i: int| 0 <= i <= mid implies
                    (#[trigger] keys@[i].as_nat()) < target.as_nat() by {
                    lemma_sorted_le_at(keys@, i, mid as int);
                }
                lo = mid + 1;
            } else {
                // every i >= mid: target <= km <= keys[i].
                assert forall|i: int| mid <= i < n implies
                    target.as_nat() <= (#[trigger] keys@[i].as_nat()) by {
                    lemma_sorted_le_at(keys@, mid as int, i);
                }
                hi = mid;
            }
        }
        lo
    }

    fn find_gt<W: IndexLike>(keys: &[W], target: W) -> (r: usize) {
        let n = keys.len();
        let mut lo: usize = 0;
        let mut hi: usize = n;
        while lo < hi
            invariant
                lo <= hi <= n,
                n == keys.len(),
                sorted_le(keys@),
                forall|i: int| 0 <= i < lo ==> (#[trigger] keys@[i].as_nat()) <= target.as_nat(),
                forall|i: int| hi <= i < n ==> target.as_nat() < (#[trigger] keys@[i].as_nat()),
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            let km = keys[mid];
            assert(km == keys@[mid as int]);
            let is_le = km.le(target);
            proof { W::lemma_order_is_as_nat(km, target); }  // is_le == (km.as_nat() <= target.as_nat())
            if is_le {
                assert forall|i: int| 0 <= i <= mid implies
                    (#[trigger] keys@[i].as_nat()) <= target.as_nat() by {
                    lemma_sorted_le_at(keys@, i, mid as int);
                }
                lo = mid + 1;
            } else {
                assert forall|i: int| mid <= i < n implies
                    target.as_nat() < (#[trigger] keys@[i].as_nat()) by {
                    lemma_sorted_le_at(keys@, mid as int, i);
                }
                hi = mid;
            }
        }
        lo
    }
}

} // verus!
