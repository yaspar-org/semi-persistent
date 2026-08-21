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
//! Both are requires-free: on any input the result is a boundary index in
//! `[0, len]`, and the partition-point characterization holds under the
//! hypothesis `sorted_le(keys@)`, stated in the ensures as an implication.
//! The tree uses `find_ge` for membership and `find_gt` to pick an internal
//! child during descent; its nodes are proven sorted, so those call sites
//! discharge the hypothesis and keep the full contract. `BinarySearch` is the
//! verified `O(log n)` impl (production's default); any `SearchKind` is
//! substitutable.

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
    /// First index `i` with `keys[i] >= target` (everything before is `<`),
    /// under the hypothesis that `keys` is sorted. On any input the result is
    /// in `[0, keys.len()]`.
    fn find_ge<W: IndexLike>(keys: &[W], target: W) -> (r: usize)
        ensures
            r <= keys.len(),
            sorted_le(keys@) ==> forall|i: int|
                0 <= i < r ==> (#[trigger] keys@[i].as_nat()) < target.as_nat(),
            sorted_le(keys@) ==> forall|i: int|
                r <= i < keys.len() ==> target.as_nat() <= (#[trigger] keys@[i].as_nat());

    /// First index `i` with `keys[i] > target` (everything before is `<=`),
    /// under the hypothesis that `keys` is sorted. On any input the result is
    /// in `[0, keys.len()]`.
    fn find_gt<W: IndexLike>(keys: &[W], target: W) -> (r: usize)
        ensures
            r <= keys.len(),
            sorted_le(keys@) ==> forall|i: int|
                0 <= i < r ==> (#[trigger] keys@[i].as_nat()) <= target.as_nat(),
            sorted_le(keys@) ==> forall|i: int|
                r <= i < keys.len() ==> target.as_nat() < (#[trigger] keys@[i].as_nat());
}

/// Branched binary search (production's default `BinarySearch`).
pub struct BinarySearch;

impl SearchKind for BinarySearch {
    #[inline(always)]
    fn find_ge<W: IndexLike>(keys: &[W], target: W) -> (r: usize) {
        let n = keys.len();
        if n == 0 {
            return 0;
        }
        // `partition_point`'s shape, not the textbook `while lo < hi`: `size`
        // shrinks unconditionally so the trip count is `log2(n)` regardless of the
        // data, and the only data-dependent value — `base` — is chosen by
        // `sel_usize`, which is intended to lower to a branchless select. See
        // `bplus_layout::sel_usize`; current code-generation and performance
        // comparisons belong in the Criterion B+tree benchmark.
        let mut base: usize = 0;
        let mut size: usize = n;
        while size > 1
            invariant
                1 <= size,
                base + size <= n,
                n == keys.len(),
                sorted_le(keys@) ==> forall|i: int|
                    0 <= i < base ==> (#[trigger] keys@[i].as_nat()) < target.as_nat(),
                sorted_le(keys@) ==> forall|i: int|
                    base + size <= i < n ==> target.as_nat() <= (#[trigger] keys@[i].as_nat()),
            decreases size,
        {
            let half = size / 2;
            let mid = base + half;
            let km = keys[mid];
            assert(km == keys@[mid as int]);
            let is_lt = km.lt(target);
            // The case split lives INSIDE `proof` (rather than being an exec
            // `if`/`else` with a proof block per arm) so that clippy does not see
            // two exec branches that erase to the same empty block —
            // `clippy::if_same_then_else`. Same reason in `find_gt` and in
            // `bplus.rs`'s two bisections.
            //
            // The split-point facts hold only under the sortedness hypothesis;
            // the `if sorted_le` guard is what makes the conditional invariants
            // provable while the index arithmetic stays unconditional.
            proof {
                W::lemma_order_is_as_nat(km, target);  // is_lt == (km.as_nat() < target.as_nat())
                if sorted_le(keys@) {
                    if is_lt {
                        // every i <= mid: keys[i] <= km < target.
                        assert forall|i: int| 0 <= i < mid implies
                            (#[trigger] keys@[i].as_nat()) < target.as_nat() by {
                            lemma_sorted_le_at(keys@, i, mid as int);
                        }
                    } else {
                        // every i >= mid: target <= km <= keys[i].
                        assert forall|i: int| mid <= i < n implies
                            target.as_nat() <= (#[trigger] keys@[i].as_nat()) by {
                            lemma_sorted_le_at(keys@, mid as int, i);
                        }
                    }
                }
            }
            base = crate::bplus_layout::sel_usize(is_lt, base, mid);
            size = size - half;
        }
        let kb = keys[base];
        assert(kb == keys@[base as int]);
        let is_lt = kb.lt(target);
        proof {
            W::lemma_order_is_as_nat(kb, target);
            if sorted_le(keys@) {
                if is_lt {
                    assert forall|i: int| 0 <= i < base + 1 implies
                        (#[trigger] keys@[i].as_nat()) < target.as_nat() by {
                        lemma_sorted_le_at(keys@, i, base as int);
                    }
                } else {
                    assert forall|i: int| base <= i < n implies
                        target.as_nat() <= (#[trigger] keys@[i].as_nat()) by {
                        lemma_sorted_le_at(keys@, base as int, i);
                    }
                }
            }
        }
        // Tail step stays a plain `if`: it lowers to `adc` on the compare's own
        // flag, which is cheaper than forcing a `cmov` here.
        base + if is_lt { 1usize } else { 0usize }
    }

    #[inline(always)]
    fn find_gt<W: IndexLike>(keys: &[W], target: W) -> (r: usize) {
        let n = keys.len();
        if n == 0 {
            return 0;
        }
        // Same shape and same reason as `find_ge`'s, with the `<=` boundary.
        let mut base: usize = 0;
        let mut size: usize = n;
        while size > 1
            invariant
                1 <= size,
                base + size <= n,
                n == keys.len(),
                sorted_le(keys@) ==> forall|i: int|
                    0 <= i < base ==> (#[trigger] keys@[i].as_nat()) <= target.as_nat(),
                sorted_le(keys@) ==> forall|i: int|
                    base + size <= i < n ==> target.as_nat() < (#[trigger] keys@[i].as_nat()),
            decreases size,
        {
            let half = size / 2;
            let mid = base + half;
            let km = keys[mid];
            assert(km == keys@[mid as int]);
            let is_le = km.le(target);
            proof {
                W::lemma_order_is_as_nat(km, target);  // is_le == (km.as_nat() <= target.as_nat())
                if sorted_le(keys@) {
                    if is_le {
                        assert forall|i: int| 0 <= i < mid implies
                            (#[trigger] keys@[i].as_nat()) <= target.as_nat() by {
                            lemma_sorted_le_at(keys@, i, mid as int);
                        }
                    } else {
                        assert forall|i: int| mid <= i < n implies
                            target.as_nat() < (#[trigger] keys@[i].as_nat()) by {
                            lemma_sorted_le_at(keys@, mid as int, i);
                        }
                    }
                }
            }
            base = crate::bplus_layout::sel_usize(is_le, base, mid);
            size = size - half;
        }
        let kb = keys[base];
        assert(kb == keys@[base as int]);
        let is_le = kb.le(target);
        proof {
            W::lemma_order_is_as_nat(kb, target);
            if sorted_le(keys@) {
                if is_le {
                    assert forall|i: int| 0 <= i < base + 1 implies
                        (#[trigger] keys@[i].as_nat()) <= target.as_nat() by {
                        lemma_sorted_le_at(keys@, i, base as int);
                    }
                } else {
                    assert forall|i: int| base <= i < n implies
                        target.as_nat() < (#[trigger] keys@[i].as_nat()) by {
                        lemma_sorted_le_at(keys@, base as int, i);
                    }
                }
            }
        }
        base + if is_le { 1usize } else { 0usize }
    }
}

/// Linear count search (production's `Branchless`): counts keys strictly
/// below (`find_ge`) / at-or-below (`find_gt`) the target over the whole
/// slice. The loop body is branch-free, matching production's: each compare
/// widens to `0`/`1` and accumulates, so the only branch is the loop bound
/// (data-independent) and LLVM can vectorize the compare-accumulate. Same
/// contracts as `BinarySearch`.
pub struct Branchless;

impl SearchKind for Branchless {
    #[inline(always)]
    fn find_ge<W: IndexLike>(keys: &[W], target: W) -> (r: usize) {
        let n = keys.len();
        let mut count: usize = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == keys.len(),
                count <= i,
                // count == number of keys in [0, i) below target; sortedness
                // makes them exactly the PREFIX [0, count).
                sorted_le(keys@) ==> forall|j: int|
                    0 <= j < count ==> (#[trigger] keys@[j].as_nat()) < target.as_nat(),
                sorted_le(keys@) ==> forall|j: int|
                    count <= j < i ==> target.as_nat() <= (#[trigger] keys@[j].as_nat()),
            decreases n - i,
        {
            let ki = keys[i];
            assert(ki == keys@[i as int]);
            let is_lt = ki.lt(target);
            proof {
                W::lemma_order_is_as_nat(ki, target);
                if sorted_le(keys@) && is_lt {
                    // sorted: keys[i] < target forces every j <= i below
                    // target (keys[j] <= keys[i] < target)...
                    assert forall|j: int| 0 <= j <= i implies
                        (#[trigger] keys@[j].as_nat()) < target.as_nat() by {
                        lemma_sorted_le_at(keys@, j, i as int);
                    }
                    // ...and the invariant's upper arm makes [count, i) keys
                    // >= target, so that range must be empty: count == i.
                    if count < i {
                        assert(target.as_nat() <= keys@[count as int].as_nat());
                        assert(keys@[count as int].as_nat() < target.as_nat());
                        assert(false);
                    }
                }
            }
            // The accumulate must stay a cast-and-add, never `if is_lt { count
            // += 1 }`: a conditional here reintroduces the mispredicting branch
            // and defeats vectorization, which is this impl's entire point.
            count = count + (is_lt as usize);
            i = i + 1;
        }
        count
    }

    #[inline(always)]
    fn find_gt<W: IndexLike>(keys: &[W], target: W) -> (r: usize) {
        let n = keys.len();
        let mut count: usize = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == keys.len(),
                count <= i,
                sorted_le(keys@) ==> forall|j: int|
                    0 <= j < count ==> (#[trigger] keys@[j].as_nat()) <= target.as_nat(),
                sorted_le(keys@) ==> forall|j: int|
                    count <= j < i ==> target.as_nat() < (#[trigger] keys@[j].as_nat()),
            decreases n - i,
        {
            let ki = keys[i];
            assert(ki == keys@[i as int]);
            let is_le = ki.le(target);
            proof {
                W::lemma_order_is_as_nat(ki, target);
                if sorted_le(keys@) && is_le {
                    assert forall|j: int| 0 <= j <= i implies
                        (#[trigger] keys@[j].as_nat()) <= target.as_nat() by {
                        lemma_sorted_le_at(keys@, j, i as int);
                    }
                    if count < i {
                        assert(target.as_nat() < keys@[count as int].as_nat());
                        assert(keys@[count as int].as_nat() <= target.as_nat());
                        assert(false);
                    }
                }
            }
            // Cast-and-add, not a conditional: see `find_ge`.
            count = count + (is_le as usize);
            i = i + 1;
        }
        count
    }
}

} // verus!
