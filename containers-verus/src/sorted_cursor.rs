// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `SortedCursor`: the shared seek-and-step cursor contract for sorted-set
//! iteration (production parity; the leapfrog-join surface).
//!
//! Implemented here by both verified cursors: `BPlusCursor` (tree-backed) and
//! `SortedVecCursor` (slice-backed). The trait itself is plain Rust (outside
//! `verus!{}`): it is the CONSUMER-facing abstraction — a trait object boundary
//! for leapfrog composition — and each impl is a 1-line delegation to the
//! VERIFIED inherent methods (`key`/`step`/`seek`). Trust ledger group E
//! (delegation glue).
//!
//! What the delegations stand on:
//!
//! | impl | seek soundness | in-order enumeration |
//! |---|---|---|
//! | `BPlusCursor` | `bplus::theorem_seek_never_skips` | `bplus::theorem_traversal_in_order` |
//! | `SortedVecCursor` | [`sorted_vec_cursor::theorem_seek_never_skips`](crate::sorted_vec_cursor::theorem_seek_never_skips) | [`sorted_vec_cursor::theorem_step_enumerates_tail`](crate::sorted_vec_cursor::theorem_step_enumerates_tail) |
//!
//! Both prove seek against the *same* spec function
//! (`bplus::seek_target_idx`), which is what makes them substitutable at this
//! boundary rather than merely similarly-shaped.
//!
//! One asymmetry the trait cannot express: `BPlusCursor::seek` is absolute
//! (`idx' == seek_target_idx(..)`) while `SortedVecCursor::seek` is forward-only
//! (`idx' == max(idx, seek_target_idx(..))`), matching production. Leapfrog only
//! ever seeks forward, so the two agree on every call it makes; a consumer that
//! seeks *backwards* through this trait would get different behavior from the
//! two impls, and the trait's contract — "advance to the first key ≥ target" —
//! is deliberately written to license only the forward-only reading.

use crate::bplus::BPlusCursor;
use crate::bplus_layout::NodeLayout;
use crate::bplus_search::SearchKind;
use crate::opt::DenseId;
use crate::sorted_vec_cursor::SortedVecCursor;

/// Seek-and-step cursor over a sorted sequence of keys.
///
/// A positioned cursor returns `Some(k)` from `key()`; an exhausted cursor
/// returns `None`. `seek(target)` advances to the first key ≥ `target`, or
/// exhausts. `step()` advances one key (no-op when exhausted).
pub trait SortedCursor {
    type Key: Copy + Ord;

    /// Current key, or `None` if exhausted.
    fn key(&self) -> Option<Self::Key>;

    /// Advance one key. No-op on an exhausted cursor.
    fn step(&mut self);

    /// Advance to the first key ≥ `target`. Exhausts the cursor if no such
    /// key exists.
    fn seek(&mut self, target: Self::Key);
}

impl<'a, K, L, S, const TRACK: bool> SortedCursor for BPlusCursor<'a, K, L, S, TRACK>
where
    K: DenseId + Copy + Ord,
    L: NodeLayout<Word = K::Index>,
    S: SearchKind,
{
    type Key = K;

    #[inline(always)]
    fn key(&self) -> Option<K> {
        BPlusCursor::key(self)
    }

    #[inline(always)]
    fn step(&mut self) {
        BPlusCursor::step(self)
    }

    #[inline(always)]
    fn seek(&mut self, target: K) {
        BPlusCursor::seek(self, target)
    }
}

impl<'a, K> SortedCursor for SortedVecCursor<'a, K>
where
    K: DenseId + Copy + Ord,
{
    type Key = K;

    /// The verified `key` has `idx() < model().len()` as a *precondition* rather
    /// than returning `Option`, because production's does (`data[pos]`, which
    /// panics past the end). The `is_valid` guard here is what discharges it, and
    /// it is the only thing these three bodies add over the `BPlusCursor` ones.
    #[inline(always)]
    fn key(&self) -> Option<K> {
        if SortedVecCursor::is_valid(self) {
            Some(SortedVecCursor::key(self))
        } else {
            None
        }
    }

    #[inline(always)]
    fn step(&mut self) {
        if SortedVecCursor::is_valid(self) {
            SortedVecCursor::step(self)
        }
    }

    #[inline(always)]
    fn seek(&mut self, target: K) {
        SortedVecCursor::seek(self, target)
    }
}
