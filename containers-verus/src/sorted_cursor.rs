// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `SortedCursor`: the shared seek-and-step cursor contract for sorted-set
//! iteration (production parity; the leapfrog-join surface).
//!
//! Implemented by `BPlusCursor` here and by `SortedVecCursor` in downstream
//! crates. The trait itself is plain Rust (outside `verus!{}`): it is the
//! CONSUMER-facing abstraction — a trait object boundary for leapfrog
//! composition — and its impl for `BPlusCursor` is a 1-line delegation to the
//! VERIFIED inherent methods (`key`/`step`/`seek`), whose contracts prove
//! in-order enumeration (`theorem_traversal_in_order`) and seek soundness
//! (`theorem_seek_never_skips`). Trust ledger group E (delegation glue).

use crate::bplus::BPlusCursor;
use crate::bplus_layout::NodeLayout;
use crate::bplus_search::SearchKind;
use crate::opt::DenseId;

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
