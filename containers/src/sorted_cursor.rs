// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Shared cursor contract for sorted-set iteration.
//!
//! Implemented directly by `BPlusCursor` (this crate) and by
//! `SortedVecCursor` in downstream crates. No intermediate adapters.

/// Seek-and-step cursor over a sorted sequence of keys.
///
/// A valid cursor points at a key: `key()` returns `Some(k)`. An
/// exhausted cursor returns `None`. `seek(target)` advances the cursor
/// to the first key ≥ `target`, or exhausts it if no such key exists.
pub trait SortedCursor {
    type Key: Copy + Ord;

    /// Current key, or `None` if exhausted.
    fn key(&self) -> Option<Self::Key>;

    /// Advance one key. No-op on an exhausted cursor.
    fn step(&mut self);

    /// Advance to the first key ≥ `target`. Exhausts the cursor if no
    /// such key exists.
    fn seek(&mut self, target: Self::Key);
}
