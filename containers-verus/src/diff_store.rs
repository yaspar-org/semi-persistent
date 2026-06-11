// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `DiffStore`: the capture-protocol contract.
//!
//! A storage backend exposes two ghost views:
//!   - `data: Seq<T>`     — the abstract sequence of stored values
//!   - `captured: Seq<bool>` — per-slot "has been logged this frame" flag
//!
//! Plus a well-formedness predicate `wf()` that ties the two together
//! (e.g. equal lengths, plus any backend-specific invariants).
//!
//! The capture protocol — first-write-wins:
//!
//!   - `prepare_mark(saved_len, prev_diffs)` clears `captured[0..saved_len]`.
//!   - `set_raw(i, v)` overwrites `data[i]`; `captured` unchanged.
//!   - `capture(i, saved_len, log)` — if `i < saved_len && !captured[i]`,
//!       appends `(data[i], i)` to `log` and sets `captured[i] = true`;
//!       otherwise no-op.
//!   - `force_capture(i, saved_len, log)` — like `capture` but unconditional
//!       (within `i < saved_len`); used by `pop` to handle the about-to-vanish
//!       slot.
//!   - `restore_entry(i, old, target_saved_len)` rewinds `data[i] := old` for
//!     `i < target_saved_len` (and `i <= data.len()` because of the pre-pad
//!     pushed by previous `restore_entry` calls in the same loop).
//!   - `finish_restore(diffs, saved_len)` rebuilds `captured` from the
//!     surviving diff suffix.
//!
//! `Vec`'s proof talks only to this contract, so it's parametric in storage.

use vstd::prelude::*;

use crate::index_like::IndexLike;

verus! {

/// Storage backend for the semi-persistent vector.
///
/// Diff entries are `(T, I)` pairs (old value, index). Methods take exec
/// slices/`Vec`s; their `@` views are the spec-level `Seq` we reason about.
pub trait DiffStore<T, I, const TRACK: bool>: Sized
where
    T: Sized + Copy,
    I: IndexLike,
{
    // -- ghost views ---------------------------------------------------------

    /// The abstract sequence of stored values. Tag-bit edits in concrete impls
    /// project out: `data()` is invariant under `set_tag`/`clear_tag` on the
    /// underlying repr.
    spec fn data(&self) -> Seq<T>;

    /// Per-slot capture flag for the active frame. Length matches `data()`.
    spec fn captured(&self) -> Seq<bool>;

    /// Backend-specific well-formedness. Concrete impls strengthen this; the
    /// universal part is `captured().len() == data().len()`.
    spec fn wf(&self) -> bool;

    /// Universal consequence of `wf`: the capture-flag sequence is exactly
    /// as long as the data sequence. Both backends discharge this trivially.
    proof fn lemma_wf_captured_len(&self)
        requires self.wf(),
        ensures self.captured().len() == self.data().len();

    // -- raw read / write API ------------------------------------------------

    fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.data().len() == 0);

    fn len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.data().len();

    fn get(&self, i: I) -> (v: T)
        requires
            self.wf(),
            i.as_nat() < self.data().len(),
        ensures v == self.data()[i.as_nat() as int];

    fn push(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).data().len() + 1 < I::max_nat(),
        ensures
            self.wf(),
            self.data() == old(self).data().push(value),
            self.captured() == old(self).captured().push(false);

    fn pop(&mut self) -> (r: Option<T>)
        requires old(self).wf(),
        ensures
            self.wf(),
            old(self).data().len() == 0 ==> {
                &&& r is None
                &&& self.data() == old(self).data()
                &&& self.captured() == old(self).captured()
            },
            old(self).data().len() > 0 ==> {
                &&& r is Some
                &&& r->Some_0 == old(self).data()[old(self).data().len() - 1]
                &&& self.data() == old(self).data().drop_last()
                &&& self.captured() == old(self).captured().drop_last()
            };

    fn set_raw(&mut self, i: I, value: T)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            self.wf(),
            self.data() == old(self).data().update(i.as_nat() as int, value),
            self.captured() == old(self).captured();

    fn truncate(&mut self, len: I)
        requires
            old(self).wf(),
            len.as_nat() <= old(self).data().len(),
        ensures
            self.wf(),
            self.data() == old(self).data().subrange(0, len.as_nat() as int),
            self.captured() == old(self).captured().subrange(0, len.as_nat() as int);

    /// Mark slot `i` as captured without logging or changing `data`. Used by
    /// `Vec::push` when a previously-popped marked index is re-added: the
    /// pop already captured `snap[i]`, so the fresh slot must inherit the
    /// captured flag to keep first-write-wins (and bound the diff log).
    fn mark_captured(&mut self, i: I)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            self.wf(),
            self.data() == old(self).data(),
            self.captured() == old(self).captured().update(i.as_nat() as int, true);

    /// Resize `data` to `len`: truncate if longer, or extend with
    /// `T::default()` fillers if shorter. Used by `restore` to regrow the
    /// popped region before the overwrite-only replay. The filler values are
    /// arbitrary — they are always overwritten by the replay, which is why
    /// no constraint is placed on `T::default()`. New slots are uncaptured.
    fn resize_default(&mut self, len: I)
        where T: core::default::Default
        requires
            old(self).wf(),
            len.as_nat() < I::max_nat(),
        ensures
            self.wf(),
            self.data().len() == len.as_nat(),
            // existing prefix preserved
            forall|j: int| 0 <= j < len.as_nat() && j < old(self).data().len()
                ==> #[trigger] self.data()[j] == old(self).data()[j],
            self.captured().len() == len.as_nat();

    // -- capture protocol ----------------------------------------------------

    /// Begin a new frame. Clears the capture flag for all slots in
    /// `[0, saved_len)`. The `prev_diffs` slice is the diff log of the
    /// outer (parent) frame, used by `InlineStore` to know which inline
    /// tags need clearing; `ParallelStore` ignores it.
    fn prepare_mark(&mut self, saved_len: I, prev_diffs: &[(T, I)])
        requires
            old(self).wf(),
            saved_len.as_nat() <= old(self).data().len(),
        ensures
            self.wf(),
            self.data() == old(self).data(),
            forall|i: int| 0 <= i < saved_len.as_nat() ==>
                #[trigger] self.captured()[i] == false;

    /// First-write-wins capture. If the slot is in-frame and not yet captured,
    /// log `(old.data()[i], i)` and flip `captured[i]`.
    fn capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            self.wf(),
            self.data() == old(self).data(),
            // First-write-wins:
            (i.as_nat() < saved_len.as_nat() && !old(self).captured()[i.as_nat() as int])
                ==> {
                    &&& diff_log@ == old(diff_log)@.push(
                            (old(self).data()[i.as_nat() as int], i))
                    &&& self.captured()[i.as_nat() as int] == true
                    &&& forall|j: int| 0 <= j < self.captured().len() && j != i.as_nat()
                            ==> #[trigger] self.captured()[j] == old(self).captured()[j]
                },
            // Already captured, or out of frame: no-op.
            !(i.as_nat() < saved_len.as_nat() && !old(self).captured()[i.as_nat() as int])
                ==> {
                    &&& diff_log@ == old(diff_log)@
                    &&& self.captured() == old(self).captured()
                };

    /// Unconditional capture (used by `pop` so the about-to-vanish slot is
    /// always logged). Within-frame: log + set captured. Out-of-frame: no-op.
    fn force_capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            self.wf(),
            self.data() == old(self).data(),
            i.as_nat() < saved_len.as_nat() ==> {
                &&& diff_log@ == old(diff_log)@.push(
                        (old(self).data()[i.as_nat() as int], i))
                &&& self.captured()[i.as_nat() as int] == true
                &&& forall|j: int| 0 <= j < self.captured().len() && j != i.as_nat()
                        ==> #[trigger] self.captured()[j] == old(self).captured()[j]
            },
            i.as_nat() >= saved_len.as_nat() ==> {
                &&& diff_log@ == old(diff_log)@
                &&& self.captured() == old(self).captured()
            };

    /// Rewind a single slot to `old_value`. Within `[0, target_saved_len)`,
    /// either overwrites the existing slot (`index < data.len()`) or pushes
    /// (`index == data.len()`); above `target_saved_len`, no-op.
    ///
    /// The push case handles the pop+restore cycle: when restore truncates
    /// then replays diffs, popped slots reappear via `restore_entry`.
    fn restore_entry(&mut self, index: I, old_value: &T, target_saved_len: I)
        requires
            old(self).wf(),
            index.as_nat() < target_saved_len.as_nat() ==>
                index.as_nat() <= old(self).data().len(),
            // If we'd push, the new length must still fit in I.
            (index.as_nat() < target_saved_len.as_nat()
                && index.as_nat() == old(self).data().len())
                ==> old(self).data().len() + 1 < I::max_nat(),
        ensures
            self.wf(),
            // In-frame, in-bounds: overwrite.
            (index.as_nat() < target_saved_len.as_nat()
                && index.as_nat() < old(self).data().len())
                ==> self.data() ==
                    old(self).data().update(index.as_nat() as int, *old_value),
            // In-frame, at end: push.
            (index.as_nat() < target_saved_len.as_nat()
                && index.as_nat() == old(self).data().len())
                ==> self.data() == old(self).data().push(*old_value),
            // Out-of-frame: no-op on data.
            (index.as_nat() >= target_saved_len.as_nat())
                ==> self.data() == old(self).data();

    /// Rebuild `captured` from the surviving diff suffix. After restore, a
    /// slot is captured iff it appears in the parent frame's diff log.
    fn finish_restore(&mut self, current_frame_diffs: &[(T, I)], saved_len: I)
        requires
            old(self).wf(),
            saved_len.as_nat() <= old(self).data().len(),
        ensures
            self.wf(),
            self.data() == old(self).data(),
            // Within `[0, saved_len)`, captured iff some surviving diff entry
            // points at this index. Above `saved_len`, unspecified (those
            // slots are about to be truncated by `Vec::restore`).
            forall|i: int| 0 <= i < saved_len.as_nat() ==>
                #[trigger] self.captured()[i] == exists|k: int|
                    0 <= k < current_frame_diffs@.len()
                        && (#[trigger] current_frame_diffs@[k]).1.as_nat() == i;

    // -- maintenance ---------------------------------------------------------

    fn shrink_if(&mut self, factor: usize, headroom: usize)
        requires old(self).wf(),
        ensures
            self.wf(),
            self.data() == old(self).data(),
            self.captured() == old(self).captured();

    /// Heap bytes used by the backing storage (diagnostic; no spec content —
    /// it's a capacity measurement, not part of the semi-persistent contract).
    /// Default 0 for backends that don't introspect capacity.
    fn heap_bytes(&self) -> usize {
        0
    }
}

} // verus!
