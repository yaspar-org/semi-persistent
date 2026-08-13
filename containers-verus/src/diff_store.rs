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

    /// Untrapped element count, for the total shell's headroom queries
    /// (total-API plan phase 2): `len()` deliberately traps past the index
    /// word (the deferred overflow protocol), so a capacity check needs the
    /// usize truth without a trap.
    fn raw_len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.data().len();

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
            final(self).wf(),
            final(self).data() == old(self).data().push(value),
            // Flag maintenance is TRACK-conditional: an untracked store may
            // skip it wholesale (production parity — its flags are dead).
            TRACK ==> final(self).captured() == old(self).captured().push(false);

    fn pop(&mut self) -> (r: Option<T>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            old(self).data().len() == 0 ==> {
                &&& r is None
                &&& final(self).data() == old(self).data()
                &&& TRACK ==> final(self).captured() == old(self).captured()
            },
            old(self).data().len() > 0 ==> {
                &&& r is Some
                &&& r->Some_0 == old(self).data()[old(self).data().len() - 1]
                &&& final(self).data() == old(self).data().drop_last()
                &&& TRACK ==> final(self).captured() == old(self).captured().drop_last()
            };

    fn set_raw(&mut self, i: I, value: T)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            final(self).wf(),
            final(self).data() == old(self).data().update(i.as_nat() as int, value),
            // TRACK-conditional for the same reason as `push`/`pop` above, and
            // it is a PERFORMANCE contract, not just a modelling nicety.
            // Preserving an inline store's flag across a write costs a read and
            // a branch (read the old repr's tag, re-set it on the new one);
            // production spends that only when tracking is on
            // (`containers/src/diff_store.rs:263`, `let was_captured = TRACK &&
            // T::tag(...)`). Stating the clause unconditionally forced verus's
            // `InlineStore` to pay it always, which cost +23% on an untracked
            // e-class ring splice (two full-cell writes per merge) —
            // `containers-conformance/examples/splicesplit.rs`. Untracked flags
            // are dead: nothing reads `captured()` when `!TRACK`.
            TRACK ==> final(self).captured() == old(self).captured();

    fn truncate(&mut self, len: I)
        requires
            old(self).wf(),
            len.as_nat() <= old(self).data().len(),
        ensures
            final(self).wf(),
            final(self).data() == old(self).data().subrange(0, len.as_nat() as int),
            TRACK ==> final(self).captured() == old(self).captured().subrange(0, len.as_nat() as int);

    /// Mark slot `i` as captured without logging or changing `data`. Used by
    /// `Vec::push` when a previously-popped marked index is re-added: the
    /// pop already captured `snap[i]`, so the fresh slot must inherit the
    /// captured flag to keep first-write-wins (and bound the diff log).
    fn mark_captured(&mut self, i: I)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            final(self).wf(),
            final(self).data() == old(self).data(),
            TRACK ==> final(self).captured()
                == old(self).captured().update(i.as_nat() as int, true);

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
            final(self).wf(),
            final(self).data().len() == len.as_nat(),
            // existing prefix preserved
            forall|j: int| 0 <= j < len.as_nat() && j < old(self).data().len()
                ==> #[trigger] final(self).data()[j] == old(self).data()[j],
            final(self).captured().len() == len.as_nat(),  // definitional (padded view at data len)
            // Flags: shared prefix preserved, grown region clear (both
            // stores: truncate retires, growth extends with clear tags).
            TRACK ==> forall|j: int| 0 <= j < len.as_nat()
                ==> #[trigger] final(self).captured()[j]
                    == (j < old(self).captured().len() && old(self).captured()[j]);

    // -- capture protocol ----------------------------------------------------

    /// Begin a new frame. Clears the capture flag for all slots in
    /// `[0, saved_len)`. The `prev_diffs` slice is the diff log of the
    /// outer (parent) frame, used by `InlineStore` to know which inline
    /// tags need clearing; `ParallelStore` ignores it.
    fn prepare_mark(&mut self, saved_len: I, prev_diffs: &[(T, I)])
        requires
            old(self).wf(),
            saved_len.as_nat() <= old(self).data().len(),
            // Sparse-clear soundness (production's O(diffs) protocol): every
            // set capture flag is indexed by some entry of `prev_diffs`, so
            // clearing exactly those slots clears ALL flags. The caller
            // (`Vec::mark`) holds this from its wf capture-flag bridge —
            // a flag is only ever set by capture/force_capture, which push
            // the slot into the diff log in the same step.
            TRACK ==> forall|j: int| 0 <= j < old(self).captured().len()
                && #[trigger] old(self).captured()[j]
                ==> exists|k: int| 0 <= k < prev_diffs@.len()
                        && (#[trigger] prev_diffs@[k]).1.as_nat() == j as nat,
        ensures
            final(self).wf(),
            final(self).data() == old(self).data(),
            TRACK ==> forall|i: int| 0 <= i < saved_len.as_nat() ==>
                #[trigger] final(self).captured()[i] == false;

    /// First-write-wins capture. If the slot is in-frame and not yet captured,
    /// log `(old.data()[i], i)` and flip `captured[i]`.
    fn capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            final(self).wf(),
            final(self).data() == old(self).data(),
            // First-write-wins (all TRACK-conditional; an untracked store's
            // flags are dead and its capture is a no-op — production parity):
            (TRACK && i.as_nat() < saved_len.as_nat()
                && !old(self).captured()[i.as_nat() as int])
                ==> {
                    &&& final(diff_log)@ == old(diff_log)@.push(
                            (old(self).data()[i.as_nat() as int], i))
                    &&& final(self).captured()[i.as_nat() as int] == true
                    &&& forall|j: int| 0 <= j < final(self).captured().len() && j != i.as_nat()
                            ==> #[trigger] final(self).captured()[j] == old(self).captured()[j]
                },
            // Already captured, out of frame, or untracked: no-op.
            !(TRACK && i.as_nat() < saved_len.as_nat()
                && !old(self).captured()[i.as_nat() as int])
                ==> {
                    &&& final(diff_log)@ == old(diff_log)@
                    &&& (TRACK ==> final(self).captured() == old(self).captured())
                };

    /// Unconditional capture (used by `pop` so the about-to-vanish slot is
    /// always logged). Within-frame: log + set captured. Out-of-frame: no-op.
    fn force_capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>)
        requires
            old(self).wf(),
            i.as_nat() < old(self).data().len(),
        ensures
            final(self).wf(),
            final(self).data() == old(self).data(),
            (TRACK && i.as_nat() < saved_len.as_nat()) ==> {
                &&& final(diff_log)@ == old(diff_log)@.push(
                        (old(self).data()[i.as_nat() as int], i))
                &&& final(self).captured()[i.as_nat() as int] == true
                &&& forall|j: int| 0 <= j < final(self).captured().len() && j != i.as_nat()
                        ==> #[trigger] final(self).captured()[j] == old(self).captured()[j]
            },
            !(TRACK && i.as_nat() < saved_len.as_nat()) ==> {
                &&& final(diff_log)@ == old(diff_log)@
                &&& (TRACK ==> final(self).captured() == old(self).captured())
            };

    /// Pre-replay flag reset: clear EVERY capture flag, given that each set
    /// flag is named by some entry of the about-to-be-replayed slice (the
    /// caller's wf bridge fact). ParallelStore: one in-place bitmap memset
    /// (production pays the identical zero inside its finish_restore;
    /// hoisting it lets `restore_entry` do NO per-entry bit work — measured
    /// 1.6µs/2048-entry replay). InlineStore: sparse tag-clear over the
    /// named slots, O(replayed) — the same protocol as its `prepare_mark`.
    fn begin_restore(&mut self, replayed_diffs: &[(T, I)])
        requires
            old(self).wf(),
            TRACK ==> forall|j: int| 0 <= j < old(self).captured().len()
                && #[trigger] old(self).captured()[j]
                ==> exists|k: int| 0 <= k < replayed_diffs@.len()
                        && (#[trigger] replayed_diffs@[k]).1.as_nat() == j as nat,
        ensures
            final(self).wf(),
            final(self).data() == old(self).data(),
            TRACK ==> forall|j: int| 0 <= j < final(self).captured().len()
                ==> !(#[trigger] final(self).captured()[j]);

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
            final(self).wf(),
            // In-frame, in-bounds: overwrite.
            (index.as_nat() < target_saved_len.as_nat()
                && index.as_nat() < old(self).data().len())
                ==> final(self).data() ==
                    old(self).data().update(index.as_nat() as int, *old_value),
            // In-frame, at end: push.
            (index.as_nat() < target_saved_len.as_nat()
                && index.as_nat() == old(self).data().len())
                ==> final(self).data() == old(self).data().push(*old_value),
            // Out-of-frame: no-op on data.
            (index.as_nat() >= target_saved_len.as_nat())
                ==> final(self).data() == old(self).data(),
            // Flags decrease-only: a replay write never SETS a flag
            // (InlineStore writes tag-clear reprs; ParallelStore leaves its
            // pre-zeroed bitmap untouched). From `begin_restore`'s all-clear
            // start this keeps every flag clear through the replay — the
            // sparse set-only `finish_restore` needs exactly that.
            TRACK ==> forall|j: int| 0 <= j < final(self).captured().len()
                && #[trigger] final(self).captured()[j]
                ==> j < old(self).captured().len() && old(self).captured()[j];

    /// Rebuild `captured` from the surviving diff suffix. After restore, a
    /// slot is captured iff it appears in the parent frame's diff log.
    /// The all-clear requires (established by the replay loop via
    /// `restore_entry`'s flag-clearing ensures) is what makes an O(diffs)
    /// set-only implementation sound — production's protocol.
    fn finish_restore(&mut self, current_frame_diffs: &[(T, I)], saved_len: I)
        requires
            old(self).wf(),
            saved_len.as_nat() <= old(self).data().len(),
            // ALL flags clear (begin_restore + flag-free replay establish
            // this over the full flag range, not just [0, saved_len)).
            TRACK ==> forall|j: int| 0 <= j < old(self).captured().len()
                ==> !(#[trigger] old(self).captured()[j]),
        ensures
            final(self).wf(),
            final(self).data() == old(self).data(),
            // Within `[0, saved_len)`, captured iff some surviving diff entry
            // points at this index. Above `saved_len`, unspecified (those
            // slots are about to be truncated by `Vec::restore`).
            TRACK ==> forall|i: int| 0 <= i < saved_len.as_nat() ==>
                #[trigger] final(self).captured()[i] == exists|k: int|
                    0 <= k < current_frame_diffs@.len()
                        && (#[trigger] current_frame_diffs@[k]).1.as_nat() == i;

    // -- maintenance ---------------------------------------------------------

    fn shrink_if(&mut self, factor: usize, headroom: usize)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).data() == old(self).data(),
            TRACK ==> final(self).captured() == old(self).captured();

    /// Heap bytes used by the backing storage (diagnostic; no spec content —
    /// it's a capacity measurement, not part of the semi-persistent contract).
    /// Default 0 for backends that don't introspect capacity.
    fn heap_bytes(&self) -> usize {
        0
    }

    /// Contiguous read access to the raw values, when the backend stores them
    /// contiguously (production parity: `Some` for `ParallelStore`, `None`
    /// for `InlineStore`, whose cells are tag-carrying reprs, not `T`s).
    fn as_slice(&self) -> (r: Option<&[T]>)
        ensures r matches Some(s) ==> s@ == self.data(),
    {
        None
    }
}

} // verus!
