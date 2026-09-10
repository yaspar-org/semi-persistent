// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `TrailStore<T, I>`: the chronological-capture DiffStore (the trail
//! discipline). Every in-frame write appends its old value to the diff log
//! unconditionally; NO runtime capture flags exist. The flags the `DiffStore`
//! contract is phrased over are GHOST state, so the write path is one read
//! plus one append (no flag load, no branch on it), and the flag-protocol
//! steps (`prepare_mark`, `begin_restore`, `finish_restore`) are exec no-ops
//! where `ParallelStore` pays a bitmap memset.
//!
//! Duplicates are sound because the reconstruction model is first-entry-wins:
//! `overlay` applies a stratum backward, so the chronologically FIRST capture
//! of a cell (the pre-frame value) lands last and wins; later duplicates are
//! inert. What the discipline gives up: the one-entry-per-cell frame bound
//! (the log grows with total writes, not the write set), and the sealing and
//! reordering paths, which require the unique discipline
//! (`unique_capture_spec` gates them). A `TrailStore` column's diff log stays
//! plain and never compresses — the SMT profile's trade, chosen per column at
//! its declaration site (`VecT`).

use vstd::prelude::*;

use crate::diff_store::DiffStore;
use crate::index_like::IndexLike;

verus! {


/// Chronological-capture DiffStore. Invariant (via `wf`): the ghost flag
/// sequence tracks the data length exactly.
pub struct TrailStore<T, I>
where
    T: Sized + Copy,
    I: IndexLike,
{
    pub(crate) data: Vec<T>,
    /// The capture flags the `DiffStore` contract is phrased over. Ghost:
    /// no runtime counterpart exists, which is the discipline's point. Never read
    /// by executable code for that reason.
    #[allow(dead_code)]
    pub(crate) captured: Ghost<Seq<bool>>,
    pub(crate) _phantom: core::marker::PhantomData<I>,
}

impl<T, I> TrailStore<T, I>
where
    T: Sized + Copy,
    I: IndexLike,
{
    pub open(crate) spec fn data_spec(&self) -> Seq<T> {
        self.data@
    }

    pub open(crate) spec fn captured_spec(&self) -> Seq<bool> {
        self.captured@
    }

    pub open(crate) spec fn wf_spec(&self) -> bool {
        &&& self.captured@.len() == self.data@.len()
        &&& self.data@.len() < I::max_nat()
    }

    pub fn new() -> (r: Self)
        ensures
            r.wf_spec(),
            r.data_spec().len() == 0,
    {
        proof {
            <I as IndexLike>::lemma_max_nat_positive();
        }
        TrailStore {
            data: Vec::new(),
            captured: Ghost(Seq::empty()),
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<T, I, const TRACK: bool> DiffStore<T, I, TRACK> for TrailStore<T, I>
where
    T: Sized + Copy,
    I: IndexLike,
{
    open spec fn data(&self) -> Seq<T> { self.data_spec() }
    open spec fn captured(&self) -> Seq<bool> { self.captured_spec() }
    open spec fn wf(&self) -> bool { self.wf_spec() }

    proof fn lemma_wf_captured_len(&self) {}

    open spec fn unique_capture_spec(&self) -> bool { false }

    fn unique_capture(&self) -> bool { false }

    #[inline(always)]
    fn is_empty(&self) -> bool {
        self.data.len() == 0
    }

    fn raw_len(&self) -> (n: usize) {
        self.data.len()
    }

    #[inline(always)]
    fn len(&self) -> I {
        I::try_from_usize(self.data.len()).expect("len overflow")
    }

    #[inline(always)]
    fn get(&self, i: I) -> T {
        self.data[i.as_usize()]
    }

    #[inline(always)]
    fn push(&mut self, value: T) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        self.data.push(value);
        proof {
            self.captured@ = self.captured@.push(false);
        }
    }

    #[inline(always)]
    fn pop(&mut self) -> Option<T> {
        broadcast use crate::diff_store::lemma_trail_discipline;
        let r = self.data.pop();
        proof {
            if r is Some {
                self.captured@ = self.captured@.drop_last();
            }
        }
        r
    }

    #[inline(always)]
    fn set_raw(&mut self, i: I, value: T) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        let iu = i.as_usize();
        self.data.set(iu, value);
    }

    fn truncate(&mut self, len: I) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        let lu = len.as_usize();
        self.data.truncate(lu);
        proof {
            self.captured@ = self.captured@.subrange(0, len.as_nat() as int);
        }
    }

    #[inline(always)]
    fn mark_captured(&mut self, i: I) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        proof {
            self.captured@ = self.captured@.update(i.as_nat() as int, true);
        }
    }

    fn resize_default(&mut self, len: I)
        where T: core::default::Default
    {
        broadcast use crate::diff_store::lemma_trail_discipline;
        let ghost old_flags = self.captured@;
        let ghost old_len = self.data@.len();
        let target = len.as_usize();
        if self.data.len() > target {
            self.data.truncate(target);
        }
        while self.data.len() < target
            invariant
                self.data@.len() <= target,
                target == len.as_nat(),
                len.as_nat() < I::max_nat(),
                // Length floor per case: it pins every quantified j below the
                // current data length, so the prefix forall never reads an
                // out-of-bounds (arbitrary) element inside the loop.
                old_len > target ==> self.data@.len() == target,
                old_len <= target ==> old_len <= self.data@.len(),
                forall|j: int| 0 <= j < len.as_nat() && j < old_len
                    ==> #[trigger] self.data@[j] == old(self).data@[j],
                old_len == old(self).data@.len(),
            decreases target - self.data.len(),
        {
            self.data.push(T::default());
        }
        proof {
            // The flag view at the new length: shared prefix preserved,
            // grown or truncated region reads clear.
            self.captured@ = Seq::new(len.as_nat(),
                |j: int| j < old_flags.len() && old_flags[j]);
        }
    }

    fn prepare_mark(&mut self, _saved_len: I, _prev_diffs: &[I]) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        // Exec no-op: the flags are ghost, so the frame-open clear costs
        // nothing (ParallelStore pays a bitmap memset here).
        proof {
            self.captured@ = Seq::new(self.data@.len(), |_j: int| false);
        }
    }

    #[inline(always)]
    fn capture<VC: crate::value_compressor::ValueCompressor<T>>(&mut self, i: I, saved_len: I, diff_log: &mut crate::diff_log::DiffLog<T, I, VC>) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        if !TRACK {
            return;
        }
        let iu = i.as_usize();
        let su = saved_len.as_usize();
        if iu >= su {
            return;
        }
        // The chronological discipline: append unconditionally. No flag
        // read, no branch on capture state — this is the hot-path saving.
        let old_val = self.data[iu];
        diff_log.push(old_val, i);
        proof {
            if !self.captured@[iu as int] {
                self.captured@ = self.captured@.update(iu as int, true);
            } else {
                // Already captured: the ghost flags are unchanged (the
                // duplicate entry is inert under first-entry-wins).
                assert(self.captured@.update(iu as int, true) =~= self.captured@);
            }
        }
    }

    fn force_capture(&mut self, i: I, saved_len: I, diff_log: &mut crate::diff_log::DiffLog<T, I>) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        if !TRACK {
            return;
        }
        let iu = i.as_usize();
        let su = saved_len.as_usize();
        if iu >= su {
            return;
        }
        let old_val = self.data[iu];
        diff_log.push(old_val, i);
        proof {
            self.captured@ = self.captured@.update(iu as int, true);
        }
    }

    open spec fn needs_replayed_indices_spec(&self) -> bool { false }

    fn needs_replayed_indices(&self) -> bool { false }

    fn begin_restore(&mut self, _replayed_diffs: &[I]) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        // Exec no-op (ghost clear only).
        proof {
            self.captured@ = Seq::new(self.data@.len(), |_j: int| false);
        }
    }

    fn restore_entry(&mut self, index: I, old_value: &T, target_saved_len: I) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        let iu = index.as_usize();
        let tsl = target_saved_len.as_usize();
        if iu >= tsl {
            return;
        }
        if iu >= self.data.len() {
            self.data.push(*old_value);
            proof {
                self.captured@ = self.captured@.push(false);
            }
        } else {
            self.data.set(iu, *old_value);
        }
    }

    fn restore_overlay<VC: crate::value_compressor::ValueCompressor<T>>(
        &mut self,
        diff_log: &crate::diff_log::DiffLog<T, I, VC>,
        lo: usize,
        hi: usize,
    ) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        let ghost pre_len = self.data@.len();
        diff_log.restore_range_into(lo, hi, &mut self.data);
        proof {
            crate::vec::lemma_overlay_len::<T, I>(
                old(self).data@, diff_log@, lo as int, hi as int);
            assert(self.data@.len() == pre_len);
        }
    }

    fn finish_restore(&mut self, current_frame_diffs: &[I], _saved_len: I) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        // Exec no-op: the post-restore flag state is defined, not computed
        // (ParallelStore walks the surviving diffs setting bits here).
        proof {
            let diffs = current_frame_diffs@;
            self.captured@ = Seq::new(self.data@.len(), |i: int| {
                exists|k: int| 0 <= k < diffs.len()
                    && (#[trigger] diffs[k]).as_nat() == i as nat
            });
        }
    }

    fn shrink_if(&mut self, _factor: usize, _headroom: usize) {
        broadcast use crate::diff_store::lemma_trail_discipline;
        // Capacity reclamation is optional under the contract; the trail
        // store keeps it a no-op (its columns are hot search state).
    }

    fn as_slice(&self) -> Option<&[T]> {
        Some(self.data.as_slice())
    }
}

} // verus!
