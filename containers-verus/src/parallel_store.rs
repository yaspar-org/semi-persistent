// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `ParallelStore<T, I>`: SoA layout with a parallel capture-flag vector.
//!
//! Production uses `Vec<u64>` packed as a bitset for cache density; we use
//! `Vec<bool>` here so the capture flags' spec view is literally the field's
//! `@`. The proofs are about correctness, not memory layout — once the
//! contracts are discharged, swapping in a bitset is a non-observable change
//! that can be revisited later without touching `Vec`'s proof.
//!
//! Implements `DiffStore<T, I, TRACK>` for any `T: Copy` and `I: IndexLike`.
//! No `Tagged` requirement — the capture bit lives outside the value type.

use vstd::prelude::*;

use crate::diff_store::DiffStore;
use crate::index_like::IndexLike;

verus! {

/// Parallel-bitset DiffStore.
///
/// Invariant (via `wf`): `data@.len() == captured@.len()`. Push, pop, set,
/// truncate maintain this invariant by mirroring the operation on both
/// vectors. `set_raw` only touches `data`. The capture protocol touches
/// `captured` (and the diff log) without disturbing `data`.
pub struct ParallelStore<T, I>
where
    T: Sized + Copy,
    I: IndexLike,
{
    pub data: Vec<T>,
    pub captured: Vec<bool>,
    pub _phantom: core::marker::PhantomData<I>,
}

impl<T, I, const TRACK: bool> DiffStore<T, I, TRACK> for ParallelStore<T, I>
where
    T: Sized + Copy,
    I: IndexLike,
{
    open spec fn data(&self) -> Seq<T> { self.data@ }
    open spec fn captured(&self) -> Seq<bool> { self.captured@ }
    open spec fn wf(&self) -> bool {
        &&& self.data@.len() == self.captured@.len()
        &&& self.data@.len() < I::max_nat()
    }

    proof fn lemma_wf_captured_len(&self) {}

    fn is_empty(&self) -> bool {
        self.data.len() == 0
    }

    fn len(&self) -> I {
        let n = self.data.len();
        match I::try_from_usize(n) {
            Some(i) => i,
            None => {
                proof {
                    // wf() guarantees data.len() < I::max_nat(), so
                    // try_from_usize(data.len()) is Some.
                    assert(false);
                }
                I::min()
            }
        }
    }

    fn get(&self, i: I) -> T {
        self.data[i.as_usize()]
    }

    fn push(&mut self, value: T) {
        self.data.push(value);
        self.captured.push(false);
    }

    fn pop(&mut self) -> Option<T> {
        let r = self.data.pop();
        let _ = self.captured.pop();
        r
    }

    fn set_raw(&mut self, i: I, value: T) {
        let iu = i.as_usize();
        self.data.set(iu, value);
    }

    fn truncate(&mut self, len: I) {
        let lu = len.as_usize();
        self.data.truncate(lu);
        self.captured.truncate(lu);
    }

    fn mark_captured(&mut self, i: I) {
        let iu = i.as_usize();
        self.captured.set(iu, true);
    }

    fn resize_default(&mut self, len: I)
        where T: core::default::Default
    {
        let target = len.as_usize();
        // The data prefix shared with the original: min(old_len, target).
        let ghost shared = if old(self).data@.len() < target as nat {
            old(self).data@.len()
        } else {
            target as nat
        };
        // Truncate if longer.
        if self.data.len() > target {
            self.data.truncate(target);
            self.captured.truncate(target);
        }
        // Grow with defaults if shorter.
        while self.data.len() < target
            invariant
                self.data@.len() == self.captured@.len(),
                self.data@.len() <= target,
                target == len.as_nat(),
                len.as_nat() < I::max_nat(),
                shared <= self.data@.len(),
                shared == (if old(self).data@.len() < target as nat {
                    old(self).data@.len()
                } else {
                    target as nat
                }),
                forall|j: int| 0 <= j < shared
                    ==> #[trigger] self.data@[j] == old(self).data@[j],
            decreases target - self.data.len(),
        {
            self.data.push(T::default());
            self.captured.push(false);
        }
    }

    fn prepare_mark(&mut self, saved_len: I, prev_diffs: &[(T, I)]) {
        // Clear all capture flags in [0, data.len()).
        let n = self.captured.len();
        let mut i: usize = 0;
        while i < n
            invariant
                self.data@.len() == old(self).data@.len(),
                self.captured@.len() == old(self).captured@.len(),
                self.captured@.len() == n,
                forall|j: int| 0 <= j < i as int ==>
                    #[trigger] self.captured@[j] == false,
                forall|j: int| i as int <= j < self.captured@.len() ==>
                    #[trigger] self.captured@[j] == old(self).captured@[j],
                self.data@ == old(self).data@,
            decreases (n - i) as int,
        {
            self.captured.set(i, false);
            i += 1;
        }
        // Postcondition asks only for `[0, saved_len)` cleared, which is
        // implied since saved_len.as_nat() <= data.len() and we cleared
        // everything in [0, data.len()).
    }

    fn capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>) {
        let iu = i.as_usize();
        let su = saved_len.as_usize();
        if iu >= su {
            return;
        }
        if !self.captured[iu] {
            let old_val = self.data[iu];
            diff_log.push((old_val, i));
            self.captured.set(iu, true);
        }
    }

    fn force_capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>) {
        let iu = i.as_usize();
        let su = saved_len.as_usize();
        if iu >= su {
            return;
        }
        let old_val = self.data[iu];
        diff_log.push((old_val, i));
        self.captured.set(iu, true);
    }

    fn restore_entry(&mut self, index: I, old_value: &T, target_saved_len: I) {
        let iu = index.as_usize();
        let tsl = target_saved_len.as_usize();
        if iu >= tsl {
            return;
        }
        if iu >= self.data.len() {
            // Pre-pad case: a previous restore_entry in this loop pushed up
            // to but not past iu. The contract requires iu == data.len().
            self.data.push(*old_value);
            self.captured.push(false);
        } else {
            self.data.set(iu, *old_value);
        }
    }

    fn finish_restore(&mut self, current_frame_diffs: &[(T, I)], saved_len: I) {
        let n = self.captured.len();

        // Step 1: clear all captured flags.
        let mut i: usize = 0;
        while i < n
            invariant
                self.captured@.len() == n,
                self.data@ == old(self).data@,
                forall|j: int| 0 <= j < i as int ==>
                    #[trigger] self.captured@[j] == false,
            decreases (n - i) as int,
        {
            self.captured.set(i, false);
            i += 1;
        }

        // Step 2: rebuild captured from the surviving diffs.
        //
        // Invariant: for each in-bounds slot j, `captured[j]` is true iff
        // some processed diff entry (kk < k) has its index equal to j AND
        // is itself in bounds (idx.as_nat() < n). That second clause is
        // critical: out-of-bounds diff entries are dropped by the `iu < n`
        // guard below and must therefore be excluded from the existential
        // for the invariant to hold.
        let m = current_frame_diffs.len();
        let mut k: usize = 0;
        while k < m
            invariant
                self.captured@.len() == n,
                self.data@ == old(self).data@,
                current_frame_diffs@.len() == m,
                k <= m,
                forall|j: int| 0 <= j < n as int ==>
                    #[trigger] self.captured@[j] == (
                        exists|kk: int|
                            0 <= kk < k as int
                                && (#[trigger] current_frame_diffs@[kk]).1.as_nat() == j as nat
                    ),
            decreases (m - k) as int,
        {
            let idx = current_frame_diffs[k].1;
            let iu = idx.as_usize();
            if iu < n {
                self.captured.set(iu, true);
            }
            k += 1;
        }

        // Bridge to the postcondition: the postcondition restricts j to
        // [0, saved_len.as_nat()), which (by precondition) is a prefix of
        // [0, n). On that prefix the existentials over kk in [0, m) and
        // kk in [0, current_frame_diffs.len()) coincide, and the
        // "in-bounds idx" guard above is redundant since j < saved_len
        // <= n means any diff entry pointing at j is automatically
        // in-bounds.
    }

    fn shrink_if(&mut self, factor: usize, headroom: usize) {
        // No-op for now: shrink_to is a hint and doesn't change @.
        // Production performs capacity reclamation here; the verus version
        // can no-op without changing observable behavior.
    }
}

impl<T, I> ParallelStore<T, I>
where
    T: Sized + Copy,
    I: IndexLike,
{
    /// A fresh, empty store: no data, no capture flags. Well-formed for any
    /// `TRACK` (the parallel store's `wf` doesn't depend on it).
    pub fn new<const TRACK: bool>() -> (s: ParallelStore<T, I>)
        ensures
            DiffStore::<T, I, TRACK>::wf(&s),
            s.data@.len() == 0,
            s.captured@.len() == 0,
    {
        proof { I::lemma_min_as_nat(); I::min_spec().lemma_as_nat_bounded(); }  // 0 < I::max_nat()
        ParallelStore { data: Vec::new(), captured: Vec::new(), _phantom: core::marker::PhantomData }
    }
}

} // verus!
