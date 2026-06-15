// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `InlineStore<T, I>` for `T: Tagged`: capture flag packed into `T::Repr`.
//!
//! The internal storage is `Vec<T::Repr>`. The abstract `data()` spec view
//! projects each repr through `T::value_of`, so it ignores the capture bit.
//! `T`'s `set_tag`/`clear_tag` round-trip axioms guarantee that flipping the
//! capture bit doesn't disturb `value_of`, so the abstract sequence is
//! invariant under capture-flag edits — which is what `Vec`'s proof needs.
//!
//! `InlineStore`'s `wf()` adds one universal invariant: every stored repr
//! is `T::repr_wf` (in the image of the encoding). Methods that introduce
//! new reprs (`push`, `restore_entry`) come via `into_repr`, which produces
//! a well-formed repr; methods that mutate tags (`set_tag`, `clear_tag`)
//! preserve well-formedness by axiom.

use vstd::prelude::*;

use crate::diff_store::DiffStore;
use crate::index_like::IndexLike;
use crate::tagged::Tagged;

verus! {

/// Capture-flag-inline DiffStore.
///
/// Invariants (`wf`): all reprs are well-formed; `data@.len() < I::max_nat()`.
/// The abstract `data()` is `T::value_of` applied pointwise. The abstract
/// `captured()` is `T::tag_of` applied pointwise.
pub struct InlineStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    pub data: Vec<T::Repr>,
    pub _phantom: core::marker::PhantomData<I>,
}

impl<T, I> InlineStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    /// Spec helper: `data()` as the `value_of`-mapped sequence of reprs.
    pub open spec fn data_spec(&self) -> Seq<T> {
        Seq::new(self.data@.len(), |i: int| T::value_of(self.data@[i]))
    }

    /// Spec helper: `captured()` as the `tag_of`-mapped sequence of reprs.
    pub open spec fn captured_spec(&self) -> Seq<bool> {
        Seq::new(self.data@.len(), |i: int| T::tag_of(self.data@[i]))
    }

    /// A fresh, empty store. Well-formed for any `TRACK` (the repr_wf forall
    /// is vacuous on empty data).
    pub fn new<const TRACK: bool>() -> (s: InlineStore<T, I>)
        ensures
            DiffStore::<T, I, TRACK>::wf(&s),
            s.data_spec().len() == 0,
            s.captured_spec().len() == 0,
    {
        proof { I::lemma_max_nat_positive(); }  // 0 < I::max_nat()
        InlineStore { data: Vec::new(), _phantom: core::marker::PhantomData }
    }
}

impl<T, I, const TRACK: bool> DiffStore<T, I, TRACK> for InlineStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    open spec fn data(&self) -> Seq<T> { self.data_spec() }
    open spec fn captured(&self) -> Seq<bool> { self.captured_spec() }
    open spec fn wf(&self) -> bool {
        &&& self.data@.len() < I::max_nat()
        &&& forall|i: int| 0 <= i < self.data@.len() ==>
                #[trigger] T::repr_wf(self.data@[i])
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
                proof { assert(false); }
                I::min()
            }
        }
    }

    fn get(&self, i: I) -> T {
        T::from_repr(&self.data[i.as_usize()])
    }

    fn push(&mut self, value: T) {
        let r = value.into_repr();
        self.data.push(r);
    }

    fn pop(&mut self) -> Option<T> {
        match self.data.pop() {
            Some(r) => Some(T::from_repr(&r)),
            None => None,
        }
    }

    fn set_raw(&mut self, i: I, value: T) {
        let iu = i.as_usize();
        let was_captured = T::tag(&self.data[iu]);
        let mut new_repr = value.into_repr();
        if was_captured {
            T::set_tag(&mut new_repr);
        }
        self.data.set(iu, new_repr);
    }

    fn truncate(&mut self, len: I) {
        let lu = len.as_usize();
        self.data.truncate(lu);
    }

    fn mark_captured(&mut self, i: I) {
        let iu = i.as_usize();
        let mut r = self.data[iu];
        T::set_tag(&mut r);
        self.data.set(iu, r);
    }

    fn resize_default(&mut self, len: I)
        where T: core::default::Default
    {
        let target = len.as_usize();
        let ghost shared = if old(self).data@.len() < target as nat {
            old(self).data@.len()
        } else {
            target as nat
        };
        if self.data.len() > target {
            self.data.truncate(target);
        }
        while self.data.len() < target
            invariant
                self.data@.len() <= target,
                target == len.as_nat(),
                len.as_nat() < I::max_nat(),
                shared <= self.data@.len(),
                shared == (if old(self).data@.len() < target as nat {
                    old(self).data@.len()
                } else {
                    target as nat
                }),
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::repr_wf(self.data@[j]),
                forall|j: int| 0 <= j < shared ==>
                    #[trigger] T::value_of(self.data@[j])
                        == T::value_of(old(self).data@[j]),
            decreases target - self.data.len(),
        {
            let filler = T::default().into_repr();
            self.data.push(filler);
        }
    }

    fn prepare_mark(&mut self, _saved_len: I, _prev_diffs: &[(T, I)]) {
        // Clear tag on every slot in [0, data.len()).
        let n = self.data.len();
        let mut i: usize = 0;
        while i < n
            invariant
                self.data@.len() == n,
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::repr_wf(self.data@[j]),
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::value_of(self.data@[j])
                        == T::value_of(old(self).data@[j]),
                forall|j: int| 0 <= j < i as int ==>
                    #[trigger] T::tag_of(self.data@[j]) == false,
            decreases (n - i) as int,
        {
            // We need a temporary because Vec doesn't have `set_with` / a
            // direct way to mutate in place; we read, mutate, write back.
            let mut r = self.data[i];
            T::clear_tag(&mut r);
            self.data.set(i, r);
            i += 1;
        }
    }

    fn capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>) {
        let iu = i.as_usize();
        let su = saved_len.as_usize();
        if iu >= su {
            return;
        }
        let r = self.data[iu];
        if !T::tag(&r) {
            let v = T::from_repr(&r);
            diff_log.push((v, i));
            let mut new_r = r;
            T::set_tag(&mut new_r);
            self.data.set(iu, new_r);
        }
    }

    fn force_capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>) {
        let iu = i.as_usize();
        let su = saved_len.as_usize();
        if iu >= su {
            return;
        }
        let r = self.data[iu];
        let v = T::from_repr(&r);
        diff_log.push((v, i));
        let mut new_r = r;
        T::set_tag(&mut new_r);
        self.data.set(iu, new_r);
    }

    fn restore_entry(&mut self, index: I, old_value: &T, target_saved_len: I) {
        let iu = index.as_usize();
        let tsl = target_saved_len.as_usize();
        if iu >= tsl {
            return;
        }
        let new_r = (*old_value).into_repr();
        if iu >= self.data.len() {
            self.data.push(new_r);
        } else {
            self.data.set(iu, new_r);
        }
    }

    fn finish_restore(&mut self, current_frame_diffs: &[(T, I)], _saved_len: I) {
        let n = self.data.len();

        // Step 1: clear all tags in [0, data.len()).
        let mut i: usize = 0;
        while i < n
            invariant
                self.data@.len() == n,
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::repr_wf(self.data@[j]),
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::value_of(self.data@[j])
                        == T::value_of(old(self).data@[j]),
                forall|j: int| 0 <= j < i as int ==>
                    #[trigger] T::tag_of(self.data@[j]) == false,
            decreases (n - i) as int,
        {
            let mut r = self.data[i];
            T::clear_tag(&mut r);
            self.data.set(i, r);
            i += 1;
        }

        // Step 2: rebuild tags from surviving diffs.
        let m = current_frame_diffs.len();
        let mut k: usize = 0;
        while k < m
            invariant
                self.data@.len() == n,
                current_frame_diffs@.len() == m,
                k <= m,
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::repr_wf(self.data@[j]),
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::value_of(self.data@[j])
                        == T::value_of(old(self).data@[j]),
                forall|j: int| 0 <= j < n as int ==>
                    #[trigger] T::tag_of(self.data@[j]) == (
                        exists|kk: int|
                            0 <= kk < k as int
                                && (#[trigger] current_frame_diffs@[kk]).1.as_nat()
                                    == j as nat
                    ),
            decreases (m - k) as int,
        {
            let idx = current_frame_diffs[k].1;
            let iu = idx.as_usize();
            if iu < n {
                let mut r = self.data[iu];
                T::set_tag(&mut r);
                self.data.set(iu, r);
            }
            k += 1;
        }
    }

    fn shrink_if(&mut self, _factor: usize, _headroom: usize) {
        // No-op: shrink_to is a hint and doesn't change @.
    }
}

} // verus!
