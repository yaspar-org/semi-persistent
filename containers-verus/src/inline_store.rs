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
/// A borrowed read of the stored repr, for stores that hold reprs: the
/// value is `T::value_of(*r)`, and nothing is decoded or copied. The B+ tree
/// cursor reads its nodes this way (a decoded node is the size of its key
/// array). Implemented by the inline store; the parallel and trail stores
/// hold values, not reprs, and do not offer it.
pub trait ReprBorrow<T, I, const TRACK: bool>: DiffStore<T, I, TRACK>
where
    T: Tagged,
    I: IndexLike,
{
    /// Total with documented panic: an out-of-range index refuses; the
    /// contract is conditional on the bound, which the verified callers hold
    /// as a precondition of their own.
    fn get_repr_ref(&self, i: I) -> (r: &T::Repr)
        requires self.wf(),
        ensures i.as_nat() < self.data().len() ==> {
            &&& T::repr_wf(*r)
            &&& T::value_of(*r) == self.data()[i.as_nat() as int]
        };
}

impl<T, I, const TRACK: bool> ReprBorrow<T, I, TRACK> for InlineStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    #[inline(always)]
    fn get_repr_ref(&self, i: I) -> (r: &T::Repr) {
        if !(i.as_usize() < self.data.as_slice().len()) {
            crate::guard::refuse("InlineStore::get_repr_ref: index out of bounds");
        }
        &self.data[i.as_usize()]
    }
}

/// `captured()` is `T::tag_of` applied pointwise.
pub struct InlineStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    pub(crate) data: Vec<T::Repr>,
    pub(crate) _phantom: core::marker::PhantomData<I>,
}

impl<T, I> InlineStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    /// Spec helper: `data()` as the `value_of`-mapped sequence of reprs.
    pub open(crate) spec fn data_spec(&self) -> Seq<T> {
        Seq::new(self.data@.len(), |i: int| T::value_of(self.data@[i]))
    }

    /// Spec helper: `captured()` as the `tag_of`-mapped sequence of reprs.
    pub open(crate) spec fn captured_spec(&self) -> Seq<bool> {
        Seq::new(self.data@.len(), |i: int| T::tag_of(self.data@[i]))
    }

    /// Spec helper: no repr carries the tag (the untracked half of `wf`).
    pub open(crate) spec fn untagged_spec(&self) -> bool {
        forall|i: int| 0 <= i < self.data@.len() ==> !(#[trigger] T::tag_of(self.data@[i]))
    }

    /// Spec helper: the `DiffStore::wf` body (factored so the open trait-impl
    /// spec fn contains no direct field access — privacy closeout).
    pub open(crate) spec fn wf_spec(&self) -> bool {
        &&& self.data@.len() < I::max_nat()
        &&& forall|i: int| 0 <= i < self.data@.len() ==>
                #[trigger] T::repr_wf(self.data@[i])
    }

    /// A fresh, empty store. Well-formed for any `TRACK` (the repr_wf forall is
    /// vacuous on empty data), so the ensures is stated for BOTH `TRACK` values
    /// rather than taking a `TRACK` const generic. prod-parity: production's
    /// `InlineStore::new()` takes no turbofish, and the const generic could not
    /// be inferred through `Vec::with_store` (whose return type does not mention
    /// `TRACK`) — the consumer calls `InlineStore::new()` bare.
    pub(crate) fn new() -> (s: InlineStore<T, I>)
        ensures
            crate::diff_store_ops::DiffStoreOps::<T, I, false>::wf(&s),
            crate::diff_store_ops::DiffStoreOps::<T, I, true>::wf(&s),
            s.data_spec().len() == 0,
            s.captured_spec().len() == 0,
    {
        proof { I::lemma_max_nat_positive(); }  // 0 < I::max_nat()
        InlineStore { data: Vec::new(), _phantom: core::marker::PhantomData }
    }
}

// prod-parity: `Default` = the empty store — production parity
// (`containers/src/diff_store.rs:225`). The consumer builds caches whose stores
// are `#[derive(Default)]`'d (`caches.rs`).
impl<T: Tagged, I: IndexLike> core::default::Default for InlineStore<T, I> {
    fn default() -> (s: InlineStore<T, I>) {
        InlineStore::new()
    }
}

impl<T, I, const TRACK: bool> crate::diff_store_ops::DiffStoreOps<T, I, TRACK> for InlineStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    open spec fn data(&self) -> Seq<T> { self.data_spec() }
    open spec fn captured(&self) -> Seq<bool> { self.captured_spec() }
    // Untracked, nothing is ever captured, so no repr carries the tag: every
    // write goes through `into_repr` (tag-clear by contract) and the tag
    // setters below return early unless `TRACK`. Stated so reads can decode
    // without the mask.
    open spec fn wf(&self) -> bool {
        &&& self.wf_spec()
        &&& (!TRACK ==> self.untagged_spec())
    }

    #[inline(always)]
    fn get(&self, i: I) -> T {
        if TRACK {
            T::from_repr(&self.data[i.as_usize()])
        } else {
            T::from_repr_clean(&self.data[i.as_usize()])
        }
    }

    #[inline(always)]
    fn push(&mut self, value: T) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        let r = value.into_repr();
        self.data.push(r);
    }

    #[inline(always)]
    fn set_raw(&mut self, i: I, value: T) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        let iu = i.as_usize();
        // `TRACK &&` is production's guard verbatim (`diff_store.rs:263`) and it
        // matters: preserving the inline capture flag across a write costs a
        // load and a branch, and when `!TRACK` the flag is dead — nothing reads
        // `captured()`. See `set_raw`'s TRACK-conditional postcondition in
        // `diff_store.rs`; current machine effects belong in Criterion.
        let was_captured = TRACK && T::tag(&self.data[iu]);
        let mut new_repr = value.into_repr();
        if was_captured {
            T::set_tag(&mut new_repr);
        }
        self.data.set(iu, new_repr);
    }

    fn truncate(&mut self, len: I) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        let lu = len.as_usize();
        self.data.truncate(lu);
    }

    #[inline(always)]
    fn mark_captured(&mut self, i: I) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        if !TRACK {
            return;
        }
        let iu = i.as_usize();
        let mut r = self.data[iu];
        T::set_tag(&mut r);
        self.data.set(iu, r);
    }

    fn resize_default(&mut self, len: I)
        where T: core::default::Default
    {
        broadcast use crate::diff_store::lemma_inline_discipline;
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
                // tags: shared prefix preserved, grown region clear (fillers
                // are into_repr = tag-clear) — the resize flag contract.
                forall|j: int| 0 <= j < shared ==>
                    #[trigger] T::tag_of(self.data@[j])
                        == T::tag_of(old(self).data@[j]),
                forall|j: int| shared <= j < self.data@.len() ==>
                    !(#[trigger] T::tag_of(self.data@[j])),
            decreases target - self.data.len(),
        {
            let filler = T::default().into_repr();
            self.data.push(filler);
        }
    }

    fn prepare_mark(&mut self, _saved_len: I, prev_diffs: &[(T, I)]) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        if !TRACK {
            return;
        }
        // Production's sparse clear: only slots named in the previous frame's
        // diffs can carry a set tag (the requires), so clearing exactly those
        // clears all flags — O(diffs since last mark), not O(len).
        let m = prev_diffs.len();
        let mut k: usize = 0;
        while k < m
            invariant
                TRACK,
                prev_diffs@.len() == m,
                k <= m,
                self.data@.len() == old(self).data@.len(),
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::repr_wf(self.data@[j]),
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::value_of(self.data@[j])
                        == T::value_of(old(self).data@[j]),
                // cleared so far: every slot named by a processed entry.
                forall|j: int| 0 <= j < self.data@.len()
                    && (exists|kk: int| 0 <= kk < k as int
                        && (#[trigger] prev_diffs@[kk]).1.as_nat() == j as nat)
                    ==> !(#[trigger] T::tag_of(self.data@[j])),
                // untouched slots keep their old tag.
                forall|j: int| 0 <= j < self.data@.len()
                    && !(exists|kk: int| 0 <= kk < k as int
                        && (#[trigger] prev_diffs@[kk]).1.as_nat() == j as nat)
                    ==> #[trigger] T::tag_of(self.data@[j])
                        == T::tag_of(old(self).data@[j]),
            decreases (m - k) as int,
        {
            let idx = prev_diffs[k].1;
            let iu = idx.as_usize();
            if iu < self.data.len() {
                let mut r = self.data[iu];
                T::clear_tag(&mut r);
                self.data.set(iu, r);
            }
            k += 1;
        }
        proof {
            // Postcondition: every flag in [0, saved_len) is false. A slot
            // with an OLD set tag is named by some prev_diffs entry (the
            // requires), hence cleared; a slot with an old clear tag either
            // kept it or was cleared — false either way.
            assert forall|i: int| 0 <= i < self.data@.len()
                implies !(#[trigger] T::tag_of(self.data@[i])) by {
                if T::tag_of(old(self).data@[i]) {
                    // requires: some diff entry names i — instantiate the
                    // trait-level existential, then the loop's cleared-so-far
                    // invariant (k == m at exit) finishes.
                    assert(old(self).captured_spec()[i]);
                    assert(crate::diff_store_ops::DiffStoreOps::<T, I, TRACK>::captured(&*old(self))[i]);
                    assert(exists|kk: int| 0 <= kk < prev_diffs@.len()
                        && (#[trigger] prev_diffs@[kk]).1.as_nat() == i as nat);
                    assert(!(T::tag_of(self.data@[i])));
                } else {
                    // old tag clear: either untouched (keeps false) or cleared.
                    if exists|kk: int| 0 <= kk < m as int
                        && (#[trigger] prev_diffs@[kk]).1.as_nat() == i as nat {
                        assert(!(T::tag_of(self.data@[i])));
                    } else {
                        assert(T::tag_of(self.data@[i])
                            == T::tag_of(old(self).data@[i]));
                    }
                }
            }
        }
    }

    #[inline(always)]
    fn capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        if !TRACK {
            return;
        }
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
            proof {
                assert(self.captured_spec()
                    =~= old(self).captured_spec().update(iu as int, true));
            }
        } else {
            proof {
                assert(self.captured_spec() =~= old(self).captured_spec());
                assert(<Self as crate::diff_store_ops::DiffStoreOps<T, I, TRACK>>::unique_capture_spec(self));
            }
        }
    }

    fn force_capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        if !TRACK {
            return;
        }
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

    open spec fn unique_capture_spec(&self) -> bool { true }

    open spec fn needs_replayed_indices_spec(&self) -> bool { true }

    open spec fn restore_entries_clear_capture_spec(&self) -> bool { true }

    fn begin_restore(&mut self, replayed_diffs: &[(T, I)]) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        if !TRACK {
            return;
        }
        // Sparse tag-clear over the named slots (same protocol and proof
        // shape as prepare_mark): every set tag is replay-named (requires),
        // so clearing exactly the named in-range slots clears all flags.
        // O(replayed). (Production's InlineStore has no restore-side clear —
        // its replay writes clear implicitly; the explicit pass keeps the
        // uniform all-clear contract provable store-locally at the same
        // asymptotic cost.)
        let m = replayed_diffs.len();
        let mut k: usize = 0;
        while k < m
            invariant
                TRACK,
                replayed_diffs@.len() == m,
                k <= m,
                self.data@.len() == old(self).data@.len(),
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::repr_wf(self.data@[j]),
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::value_of(self.data@[j])
                        == T::value_of(old(self).data@[j]),
                forall|j: int| 0 <= j < self.data@.len()
                    && (exists|kk: int| 0 <= kk < k as int
                        && (#[trigger] replayed_diffs@[kk]).1.as_nat() == j as nat)
                    ==> !(#[trigger] T::tag_of(self.data@[j])),
                forall|j: int| 0 <= j < self.data@.len()
                    && !(exists|kk: int| 0 <= kk < k as int
                        && (#[trigger] replayed_diffs@[kk]).1.as_nat() == j as nat)
                    ==> #[trigger] T::tag_of(self.data@[j])
                        == T::tag_of(old(self).data@[j]),
            decreases (m - k) as int,
        {
            let idx = replayed_diffs[k].1;
            let iu = idx.as_usize();
            if iu < self.data.len() {
                let mut r = self.data[iu];
                T::clear_tag(&mut r);
                self.data.set(iu, r);
            }
            k += 1;
        }
        proof {
            assert forall|i: int| 0 <= i < self.data@.len()
                implies !(#[trigger] T::tag_of(self.data@[i])) by {
                if T::tag_of(old(self).data@[i]) {
                    assert(crate::diff_store_ops::DiffStoreOps::<T, I, TRACK>::captured(&*old(self))[i]);
                }
            }
        }
    }

    fn restore_entry(&mut self, index: I, old_value: &T, target_saved_len: I) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        let iu = index.as_usize();
        let tsl = target_saved_len.as_usize();
        if iu >= tsl {
            return;
        }
        // into_repr IS tag-clear: the write clears the slot's capture flag.
        let new_r = (*old_value).into_repr();
        if iu >= self.data.len() {
            self.data.push(new_r);
        } else {
            self.data.set(iu, new_r);
        }
    }

    fn restore_overlay(
        &mut self,
        diff_log: &Vec<(T, I)>,
        lo: usize,
        hi: usize,
    ) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        // Backward replay of [lo, hi). Inherently per-element for this store: every
        // write re-encodes through `into_repr` (which is also the tag-clear), so a
        // raw memcpy of `T` values would skip the tagging and be WRONG here.
        //
        // The pairs are BORROWED from the hot tail when the range lives there,
        // which on the restore path it always does for a live log (empty cold
        // tier): zero allocation, zero copy, production's shape (design doc
        // restore-from-compressed-frames-goal.md #1/#4). Only a range dipping
        // into sealed cold frames materializes, and that is off the live path.
        let sl = vstd::slice::slice_subrange(diff_log.as_slice(), lo, hi);

            proof {
                assert(sl@ =~= diff_log@.subrange(lo as int, hi as int));
            }
            let ghost base = self.data_spec();
            let mut i: usize = hi;
            while i > lo
                invariant
                    lo <= i <= hi,
                    hi <= diff_log@.len(),
                    sl@ == diff_log@.subrange(lo as int, hi as int),
                    self.wf_spec(),
                    self.data@.len() == base.len(),
                    self.data_spec() == crate::vec::overlay::<T, I>(
                        base, diff_log@, i as int, hi as int),
                    forall|j: int| 0 <= j < self.captured_spec().len()
                        && #[trigger] self.captured_spec()[j]
                        ==> old(self).captured_spec()[j],
                    forall|j: int| 0 <= j < self.captured_spec().len()
                        && #[trigger] self.captured_spec()[j]
                        ==> !crate::vec::captured_in_range::<T, I>(
                            diff_log@, i as int, hi as int, j as nat),
                decreases i,
            {
                i -= 1;
                let (v, idx) = sl[i - lo];
                proof {
                    assert(sl@[(i - lo) as int] == diff_log@[i as int]);
                }
                proof {
                    crate::vec::lemma_overlay_len::<T, I>(base, diff_log@, (i + 1) as int, hi as int);
                }
                let ghost pre_caps = self.captured_spec();
                let iu = idx.as_usize();
                if iu < self.data.len() {
                    self.data.set(iu, v.into_repr());
                }
                proof {
                    assert(self.data_spec() =~= crate::vec::overlay::<T, I>(
                        base, diff_log@, i as int, hi as int));
                    assert forall|j: int| 0 <= j < self.captured_spec().len()
                        && #[trigger] self.captured_spec()[j]
                        implies old(self).captured_spec()[j] by {
                        assert(pre_caps[j]);
                    }
                    assert forall|j: int| 0 <= j < self.captured_spec().len()
                        && #[trigger] self.captured_spec()[j]
                        implies !crate::vec::captured_in_range::<T, I>(
                            diff_log@, i as int, hi as int, j as nat) by {
                        assert(pre_caps[j]);
                        assert(j != idx.as_nat());
                        assert forall|q: int| i <= q < hi implies
                            (#[trigger] diff_log@[q]).1.as_nat() != j as nat by {
                            if q == i {
                                assert(diff_log@[q].1 == idx);
                            }
                        }
                    }
                }
            }
            proof {
                // Untracked: a tag now would be a capture now, hence one before,
                // and the untracked store had none.
                if !TRACK {
                    assert forall|j: int| 0 <= j < self.data@.len()
                        implies !(#[trigger] T::tag_of(self.data@[j])) by {
                        if T::tag_of(self.data@[j]) {
                            assert(self.captured_spec()[j]);
                            assert(old(self).captured_spec()[j]);
                        }
                    }
                }
            }

    }

    fn finish_restore(&mut self, current_frame_diffs: &[(T, I)], _saved_len: I) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        if !TRACK {
            return;
        }
        // Production protocol: set-only, O(surviving diffs). The requires
        // guarantees every flag below saved_len is already clear (the replay
        // loop cleared each written slot), so setting exactly the surviving
        // entries' slots realizes "captured iff in the slice".
        let n = self.data.len();
        let m = current_frame_diffs.len();
        let mut k: usize = 0;
        while k < m
            invariant
                TRACK,
                self.data@.len() == n,
                current_frame_diffs@.len() == m,
                k <= m,
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::repr_wf(self.data@[j]),
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::value_of(self.data@[j])
                        == T::value_of(old(self).data@[j]),
                // set so far: tag iff (was set before ∨ named by a processed entry)
                forall|j: int| 0 <= j < self.data@.len() ==>
                    #[trigger] T::tag_of(self.data@[j])
                        == (T::tag_of(old(self).data@[j])
                            || exists|kk: int| 0 <= kk < k as int
                                && (#[trigger] current_frame_diffs@[kk]).1.as_nat()
                                    == j as nat),
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
        proof {
            // Postcondition on [0, saved_len): old tag is false there (the
            // requires), so tag == named-by-some-surviving-entry.
            assert forall|i: int| 0 <= i < _saved_len.as_nat()
                implies #[trigger] self.captured_spec()[i] == (
                    exists|kk: int| 0 <= kk < current_frame_diffs@.len()
                        && (#[trigger] current_frame_diffs@[kk]).1.as_nat() == i as nat
                ) by {
                // requires (all-clear below saved_len), via the trait view.
                assert(!(crate::diff_store_ops::DiffStoreOps::<T, I, TRACK>::captured(&*old(self))[i]));
                assert(!(T::tag_of(old(self).data@[i])));
            }
        }
    }
}

impl<T, I, const TRACK: bool> DiffStore<T, I, TRACK> for InlineStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{

    proof fn lemma_wf_captured_len(&self) {}

    proof fn lemma_wf_data_len(&self) {}

    #[inline(always)]
    fn is_empty(&self) -> bool {
        self.data.as_slice().len() == 0
    }

    #[inline(always)]
    fn raw_len(&self) -> (n: usize) {
        self.data.as_slice().len()
    }

    #[inline(always)]
    fn len(&self) -> I {
        // Production's line verbatim (containers/src/diff_store.rs:246); vstd's
        // `Option::expect` spec requires `is Some`, discharged by wf.
        I::try_from_usize(self.data.as_slice().len()).expect("len overflow")
    }

    #[inline(always)]
    fn pop(&mut self) -> Option<T> {
        broadcast use crate::diff_store::lemma_inline_discipline;
        match self.data.pop() {
            Some(r) => Some(T::from_repr(&r)),
            None => None,
        }
    }

    fn unique_capture(&self) -> bool { true }

    fn needs_replayed_indices(&self) -> bool { true }

    #[inline(always)]
    fn restore_entries_clear_capture(&self) -> bool { true }

    fn restore_run(&mut self, base: I, values: &[T]) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        let b = base.as_usize();
        let n = self.data.len();
        let ghost before = self.data@;
        if b >= n {
            return;
        }
        let count = if values.len() <= n - b { values.len() } else { n - b };
        let mut q = 0usize;
        while q < count
            invariant
                b < n,
                count == if values@.len() <= n - b { values@.len() as int } else { n - b },
                q <= count,
                self.data@.len() == n,
                before.len() == n,
                self.wf_spec(),
                forall|i: int| 0 <= i < n ==>
                    T::tag_of(#[trigger] self.data@[i]) == T::tag_of(before[i]),
                forall|i: int| 0 <= i < n ==>
                    T::value_of(#[trigger] self.data@[i]) ==
                        if b <= i < b + q { values@[i - b] }
                        else { T::value_of(before[i]) },
            decreases count - q,
        {
            let i = b + q;
            let tag = T::tag(&self.data[i]);
            let mut repr = values[q].into_repr();
            if tag {
                T::set_tag(&mut repr);
            }
            self.data.set(i, repr);
            q += 1;
        }
        proof {
            assert(self.captured_spec() =~= old(self).captured_spec());
        }
    }

    fn shrink_if(&mut self, factor: usize, headroom: usize) {
        broadcast use crate::diff_store::lemma_inline_discipline;
        // Production formula: shrink capacity when `cap > factor * len`,
        // keeping `headroom * len` (see the ParallelStore helper's ledger note).
        crate::parallel_store::shrink_vec_capacity(&mut self.data, factor, headroom);
    }

}

} // verus!

// Byte reporter — OUTSIDE the verified perimeter (stratified; see
// `diagnostics.rs`). Production formula: the reprs ARE the backing.
impl<T, I> crate::diagnostics::HeapBytes for InlineStore<T, I>
where
    T: Tagged,
    I: IndexLike,
{
    fn heap_bytes(&self) -> usize {
        self.data.capacity() * core::mem::size_of::<T::Repr>()
    }
}
