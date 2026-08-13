// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `ParallelStore<T, I>`: SoA layout with a parallel capture-flag bit-vector.
//!
//! The capture flags live in a packed [`CaptureBits`](crate::capture_bits) — a
//! `Vec<u64>` with one bit per slot, like production's bitset, for cache
//! density (8× less memory than a `Vec<bool>`). `CaptureBits` exposes a
//! `Seq<bool>` view, so the `captured()` spec is literally that view and the
//! `DiffStore` proof is identical to the one a `Vec<bool>` backing would give:
//! the packed representation is verified separately and is non-observable here.
//!
//! Implements `DiffStore<T, I, TRACK>` for any `T: Copy` and `I: IndexLike`.
//! No `Tagged` requirement — the capture bit lives outside the value type.

use vstd::prelude::*;

use crate::capture_bits::CaptureBits;
use crate::diff_store::DiffStore;
use crate::index_like::IndexLike;

verus! {

/// Parallel-bitset DiffStore.
///
/// Invariant (via `wf`): `data@.len() == captured@.len()`. Push, pop, set,
/// truncate maintain this invariant by mirroring the operation on both
/// stores. `set_raw` only touches `data`. The capture protocol touches
/// `captured` (and the diff log) without disturbing `data`.
///
/// The capture flags live in a packed [`CaptureBits`] (a `Vec<u64>` bit-vector,
/// 1 bit/slot — 8× less memory than a `Vec<bool>`); its `Seq<bool>` view means
/// the `captured()` spec and all the proofs over it are unchanged.
pub struct ParallelStore<T, I>
where
    T: Sized + Copy,
    I: IndexLike,
{
    pub(crate) data: Vec<T>,
    pub(crate) captured: CaptureBits,
    pub(crate) _phantom: core::marker::PhantomData<I>,
}

impl<T, I> ParallelStore<T, I>
where
    T: Sized + Copy,
    I: IndexLike,
{
    /// Spec twins (privacy closeout): the open trait-impl spec fns delegate
    /// here so they contain no direct field access.
    pub open(crate) spec fn data_spec(&self) -> Seq<T> {
        self.data@
    }

    /// The abstract capture flags: the LAZY bit-vector's padded view at the
    /// data length (see capture_bits.rs — `false` beyond materialized
    /// words). `data.push` therefore extends this sequence with `false` at
    /// ZERO exec cost; `tail_clear` (in `wf`) is what makes that sound.
    pub open(crate) spec fn captured_spec(&self) -> Seq<bool> {
        self.captured.flags(self.data@.len() as int)
    }

    pub open(crate) spec fn wf_spec_at<const TRACK: bool>(&self) -> bool {
        // tail_clear is only load-bearing under TRACK (it is what makes the
        // free flag-sequence extension sound); an untracked store's flags
        // are dead and unconstrained — production parity.
        &&& (TRACK ==> crate::capture_bits::tail_clear(
                self.captured.words_view(), self.data@.len() as int))
        &&& self.data@.len() < I::max_nat()
    }
}

impl<T, I, const TRACK: bool> DiffStore<T, I, TRACK> for ParallelStore<T, I>
where
    T: Sized + Copy,
    I: IndexLike,
{
    open spec fn data(&self) -> Seq<T> { self.data_spec() }
    open spec fn captured(&self) -> Seq<bool> { self.captured_spec() }
    open spec fn wf(&self) -> bool { self.wf_spec_at::<TRACK>() }

    proof fn lemma_wf_captured_len(&self) {}

    #[inline(always)]
    fn is_empty(&self) -> bool {
        self.data.len() == 0
    }

    fn raw_len(&self) -> (n: usize) {
        self.data.len()
    }

    #[inline(always)]
    fn len(&self) -> I {
        // Production's line verbatim (containers/src/diff_store.rs:95). vstd
        // specs `Option::expect` with `requires option is Some`, which `wf()`
        // discharges (`data().len() < I::max_nat()`), so no hand-written dead
        // arm is needed — and an unverified caller who overflowed still traps
        // here, at production's trap point with production's message.
        I::try_from_usize(self.data.len()).expect("len overflow")
    }

    #[inline(always)]
    fn get(&self, i: I) -> T {
        self.data[i.as_usize()]
    }

    #[inline(always)]
    fn push(&mut self, value: T) {
        // Production parity: ONE line. The abstract captured() extends with
        // `false` for free — the fresh position is beyond the old length,
        // where tail_clear pins every materialized bit to zero and the
        // padding reads zero.
        self.data.push(value);
        proof {
            if TRACK {
                assert(self.captured_spec() =~= old(self).captured_spec().push(false));
            }
        }
    }

    #[inline(always)]
    fn pop(&mut self) -> Option<T> {
        let r = self.data.pop();
        if TRACK && r.is_some() {
            // Retire the vanished position's flag so tail_clear holds at the
            // shorter length. A pure bounds-check branch while nothing is
            // materialized — the entire TRACK=false lifetime.
            self.captured.clear_bit(self.data.len());
            proof {
                let new_len = self.data@.len() as int;
                // tail_clear at new_len: position new_len was just cleared;
                // positions > new_len were tail-clear at old_len == new_len+1.
                assert forall|k: int| new_len <= k
                    && #[trigger] (k / 64) < self.captured.words_view().len()
                    implies !crate::capture_bits::spec_bit(
                        self.captured.words_view(), k) by {
                    if k == new_len {
                        assert(!crate::capture_bits::padded_bit(
                            self.captured.words_view(), k));
                    } else {
                        // k >= old_len: pre-pop tail_clear pinned it false,
                        // and clear_bit preserved every other position.
                        assert(crate::capture_bits::padded_bit(
                            self.captured.words_view(), k)
                            == crate::capture_bits::padded_bit(
                                old(self).captured.words_view(), k));
                        assert(!crate::capture_bits::padded_bit(
                            old(self).captured.words_view(), k));
                    }
                }
                assert(self.captured_spec() =~= old(self).captured_spec().drop_last());
            }
        }
        r
    }

    #[inline(always)]
    fn set_raw(&mut self, i: I, value: T) {
        let iu = i.as_usize();
        self.data.set(iu, value);
    }

    fn truncate(&mut self, len: I) {
        let lu = len.as_usize();
        self.data.truncate(lu);
        if TRACK {
            self.captured.retire_from(lu);
            proof {
                assert(self.captured_spec()
                    =~= old(self).captured_spec().subrange(0, len.as_nat() as int));
            }
        }
    }

    #[inline(always)]
    fn mark_captured(&mut self, i: I) {
        if TRACK {
            let iu = i.as_usize();
            self.captured.set_true(iu, Ghost(self.data@.len() as int));
            proof {
                assert(self.captured_spec()
                    =~= old(self).captured_spec().update(i.as_nat() as int, true));
            }
        }
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
        // Truncate if longer (retiring the suffix flags keeps tail_clear).
        if self.data.len() > target {
            self.data.truncate(target);
            self.captured.retire_from(target);
        }
        // Grow with defaults if shorter: the flags extend with `false` for
        // free (tail_clear on the growing region).
        while self.data.len() < target
            invariant
                TRACK ==> crate::capture_bits::tail_clear(
                    self.captured.words_view(), self.data@.len() as int),
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
                // flags: shared prefix preserved (truncate/retire touched only
                // >= target; growth doesn't touch words), grown region false
                // (tail_clear at every intermediate length).
                TRACK ==> forall|j: int| 0 <= j < self.data@.len()
                    ==> #[trigger] crate::capture_bits::padded_bit(
                            self.captured.words_view(), j)
                        == (j < shared
                            && crate::capture_bits::padded_bit(
                                old(self).captured.words_view(), j)),
            decreases target - self.data.len(),
        {
            self.data.push(T::default());
        }
    }

    fn prepare_mark(&mut self, _saved_len: I, _prev_diffs: &[(T, I)]) {
        if !TRACK {
            return;
        }
        // Production's protocol verbatim (diff_store.rs:118-127): zero the
        // materialized words in place, then bulk-resize to cover the data
        // length. The eager resize keeps `set_true` off the word-growth path
        // during the frame's writes — see `CaptureBits::zero_and_materialize`.
        // O(words), a vectorizable memset.
        self.captured.zero_and_materialize(self.data.len());
    }

    #[inline(always)]
    fn capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>) {
        if !TRACK {
            return;
        }
        let iu = i.as_usize();
        let su = saved_len.as_usize();
        if iu >= su {
            return;
        }
        if !self.captured.get(iu) {
            let old_val = self.data[iu];
            diff_log.push((old_val, i));
            self.captured.set_true(iu, Ghost(self.data@.len() as int));
        }
        proof {
            // Postcondition bridge: the padded flags at the (unchanged) data
            // length changed at exactly iu (or not at all).
            if i.as_nat() < saved_len.as_nat() && !old(self).captured_spec()[i.as_nat() as int] {
                assert(self.captured_spec()
                    =~= old(self).captured_spec().update(i.as_nat() as int, true));
            } else {
                assert(self.captured_spec() =~= old(self).captured_spec());
            }
        }
    }

    fn force_capture(&mut self, i: I, saved_len: I, diff_log: &mut Vec<(T, I)>) {
        if !TRACK {
            return;
        }
        let iu = i.as_usize();
        let su = saved_len.as_usize();
        if iu >= su {
            return;
        }
        let old_val = self.data[iu];
        diff_log.push((old_val, i));
        self.captured.set_true(iu, Ghost(self.data@.len() as int));
        proof {
            assert(self.captured_spec()[i.as_nat() as int] == true);
        }
    }

    fn begin_restore(&mut self, _replayed_diffs: &[(T, I)]) {
        if !TRACK {
            return;
        }
        // The wholesale bitmap zero, hoisted before the replay (production
        // pays the identical memset inside finish_restore; doing it first
        // lets restore_entry stay bit-free). The named-slots slice is not
        // needed — the zero is total.
        self.captured.zero_all();
    }

    // NOTE: already inlined into `Vec::restore`'s replay loop by LLVM (verified
    // in the disassembly — there is no call in the loop), so `inline(always)`
    // here measures as a no-op. The residual restore delta is register spilling
    // in that loop, not this call; see `doc/design/11-layout-parity.md`.
    fn restore_entry(&mut self, index: I, old_value: &T, target_saved_len: I) {
        let iu = index.as_usize();
        let tsl = target_saved_len.as_usize();
        if iu >= tsl {
            return;
        }
        if iu >= self.data.len() {
            // Pre-pad case: a previous restore_entry in this loop pushed up
            // to but not past iu (contract: iu == data.len()). NO bit work —
            // the extended flag reads false (tail_clear at the old length),
            // preserving decrease-only.
            self.data.push(*old_value);
            proof {
                if TRACK {
                    assert(!crate::capture_bits::padded_bit(
                        self.captured.words_view(), iu as int));
                    assert forall|k: int| self.data@.len() as int <= k
                        && #[trigger] (k / 64) < self.captured.words_view().len()
                        implies !crate::capture_bits::spec_bit(
                            self.captured.words_view(), k) by {
                        assert(!crate::capture_bits::padded_bit(
                            old(self).captured.words_view(), k));
                    }
                }
            }
        } else {
            // Data write only (production parity): the bitmap was zeroed in
            // begin_restore and data writes never touch it.
            self.data.set(iu, *old_value);
        }
    }

    fn finish_restore(&mut self, current_frame_diffs: &[(T, I)], _saved_len: I) {
        if !TRACK {
            return;
        }
        // Set-only: the all-clear requires (established by begin_restore +
        // the flag-free replay) makes the survivor pass sufficient — and
        // saves the second wholesale zero production performs here (it
        // zeroes in BOTH prepare_mark and finish_restore; we zero once, in
        // begin_restore).
        proof {
            // all-false start for the loop invariant, from the requires
            // (which covers [0, saved_len) == [0, captured().len())).
            DiffStore::<T, I, TRACK>::lemma_wf_captured_len(&*self);
        }

        // Step 2: rebuild from the surviving diffs. Invariant: an in-bounds
        // slot j is flagged iff some processed entry (kk < k) points at j.
        // Out-of-bounds entries are dropped by the guard and excluded from
        // the existential.
        let n = self.data.len();
        let m = current_frame_diffs.len();
        let mut k: usize = 0;
        while k < m
            invariant
                self.data@ == old(self).data@,
                n == self.data@.len(),
                current_frame_diffs@.len() == m,
                k <= m,
                crate::capture_bits::tail_clear(
                    self.captured.words_view(), self.data@.len() as int),
                forall|j: int| 0 <= j < n as int ==>
                    #[trigger] self.captured.flags(n as int)[j] == (
                        exists|kk: int|
                            0 <= kk < k as int
                                && (#[trigger] current_frame_diffs@[kk]).1.as_nat() == j as nat
                    ),
            decreases (m - k) as int,
        {
            let ghost pre_words = self.captured.words_view();
            let ghost k0 = k as int;
            proof {
                // Pin the entry invariant on the snapshot before mutating.
                assert forall|j: int| 0 <= j < n as int implies
                    #[trigger] crate::capture_bits::flags_of(pre_words, n as int)[j] == (
                        exists|kk: int|
                            0 <= kk < k0
                                && (#[trigger] current_frame_diffs@[kk]).1.as_nat() == j as nat
                    ) by {
                    assert(self.captured.flags(n as int)[j]
                        == crate::capture_bits::flags_of(pre_words, n as int)[j]);
                }
            }
            let idx = current_frame_diffs[k].1;
            let iu = idx.as_usize();
            if iu < n {
                self.captured.set_true(iu, Ghost(n as int));
            }
            k += 1;
            proof {
                // The k-step existential extension: entry k0 either flagged a
                // new in-bounds j == iu, or was dropped (out of bounds).
                let target = idx.as_nat() as int;
                assert forall|j: int| 0 <= j < n as int implies
                    #[trigger] self.captured.flags(n as int)[j] == (
                        exists|kk: int|
                            0 <= kk < k as int
                                && (#[trigger] current_frame_diffs@[kk]).1.as_nat() == j as nat
                    ) by {
                    // Pointwise flag change from set_true's ensures (or no-op).
                    let flag_now = crate::capture_bits::padded_bit(
                        self.captured.words_view(), j);
                    let flag_pre = crate::capture_bits::padded_bit(pre_words, j);
                    if (iu as int) < n as int {
                        assert(flag_now == if j == iu as int { true } else { flag_pre });
                    } else {
                        assert(flag_now == flag_pre);
                    }
                    // Old invariant at j, via the pinned snapshot fact:
                    assert(crate::capture_bits::flags_of(pre_words, n as int)[j] == flag_pre);
                    assert(flag_pre == (
                        exists|kk: int|
                            0 <= kk < k0
                                && (#[trigger] current_frame_diffs@[kk]).1.as_nat() == j as nat));
                    if flag_now {
                        // Forward: witness is either the old one or kk == k0.
                        if (iu as int) < n as int && j == iu as int {
                            assert(current_frame_diffs@[k0].1.as_nat() == j as nat);
                            assert(0 <= k0 < k as int);
                        } else {
                            let kk0 = choose|kk: int|
                                0 <= kk < k0
                                    && (#[trigger] current_frame_diffs@[kk]).1.as_nat()
                                        == j as nat;
                            assert(0 <= kk0 < k as int);
                        }
                    } else {
                        // Backward: no witness below k, in particular not k0.
                        assert forall|kk: int| 0 <= kk < k as int implies
                            (#[trigger] current_frame_diffs@[kk]).1.as_nat() != j as nat by {
                            if kk == k0 {
                                // entry k0 pointing at j would have flagged j
                                // (in-bounds since j < n).
                                if current_frame_diffs@[kk].1.as_nat() == j as nat {
                                    assert(target == j);
                                    assert((iu as int) == target);
                                    assert((iu as int) < n as int);
                                    assert(flag_now);  // contradiction
                                }
                            }
                        }
                    }
                }
            }
        }

        // The postcondition restricts j to [0, saved_len) ⊆ [0, n); on that
        // prefix the loop invariant IS the postcondition (any entry pointing
        // below saved_len is automatically in-bounds).
    }

    fn shrink_if(&mut self, factor: usize, headroom: usize) {
        // Production formula (containers/src/diff_store.rs:192-197): shrink the
        // data capacity when overallocated by `factor`, keeping `headroom * len`,
        // THEN truncate the capture words to `data.capacity().div_ceil(64)`.
        // external_body helper: capacity is unmodeled by Verus; the contract
        // is data-preservation (trust ledger group B — same class as
        // heap_bytes, but contract-carrying).
        shrink_vec_capacity(&mut self.data, factor, headroom);
        // Reclaim capture words that no longer cover any live slot. Production
        // does this in the same branch; omitting it left the word vector at a
        // permanent high-water mark, so a shrunk verus store kept strictly more
        // memory than the production one it is supposed to match.
        //
        // The argument is `data_capacity_bits()` (post-shrink), NOT `len`: the
        // slots between `len` and capacity are live storage that `push` can
        // reoccupy without re-materializing words, exactly as in production.
        // Every flag below that bound is preserved, so `captured()` — which is
        // read at logical length `len <= capacity` — is unchanged, and the
        // store's `wf`/`captured` obligations transfer untouched.
        let keep = data_capacity_bits(&self.data);
        self.captured.truncate_words_for(keep);
    }

    fn as_slice(&self) -> (r: Option<&[T]>) {
        Some(self.data.as_slice())
    }

    #[verifier::external_body]
    fn heap_bytes(&self) -> usize {
        // Production formula (containers/src/diff_store.rs): data capacity
        // plus the capture bit-vector's word capacity. external_body
        // (capacity is unmodeled and the diagnostic sum carries no spec;
        // read-only). Trust ledger: group B.
        self.data.capacity() * core::mem::size_of::<T>() + self.captured.heap_bytes()
    }
}

/// Capacity-only shrink: if `cap > factor * len`, `shrink_to(headroom * len)`.
/// `external_body` because Verus does not model `Vec::capacity`/`shrink_to`;
/// the trusted contract is exactly "the element sequence is unchanged" (the
/// std-documented behavior of `shrink_to`). Trust ledger: group B.
#[verifier::external_body]
pub(crate) fn shrink_vec_capacity<T>(data: &mut Vec<T>, factor: usize, headroom: usize)
    ensures final(data)@ == old(data)@,
{
    if data.capacity() > factor.saturating_mul(data.len()) {
        data.shrink_to(headroom.saturating_mul(data.len()));
    }
}

/// How many logical slots the data vector's allocation currently covers.
/// `external_body` for the same reason as `shrink_vec_capacity`: `capacity()`
/// is unmodeled. The trusted contract is `>= data.len()`, which is what makes
/// the capture-word truncation invisible to `captured()` — every flag a caller
/// can still observe sits below `len <= capacity`. Trust ledger: group B.
#[verifier::external_body]
pub(crate) fn data_capacity_bits<T>(data: &Vec<T>) -> (n: usize)
    ensures n >= data@.len(),
{
    data.capacity()
}


impl<T, I> ParallelStore<T, I>
where
    T: Sized + Copy,
    I: IndexLike,
{
    /// A fresh, empty store: no data, no capture flags. Well-formed for any
    /// `TRACK` (the parallel store's `wf` doesn't depend on it).
    // prod-parity: no `TRACK` const generic (un-inferable through
    // `Vec::with_store`; production's `new()` is bare). Empty ⟹ wf for both
    // `TRACK` values, so the ensures is stated for each.
    pub fn new() -> (s: ParallelStore<T, I>)
        ensures
            DiffStore::<T, I, false>::wf(&s),
            DiffStore::<T, I, true>::wf(&s),
            DiffStore::<T, I, false>::data(&s).len() == 0,
            DiffStore::<T, I, true>::data(&s).len() == 0,
            DiffStore::<T, I, false>::captured(&s).len() == 0,
            DiffStore::<T, I, true>::captured(&s).len() == 0,
    {
        proof { I::lemma_max_nat_positive(); }  // 0 < I::max_nat()
        ParallelStore { data: Vec::new(), captured: CaptureBits::new(), _phantom: core::marker::PhantomData }
    }
}

// prod-parity: `Default` = the empty store — production parity
// (`containers/src/diff_store.rs:58`).
impl<T: Sized + Copy, I: IndexLike> core::default::Default for ParallelStore<T, I> {
    fn default() -> (s: ParallelStore<T, I>) {
        ParallelStore::new()
    }
}

} // verus!
