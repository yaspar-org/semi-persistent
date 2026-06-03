// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Vec<T, I, S, const TRACK: bool>`: the headline semi-persistent vector.
//!
//! M3a (already landed): scaffold — push, set, get, view. No mark/restore.
//!
//! M3b (this milestone): single-frame `mark` and `restore`, plus `pop`.
//! Proves the headline correctness theorem
//!
//!     view() == snapshots[token.frame_idx]
//!
//! after restore, where `snapshots: Seq<Seq<T>>` is a ghost stack of deep
//! copies recorded at each `mark()`. M3b restricts to a single live frame
//! at a time — no nested marks. M4 will lift that.
//!
//! Branch-cut safety (M5) is not enforced yet: M3b's `restore` accepts any
//! token whose `frame_idx` is in range. M5 adds `ContainerId` + `ForkHistory`.
//!
//! ## Invariant (M3b, single frame)
//!
//! Production calls this "first-write-wins": each captured slot appears in
//! the diff log at most once, with its pre-frame value. The clean spec-side
//! statement is **pointwise**:
//!
//!   For each `j < saved_len`:
//!     if `(old, j) ∈ diff_log` for some entry, then `snapshots[0][j] == old`;
//!     otherwise                                    `snapshots[0][j] == view[j]`.
//!
//! That is: `snapshots[0]` is reconstructed by overlaying the diff entries
//! onto the current view. Recursion-free, no `replay_reverse` to chase.
//!
//! Plus two structural conditions:
//!   - every diff entry idx is `< saved_len` (no out-of-frame entries);
//!   - first-write-wins: distinct entries point at distinct indices.

use vstd::prelude::*;

use crate::diff_store::DiffStore;
use crate::frame::Frame;
use crate::index_like::IndexLike;

verus! {

/// Opaque token returned by `mark()`. M3b carries only `frame_idx`; M5
/// will add container_id + branch_id + depth.
#[derive(Copy, Clone)]
pub struct VecToken {
    pub frame_idx: usize,
}

/// Spec helper: there is some entry in `diffs` pointing at index `j`.
pub open spec fn diff_has_index<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
    j: nat,
) -> bool {
    exists|k: int| 0 <= k < diffs.len()
        && (#[trigger] diffs[k]).1.as_nat() == j
}

/// Spec helper: the value of `j` recorded in `diffs` (pre-frame value).
/// Defined only when `diff_has_index(diffs, j)`; else `arbitrary()`.
/// First-write-wins ensures uniqueness, so `choose` picks the only entry.
pub open spec fn diff_value_at<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
    j: nat,
) -> T {
    let k = choose|k: int| 0 <= k < diffs.len()
        && (#[trigger] diffs[k]).1.as_nat() == j;
    diffs[k].0
}

/// First-write-wins: each index appears at most once.
pub open spec fn diffs_unique_indices<T, I: IndexLike>(
    diffs: Seq<(T, I)>,
) -> bool {
    forall|i: int, j: int|
        0 <= i < diffs.len() && 0 <= j < diffs.len() && i != j
            ==> (#[trigger] diffs[i]).1.as_nat() != (#[trigger] diffs[j]).1.as_nat()
}

/// Pointwise reconstruction of the snapshot from view + diffs.
///
/// `reconstruct(view, diffs)[j]` =
///   diff_value_at(diffs, j)  if diff_has_index(diffs, j)
///   view[j]                  otherwise
pub open spec fn reconstruct<T, I: IndexLike>(
    view: Seq<T>,
    diffs: Seq<(T, I)>,
    saved_len: nat,
) -> Seq<T> {
    Seq::new(saved_len, |j: int|
        if diff_has_index::<T, I>(diffs, j as nat) {
            diff_value_at::<T, I>(diffs, j as nat)
        } else if 0 <= j && (j as nat) < view.len() {
            view[j]
        } else {
            arbitrary()
        }
    )
}

/// Semi-persistent vector parameterized by storage backend `S` and index
/// type `I`. `TRACK` compiles out all tracking when false.
pub struct Vec<T, I, S, const TRACK: bool>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    pub store: S,
    pub diff_log: std::vec::Vec<(T, I)>,
    pub frames: std::vec::Vec<Frame<I>>,
    pub phantom: core::marker::PhantomData<(T, I)>,
    /// Ghost stack of deep copies. `snapshots[k]` is `view()` at the
    /// moment frame `k` was pushed. Always `snapshots.len() == frames.len()`.
    pub snapshots: Ghost<Seq<Seq<T>>>,
}

impl<T, I, S, const TRACK: bool> Vec<T, I, S, TRACK>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// Public spec view: the abstract sequence of stored values.
    pub open spec fn view(&self) -> Seq<T> {
        self.store.data()
    }

    /// Snapshot stack (ghost).
    pub open spec fn snapshots_view(&self) -> Seq<Seq<T>> {
        self.snapshots@
    }

    /// Well-formedness. M3b invariants:
    ///   - snapshots.len() == frames.len()           (parallel stacks)
    ///   - frames.len() <= 1                          (single frame for now)
    ///   - frames.len() == 0 ==> diff_log is empty   (no orphan diff entries)
    ///   - if frames.len() == 1:
    ///       saved_len <= view.len()
    ///       diff_start == 0
    ///       every diff entry idx is < saved_len    (in-bounds diffs only)
    ///       diff entries have unique indices       (first-write-wins)
    ///       snapshots[0] == reconstruct(view, diff_log, saved_len)
    pub open spec fn wf(&self) -> bool {
        &&& self.store.wf()
        &&& self.snapshots@.len() == self.frames@.len()
        &&& self.frames@.len() <= 1
        &&& (self.frames@.len() == 0 ==> self.diff_log@.len() == 0)
        &&& (self.frames@.len() == 1 ==> {
                let f = self.frames@[0];
                &&& f.diff_start == 0
                &&& f.saved_len.as_nat() <= self.view().len()
                &&& (forall|k: int| 0 <= k < self.diff_log@.len() ==>
                        (#[trigger] self.diff_log@[k]).1.as_nat() < f.saved_len.as_nat())
                &&& diffs_unique_indices::<T, I>(self.diff_log@)
                &&& self.snapshots@[0]
                    == reconstruct::<T, I>(self.view(), self.diff_log@, f.saved_len.as_nat())
            })
    }

    pub fn len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.view().len(),
    {
        self.store.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() == 0),
    {
        self.store.is_empty()
    }

    pub fn get(&self, i: I) -> (v: T)
        requires
            self.wf(),
            i.as_nat() < self.view().len(),
        ensures v == self.view()[i.as_nat() as int],
    {
        self.store.get(i)
    }

    pub fn push(&mut self, value: T)
        requires
            old(self).wf(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            self.wf(),
            self.view() == old(self).view().push(value),
            self.snapshots_view() == old(self).snapshots_view(),
    {
        self.store.push(value);
        // The wf invariant in the frame=1 case requires
        //   snapshots[0] == reconstruct(view, diff_log, saved_len)
        // After push: diff_log and saved_len unchanged; view extended by one.
        // For each j < saved_len:
        //   - if diff_has_index(diff_log, j): reconstruct[j] = diff_value_at(diff_log, j),
        //     unchanged from old.
        //   - else: reconstruct[j] = view[j]. Since saved_len <= old.view().len(),
        //     the prefix view[0..saved_len] is identical pre/post push.
        // Hence reconstruct is unchanged. wf re-establishes by extensionality.
        proof {
            if self.frames@.len() == 1 {
                let f = self.frames@[0];
                let saved_len = f.saved_len.as_nat();
                let old_recon = reconstruct::<T, I>(old(self).view(), self.diff_log@, saved_len);
                let new_recon = reconstruct::<T, I>(self.view(), self.diff_log@, saved_len);
                assert(old_recon =~= new_recon);
            }
        }
    }

    pub fn pop(&mut self) -> (r: Option<T>)
        requires
            old(self).wf(),
            // No live frames: pop in tracked mode after a mark would need
            // force_capture, which lives behind the M3b precondition that
            // pop is only callable when the frame stack is empty (or the
            // popped slot is beyond saved_len). For M3b, simplest is to
            // require no live frames.
            old(self).frames@.len() == 0,
        ensures
            self.wf(),
            old(self).view().len() == 0 ==> r is None && self.view() == old(self).view(),
            old(self).view().len() > 0 ==> {
                &&& r is Some
                &&& r->Some_0 == old(self).view()[old(self).view().len() - 1]
                &&& self.view() == old(self).view().drop_last()
            },
            self.snapshots_view() == old(self).snapshots_view(),
    {
        self.store.pop()
    }

    pub fn set(&mut self, i: I, value: T)
        requires
            old(self).wf(),
            i.as_nat() < old(self).view().len(),
            // M3b: `set` only modifies untracked slots or those already
            // captured. To keep the proof simple, restrict to the no-live-
            // frame case for now. A capturing set lands in M4.
            old(self).frames@.len() == 0,
        ensures
            self.wf(),
            self.view() == old(self).view().update(i.as_nat() as int, value),
            self.snapshots_view() == old(self).snapshots_view(),
    {
        self.store.set_raw(i, value);
    }

    /// Mark a snapshot point. Returns a token that can be passed to
    /// `restore` to roll back to the current state.
    ///
    /// M3b: only one live mark at a time. The precondition rejects nested
    /// marks; M4 will lift that.
    pub fn mark(&mut self) -> (token: VecToken)
        requires
            old(self).wf(),
            old(self).frames@.len() == 0,
        ensures
            self.wf(),
            self.view() == old(self).view(),
            token.frame_idx == 0,
            self.frames@.len() == 1,
            self.snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        let saved_len = self.store.len();
        self.store.prepare_mark(saved_len, self.diff_log.as_slice());

        let view_now: Ghost<Seq<T>> = Ghost(self.view());
        self.snapshots = Ghost(self.snapshots@.push(view_now@));

        self.frames.push(Frame { saved_len, diff_start: 0 });

        // Establish wf for the new frame. With diff_log empty (wf
        // precondition for frames.len() == 0), reconstruct just reads
        // view[j] for every j < saved_len, which is exactly view (since
        // saved_len == view.len()). So snapshots[0] = view = reconstruct.
        proof {
            let saved_len_nat = saved_len.as_nat();
            let recon = reconstruct::<T, I>(self.view(), self.diff_log@, saved_len_nat);
            assert(recon =~= self.view());
        }

        VecToken { frame_idx: 0 }
    }

    /// Restore the vector to the state captured by `token`.
    ///
    /// M3b: only single-frame restore. After restore:
    ///   - view() equals the snapshot taken at the corresponding `mark()`.
    ///   - the snapshot stack is truncated to `token.frame_idx`.
    pub fn restore(&mut self, token: VecToken)
        requires
            old(self).wf(),
            token.frame_idx < old(self).frames@.len(),
        ensures
            self.wf(),
            self.view() == old(self).snapshots_view()[token.frame_idx as int],
            self.frames@.len() == token.frame_idx as nat,
            self.snapshots_view() == old(self).snapshots_view().subrange(0, token.frame_idx as int),
    {
        let target_index = token.frame_idx;
        let target_frame = self.frames[target_index];
        let saved_len = target_frame.saved_len;
        let diff_start = target_frame.diff_start;

        // Capture pre-state. snapshots[0] equals reconstruct(pre_view,
        // pre_diffs, saved_len) by the wf invariant.
        let pre_view: Ghost<Seq<T>> = Ghost(self.view());
        let pre_diffs: Ghost<Seq<(T, I)>> = Ghost(self.diff_log@);
        let snap0: Ghost<Seq<T>> = Ghost(self.snapshots@[target_index as int]);

        self.store.truncate(saved_len);

        // Loop invariant. Walk i from n down to diff_start; the suffix
        // [i, n) has been applied. For j < saved_len, j is "fully restored"
        // iff no entry in [diff_start, i) points at j — equivalently, all
        // entries pointing at j (if any) have been processed.
        //
        // Two sub-cases when no entry in [diff_start, i) points at j:
        //   (a) j has an entry in [i, n): we already applied it, so
        //       data[j] = the entry's old value = snap0[j] (by reconstruct).
        //   (b) j has no entry anywhere in diff_log: data[j] never changed
        //       from pre_view[j]; since saved_len <= pre_view.len() and
        //       reconstruct fell through to view[j], data[j] = snap0[j].
        let n = self.diff_log.len();
        let mut i: usize = n;
        while i > diff_start
            invariant
                self.store.wf(),
                self.diff_log@ == pre_diffs@,
                self.diff_log@.len() == n,
                diff_start <= i <= n,
                self.store.data().len() == saved_len.as_nat(),
                saved_len.as_nat() <= pre_view@.len(),
                forall|k: int| 0 <= k < self.diff_log@.len() ==>
                    (#[trigger] self.diff_log@[k]).1.as_nat() < saved_len.as_nat(),
                diffs_unique_indices::<T, I>(self.diff_log@),
                snap0@ == reconstruct::<T, I>(pre_view@, pre_diffs@, saved_len.as_nat()),
                // Pointwise correctness: any j whose entry has already been
                // processed (or never had one) is now at its snapshot value.
                forall|j: int| #![trigger self.store.data()[j]]
                    0 <= j < saved_len.as_nat()
                    && !(exists|k: int| diff_start <= k < (i as int)
                            && (#[trigger] self.diff_log@[k]).1.as_nat() == j as nat)
                        ==> self.store.data()[j] == snap0@[j],
            decreases i,
        {
            i -= 1;
            let (old_val, idx) = self.diff_log[i];
            self.store.restore_entry(idx, &old_val, saved_len);
        }

        // After the loop: i == diff_start. With diff_start == 0, the
        // "still to be applied" set is empty, so every j is restored.
        self.diff_log.truncate(diff_start);
        self.frames.truncate(target_index);
        self.snapshots = Ghost(self.snapshots@.subrange(0, target_index as int));
    }
}


} // verus!
