// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Push-only semi-persistent vector (verified).
//!
//! `mark` saves the current length; `restore` truncates back to it. There is
//! NO diff log — data is never overwritten, only appended. So the snapshot a
//! frame names is literally a length-prefix of the current data:
//! `snapshots[k] == data[0 .. frames[k]]`, and restore just truncates `data`
//! to `frames[target]`, reproducing `snapshots[target]` exactly.
//!
//! Reuses the verified `ForkHistory` (branch-cut safety) and `ContainerId`
//! (cross-container rejection) unchanged — `restore` requires the same
//! `is_token_valid_spec` validity precondition as `Vec::restore`, and records
//! the cut via `forks.fork(...)`.

use vstd::prelude::*;

verus! {

use crate::container_id::ContainerId;
use crate::fork_history::ForkHistory;
use crate::index_like::IndexLike;
use crate::vec::{ShrinkPolicy, VecToken};

/// Push-only vec with semi-persistent mark/restore.
pub struct AppendOnlyVec<T, const TRACK: bool> {
    pub data: std::vec::Vec<T>,
    pub frames: std::vec::Vec<usize>,
    pub forks: ForkHistory,
    pub id: ContainerId,
    /// Ghost snapshot stack: `snapshots[k]` is `data@` as of frame `k`'s mark,
    /// i.e. the length-`frames[k]` prefix. Parallel to `frames`.
    pub snapshots: Ghost<Seq<Seq<T>>>,
}

impl<T, const TRACK: bool> AppendOnlyVec<T, TRACK> {
    /// The abstract contents: the data sequence.
    pub open spec fn view(&self) -> Seq<T> {
        self.data@
    }

    pub open spec fn snapshots_view(&self) -> Seq<Seq<T>> {
        self.snapshots@
    }

    /// Well-formedness:
    ///  - snapshots and frames are parallel stacks;
    ///  - every saved length is within the current data and monotone
    ///    non-decreasing (append-only: a frame's prefix never shrinks while
    ///    live, and marks record ever-larger lengths);
    ///  - each snapshot IS the corresponding data prefix;
    ///  - the fork history is well-formed.
    pub open spec fn wf(&self) -> bool {
        let data = self.data@;
        let frames = self.frames@;
        let snaps = self.snapshots@;
        &&& snaps.len() == frames.len()
        &&& (forall|k: int| 0 <= k < frames.len() ==> #[trigger] frames[k] <= data.len())
        &&& (forall|k: int| 0 <= k && k + 1 < frames.len() ==>
                #[trigger] frames[k] <= #[trigger] frames[k + 1])
        &&& (forall|k: int| 0 <= k < frames.len() ==>
                #[trigger] snaps[k] == data.subrange(0, frames[k] as int))
        &&& self.forks.wf()
    }

    /// Token validity (same as `Vec`): same container AND on the live branch
    /// path within its depth bound. The `restore` precondition.
    pub open spec fn is_token_valid_spec(&self, token: VecToken) -> bool {
        &&& token.container_id.id() == self.id.id()
        &&& crate::fork_history::fork_valid(
                self.forks.origins@,
                self.forks.current_branch_id as nat,
                self.frames@.len() as nat,
                token.branch_id as nat,
                token.depth as nat)
    }

    /// Empty append-only vec.
    pub fn new() -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        AppendOnlyVec {
            data: std::vec::Vec::new(),
            frames: std::vec::Vec::new(),
            forks: ForkHistory::new(),
            id: ContainerId::new(),
            snapshots: Ghost(Seq::empty()),
        }
    }

    pub fn len(&self) -> (n: usize)
        ensures n == self.view().len(),
    {
        self.data.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        ensures b == (self.view().len() == 0),
    {
        self.data.len() == 0
    }

    pub fn get(&self, idx: usize) -> (v: &T)
        requires idx < self.view().len(),
        ensures *v == self.view()[idx as int],
    {
        &self.data[idx]
    }

    /// Append a value; returns its index. Existing data and every snapshot
    /// prefix are preserved (append-only), so `wf` is maintained.
    pub fn push(&mut self, val: T) -> (idx: usize)
        requires old(self).wf(),
        ensures
            self.wf(),
            idx == old(self).view().len(),
            self.view() == old(self).view().push(val),
            self.snapshots_view() == old(self).snapshots_view(),
    {
        let idx = self.data.len();
        self.data.push(val);
        proof {
            let data = self.data@;
            let old_data = old(self).data@;
            assert(data == old_data.push(val));
            // Each old frame length <= old_data.len() <= data.len(), and the
            // prefix [0, frames[k]) is unchanged by the append.
            assert forall|k: int| 0 <= k < self.frames@.len() implies
                #[trigger] self.snapshots@[k] == data.subrange(0, self.frames@[k] as int)
            by {
                assert(old(self).snapshots@[k] == old_data.subrange(0, self.frames@[k] as int));
                assert(self.frames@[k] <= old_data.len());
                assert(data.subrange(0, self.frames@[k] as int)
                    =~= old_data.subrange(0, self.frames@[k] as int));
            }
        }
        idx
    }

    /// Current depth (number of live marks).
    pub fn depth(&self) -> (d: usize)
        ensures d == self.frames@.len(),
    {
        self.frames.len()
    }

    /// How many more `restore`s this container can accept before the
    /// fork-history branch counter saturates `u32` (saturating at 0). While
    /// `> 0`, `restore`'s `origins.len() + 1 <= u32::MAX` precondition holds.
    pub fn restores_remaining(&self) -> (r: usize)
        requires self.wf(),
        ensures
            self.forks.origins@.len() < u32::MAX ==>
                r as nat == (u32::MAX - self.forks.origins@.len()) as nat,
            self.forks.origins@.len() >= u32::MAX ==> r == 0,
    {
        let used = self.forks.origins.len();
        (u32::MAX as usize).saturating_sub(used)
    }

    /// Mark: save the current length, returning a token. The new frame records
    /// `data.len()` (>= every prior frame, since data only grew), keeping
    /// `frames` monotone.
    pub fn mark(&mut self, _shrink: ShrinkPolicy) -> (token: VecToken)
        requires
            old(self).wf(),
            old(self).frames@.len() < u32::MAX,
        ensures
            self.wf(),
            self.view() == old(self).view(),
            token.frame_idx == old(self).frames@.len(),
            self.frames@.len() == old(self).frames@.len() + 1,
            self.snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        let token_branch = self.forks.current_branch();
        let token_depth = self.frames.len() as u32;
        let token_container = self.id;

        let saved_len = self.data.len();
        let ghost old_view = self.view();
        let ghost old_frames = self.frames@;

        self.frames.push(saved_len);
        self.snapshots = Ghost(self.snapshots@.push(old_view));

        proof {
            let data = self.data@;
            let frames = self.frames@;
            let snaps = self.snapshots@;
            let new_top = (frames.len() - 1) as int;
            assert(frames[new_top] == saved_len);
            assert(forall|k: int| 0 <= k < old_frames.len() ==> frames[k] == old_frames[k]);
            // monotone: only the new adjacency (old top, new) to check;
            // old top <= old_data.len() == saved_len == frames[new_top].
            assert forall|k: int| 0 <= k && k + 1 < frames.len() implies
                #[trigger] frames[k] <= #[trigger] frames[k + 1] by {
                if k + 1 < new_top {
                } else {
                    assert(frames[k] <= data.len());
                    assert(frames[k + 1] == saved_len == data.len());
                }
            }
            // snapshots: new top is the full current data prefix; old ones
            // unchanged (data unchanged by mark).
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] snaps[k] == data.subrange(0, frames[k] as int) by {
                if k < new_top {
                    assert(old(self).snapshots@[k] == data.subrange(0, frames[k] as int));
                } else {
                    assert(snaps[new_top] == old_view);
                    assert(frames[new_top] == data.len());
                    assert(old_view =~= data.subrange(0, data.len() as int));
                }
            }
        }

        VecToken {
            frame_idx: self.frames.len() - 1,
            branch_id: token_branch,
            depth: token_depth,
            container_id: token_container,
        }
    }

    /// Token validity check (parity with production `is_valid_token`).
    pub fn is_valid_token(&self, token: VecToken) -> (b: bool)
        requires self.wf(), self.frames@.len() < u32::MAX,
        ensures b == self.is_token_valid_spec(token),
    {
        let same_container = token.container_id.eq(self.id);
        if !same_container {
            return false;
        }
        let cur_depth = self.frames.len() as u32;
        self.forks.is_valid(token.branch_id, token.depth, cur_depth)
    }

    /// Restore to the state the token names: truncate `data` to the saved
    /// length and the frame/snapshot stacks to the target, then record the
    /// branch cut. Reproduces `snapshots[token.frame_idx]` exactly.
    pub fn restore(&mut self, token: VecToken)
        requires
            old(self).wf(),
            old(self).is_token_valid_spec(token),
            token.frame_idx < old(self).frames@.len(),
            old(self).frames@.len() < u32::MAX,
            old(self).forks.origins@.len() + 1 <= u32::MAX,
        ensures
            self.wf(),
            self.view() == old(self).snapshots_view()[token.frame_idx as int],
            self.frames@.len() == token.frame_idx as nat,
            self.snapshots_view() == old(self).snapshots_view().subrange(0, token.frame_idx as int),
    {
        // Runtime guards (overflow): a verified caller proves the two u32
        // bounds; an unverified one is trapped before `fork`'s `as u32` cast on
        // the fork-history counters would silently wrap. `origins.len()` is the
        // lifetime restore count (never reclaimed); `frames.len()` the live
        // nesting depth.
        crate::guard::check_precondition(
            self.frames.len() < u32::MAX as usize,
            "AppendOnlyVec::restore: frame-stack depth would overflow u32",
        );
        crate::guard::check_precondition(
            self.forks.origins.len() < u32::MAX as usize,
            "AppendOnlyVec::restore: fork history exhausted (too many restores)",
        );

        let target = token.frame_idx;
        let saved_len = self.frames[target];

        let ghost old_data = self.data@;
        let ghost old_frames = self.frames@;
        let ghost old_snaps = self.snapshots@;
        let ghost forks_origins0 = self.forks.origins@;
        let ghost forks_branch0 = self.forks.current_branch_id;

        // Establish fork()'s precondition (branch <= origins.len()) from
        // validity, while self is pristine.
        proof {
            crate::fork_history::lemma_fork_valid_characterization(
                self.forks.origins@, self.forks.current_branch_id as nat,
                self.frames@.len() as nat, token.branch_id as nat, token.depth as nat);
            crate::fork_history::lemma_reaches_in_range(
                self.forks.origins@, self.forks.current_branch_id as nat,
                token.branch_id as nat);
            assert(token.branch_id as nat <= forks_origins0.len());
            // target frame length, for the result.
            assert(old_snaps[target as int] == old_data.subrange(0, saved_len as int));
            assert(saved_len <= old_data.len());
        }

        self.data.truncate(saved_len);
        self.frames.truncate(target);
        self.snapshots = Ghost(self.snapshots@.subrange(0, target as int));

        proof {
            assert(self.forks.origins@ == forks_origins0);
            assert(self.forks.current_branch_id == forks_branch0);
            assert(token.branch_id as nat <= self.forks.origins@.len());
        }
        self.forks.fork(token.branch_id, token.depth);

        proof {
            let data = self.data@;
            let frames = self.frames@;
            let snaps = self.snapshots@;
            // view == old data prefix [0, saved_len) == old snapshot[target].
            assert(data =~= old_data.subrange(0, saved_len as int));
            assert(data =~= old_snaps[target as int]);
            assert(snaps =~= old_snaps.subrange(0, target as int));
            assert(frames =~= old_frames.subrange(0, target as int));
            // wf of the truncated stacks: prefixes of the old (still-valid)
            // facts; each surviving frame's length <= saved_len == data.len(),
            // and its prefix is unchanged by the data truncation.
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] frames[k] <= data.len() by {
                assert(frames[k] == old_frames[k]);
                assert(k < target);
                // old monotone: frames[k] <= old_frames[target] == saved_len.
                lemma_aov_frames_le(old_frames, k, target as int);
            }
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] snaps[k] == data.subrange(0, frames[k] as int) by {
                assert(snaps[k] == old_snaps[k]);
                assert(old_snaps[k] == old_data.subrange(0, frames[k] as int));
                lemma_aov_frames_le(old_frames, k, target as int);
                assert(frames[k] <= saved_len);
                // data == old_data prefix [0,saved_len); for m < frames[k] <= saved_len
                // the two prefixes agree.
                assert(data.subrange(0, frames[k] as int)
                    =~= old_data.subrange(0, frames[k] as int));
            }
        }
    }
}

/// In a monotone non-decreasing frame-length sequence, `frames[k] <=
/// frames[j]` for `k <= j`. (Used to bound a surviving frame by the restore
/// target's saved length.)
pub proof fn lemma_aov_frames_le(frames: Seq<usize>, k: int, j: int)
    requires
        0 <= k <= j < frames.len(),
        forall|a: int| 0 <= a && a + 1 < frames.len() ==>
            #[trigger] frames[a] <= #[trigger] frames[a + 1],
    ensures
        frames[k] <= frames[j],
    decreases j - k,
{
    if k < j {
        lemma_aov_frames_le(frames, k, j - 1);
        assert(0 <= (j - 1) && (j - 1) + 1 < frames.len());
        assert(frames[(j - 1)] <= frames[(j - 1) + 1]);  // trigger at a = j-1
    }
}

} // verus!
