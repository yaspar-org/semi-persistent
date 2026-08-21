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
///
/// `I` is the index word: it names a position and thereby bounds the collection
/// (`wf` pins `data.len() < I::max_nat()`, so the last storable element sits at
/// `I::max_spec()` and no position ever wraps). Saved frame lengths are positions
/// too, hence `frames: Vec<I>` rather than `Vec<usize>` — at a 31-bit index that
/// halves the frame stack. `usize` is the default because a container cannot know
/// its own population; a caller who knows it opts into the narrow word.
pub struct AppendOnlyVec<T, I: IndexLike = usize, const TRACK: bool = true> {
    pub(crate) data: std::vec::Vec<T>,
    pub(crate) frames: std::vec::Vec<I>,
    pub(crate) forks: ForkHistory,
    pub(crate) id: ContainerId,
    /// Ghost snapshot stack: `snapshots[k]` is `data@` as of frame `k`'s mark,
    /// i.e. the length-`frames[k]` prefix. Parallel to `frames`.
    pub(crate) snapshots: Ghost<Seq<Seq<T>>>,
}

impl<T, I: IndexLike, const TRACK: bool> AppendOnlyVec<T, I, TRACK> {
    /// The abstract contents: the data sequence.
    pub open(crate) spec fn view(&self) -> Seq<T> {
        self.data@
    }

    pub open(crate) spec fn snapshots_view(&self) -> Seq<Seq<T>> {
        self.snapshots@
    }

    /// Frame-stack depth (spec counterpart of `depth()`; fields are `pub(crate)` —
    /// privacy closeout — so public contracts phrase frame counts through this).
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.frames@.len()
    }

    /// Lifetime restore count (fork-history origins length).
    pub open(crate) spec fn fork_count_spec(&self) -> nat {
        self.forks.origins@.len()
    }

    /// Well-formedness:
    ///  - the element count fits the index word, so every position — the index
    ///    `push` returns, the length `len` reports, the frame lengths `mark`
    ///    saves — is representable in `I` and the checked conversions below are
    ///    infallible rather than merely guarded;
    ///  - snapshots and frames are parallel stacks;
    ///  - every saved length is within the current data and monotone
    ///    non-decreasing (append-only: a frame's prefix never shrinks while
    ///    live, and marks record ever-larger lengths);
    ///  - each snapshot IS the corresponding data prefix;
    ///  - the fork history is well-formed.
    pub open(crate) spec fn wf(&self) -> bool {
        let data = self.data@;
        let frames = self.frames@;
        let snaps = self.snapshots@;
        &&& data.len() < I::max_nat()
        &&& snaps.len() == frames.len()
        &&& (forall|k: int| 0 <= k < frames.len() ==>
                #[trigger] frames[k].as_nat() <= data.len())
        &&& (forall|k: int| 0 <= k && k + 1 < frames.len() ==>
                (#[trigger] frames[k]).as_nat() <= (#[trigger] frames[k + 1]).as_nat())
        &&& (forall|k: int| 0 <= k < frames.len() ==>
                #[trigger] snaps[k] == data.subrange(0, frames[k].as_nat() as int))
        &&& self.forks.wf()
    }

    /// Token validity (same as `Vec`): same container AND on the live branch
    /// path within its depth bound. The `restore` precondition.
    pub open(crate) spec fn is_token_valid_spec(&self, token: VecToken) -> bool {
        &&& token.container_id.id() == self.id.id()
        &&& crate::fork_history::fork_valid(
                self.forks.origins@,
                self.forks.current_branch_id as nat,
                self.frames@.len() as nat,
                token.branch_id as nat,
                token.depth as nat)
    }

    /// The full runtime-checkable precondition of `restore`, which is what the
    /// public `is_valid_token` answers.
    pub open(crate) spec fn is_restorable_spec(&self, token: VecToken) -> bool {
        &&& TRACK
        &&& self.is_token_valid_spec(token)
        &&& token.frame_idx < self.frames@.len()
        &&& self.frames@.len() < u32::MAX
        &&& self.forks.origins@.len() + 1 <= u32::MAX
    }

    /// Empty append-only vec.
    pub fn new() -> (v: Self)
        ensures v.wf(), v.view().len() == 0, v.snapshots_view().len() == 0,
    {
        proof { I::lemma_max_nat_positive(); }  // 0 < I::max_nat(), so empty is wf
        AppendOnlyVec {
            data: std::vec::Vec::new(),
            frames: std::vec::Vec::new(),
            forks: ForkHistory::new(),
            id: ContainerId::new(),
            snapshots: Ghost(Seq::empty()),
        }
    }

    /// Element count, as a position in `I`.
    ///
    /// The `expect` is discharged by `wf`'s `data.len() < I::max_nat()` clause, so
    /// this cannot fail for a well-formed vec — the same protocol as
    /// `InlineStore::len` (`inline_store.rs`), and the reason `push` guards the
    /// *new* length rather than the returned index.
    pub fn len(&self) -> (n: I)
        requires self.wf(),
        ensures n.as_nat() == self.view().len(),
    {
        I::try_from_usize(self.data.len()).expect("len overflow")
    }

    pub fn is_empty(&self) -> (b: bool)
        ensures b == (self.view().len() == 0),
    {
        self.data.len() == 0
    }

    pub fn get(&self, idx: I) -> (v: &T)
        ensures idx.as_nat() < self.view().len() ==> *v == self.view()[idx.as_nat() as int],
    {
        // Total-with-documented-panic: explicit bound branch.
        if !(idx.as_usize() < self.data.len()) {
            crate::guard::refuse("AppendOnlyVec::get: index out of bounds");
        }
        &self.data[idx.as_usize()]
    }

    /// Contiguous read access to all elements (production parity; also the
    /// safe replacement for egraph's `from_raw_parts` contiguity assumption).
    /// The backing store IS a `std::vec::Vec`, so the slice is the view.
    pub fn as_slice(&self) -> (r: &[T])
        ensures r@ == self.view(),
    {
        self.data.as_slice()
    }

    /// Append a value; returns its index. Existing data and every snapshot
    /// prefix are preserved (append-only), so `wf` is maintained.
    ///
    /// The capacity precondition is on the length *after* the append, not on the
    /// returned index: `wf` has to hold on exit, and it is what makes `len` and
    /// `mark` infallible. Requiring only `view().len() < I::max_nat()` would admit
    /// a final push whose successor length falls outside `I`.
    pub(crate) fn push(&mut self, val: T) -> (idx: I)
        requires
            old(self).wf(),
            old(self).view().len() + 1 < I::max_nat(),
        ensures
            final(self).wf(),
            idx.as_nat() == old(self).view().len(),
            final(self).view() == old(self).view().push(val),
            final(self).snapshots_view() == old(self).snapshots_view(),
    {
        let idx = I::try_from_usize(self.data.len()).expect(
            "append-only vec is full for its index word",
        );
        self.data.push(val);
        proof {
            let data = self.data@;
            let old_data = old(self).data@;
            assert(data == old_data.push(val));
            // Each old frame length <= old_data.len() <= data.len(), and the
            // prefix [0, frames[k]) is unchanged by the append.
            assert forall|k: int| 0 <= k < self.frames@.len() implies
                #[trigger] self.snapshots@[k] == data.subrange(0, self.frames@[k].as_nat() as int)
            by {
                assert(old(self).snapshots@[k]
                    == old_data.subrange(0, self.frames@[k].as_nat() as int));
                assert(self.frames@[k].as_nat() <= old_data.len());
                assert(data.subrange(0, self.frames@[k].as_nat() as int)
                    =~= old_data.subrange(0, self.frames@[k].as_nat() as int));
            }
        }
        idx
    }

    /// Current depth (number of live marks).
    pub fn depth(&self) -> (d: usize)
        ensures d == self.depth_spec(),
    {
        self.frames.len()
    }

    /// How many more `restore`s this container can accept before the
    /// fork-history branch counter saturates `u32` (saturating at 0). While
    /// `> 0`, `restore`'s `origins.len() + 1 <= u32::MAX` precondition holds.
    pub fn restores_remaining(&self) -> (r: usize)
        requires self.wf(),
        ensures
            self.fork_count_spec() < u32::MAX ==>
                r as nat == (u32::MAX - self.fork_count_spec()) as nat,
            self.fork_count_spec() >= u32::MAX ==> r == 0,
    {
        let used = self.forks.origins.len();
        (u32::MAX as usize).saturating_sub(used)
    }

    /// Mark: save the current length, returning a token. The new frame records
    /// `data.len()` (>= every prior frame, since data only grew), keeping
    /// `frames` monotone.
    pub(crate) fn mark(&mut self, shrink: ShrinkPolicy) -> (token: VecToken)
        requires
            old(self).wf(),
            // Production permits marks only when tracking is enabled.
            TRACK,
            old(self).depth_spec() < u32::MAX,
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            token.frame_idx_spec() == old(self).depth_spec(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).snapshots_view() == old(self).snapshots_view().push(old(self).view()),
    {
        crate::guard::check_precondition(TRACK, "mark() called on untracked AppendOnlyVec");
        crate::guard::check_precondition(
            self.frames.len() < u32::MAX as usize,
            "AppendOnlyVec::mark: frame-stack depth would overflow u32",
        );

        // Capacity reclamation, production's AppendOnlyVec variant:
        // condition `cap > len * factor + headroom` (vs Vec's
        // `cap > factor * len`), target `len + headroom`. Observably inert
        // (external_body helper: capacity is unmodeled; contract = element
        // sequence unchanged).
        match shrink {
            ShrinkPolicy::Never => {}
            ShrinkPolicy::IfOverallocated { factor, headroom } => {
                shrink_aov_capacity(&mut self.data, factor, headroom);
            }
        }

        let token_branch = self.forks.current_branch();
        let token_depth = self.frames.len() as u32;
        let token_container = self.id;

        // The saved length is a position, so it is stored as `I`; the conversion
        // is infallible by `wf`.
        let saved_len = I::try_from_usize(self.data.len()).expect("len overflow");
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
                (#[trigger] frames[k]).as_nat() <= (#[trigger] frames[k + 1]).as_nat() by {
                if k + 1 < new_top {
                } else {
                    assert(frames[k].as_nat() <= data.len());
                    assert(frames[k + 1].as_nat() == saved_len.as_nat() == data.len());
                }
            }
            // snapshots: new top is the full current data prefix; old ones
            // unchanged (data unchanged by mark).
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] snaps[k] == data.subrange(0, frames[k].as_nat() as int) by {
                if k < new_top {
                    assert(old(self).snapshots@[k]
                        == data.subrange(0, frames[k].as_nat() as int));
                } else {
                    assert(snaps[new_top] == old_view);
                    assert(frames[new_top].as_nat() == data.len());
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

    // ------------------------------------------------------------------
    // Total-operation shell, matching Vec's pattern.
    // ------------------------------------------------------------------

    /// Exec counterpart of `push`'s capacity precondition.
    pub fn can_push(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.view().len() + 1 < I::max_nat()),
    {
        let n = self.data.len();
        let cap = <I as crate::index_like::IndexLike>::max().as_usize();
        proof {
            <I as crate::index_like::IndexLike>::lemma_max_nat_positive();
            <I as crate::index_like::IndexLike>::lemma_max_as_nat();
            <I as crate::index_like::IndexLike>::lemma_max_nat_fits_usize();
            assert(cap as nat == I::max_nat() - 1);
        }
        n < cap
    }

    /// Total push: refuses at the index word's capacity, returns the new
    /// element's index on success.
    pub fn try_push(&mut self, val: T) -> (r: Result<I, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(idx) ==> idx.as_nat() == old(self).view().len()
                && final(self).view() == old(self).view().push(val),
            r is Err ==> final(self).view() == old(self).view(),
            final(self).snapshots_view() == old(self).snapshots_view(),
            r matches Err(e) ==> e == crate::error::ContainerError::CapacityExhausted,
    {
        if self.can_push() {
            Ok(self.push(val))
        } else {
            Err(crate::error::ContainerError::CapacityExhausted)
        }
    }

    /// Total mark: the error names which precondition failed.
    pub fn try_mark(&mut self, shrink: ShrinkPolicy)
        -> (r: Result<VecToken, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(token) ==> {
                &&& final(self).view() == old(self).view()
                &&& token.frame_idx_spec() == old(self).depth_spec()
                &&& final(self).depth_spec() == old(self).depth_spec() + 1
                &&& final(self).snapshots_view()
                    == old(self).snapshots_view().push(old(self).view())
            },
            r is Err ==> final(self).view() == old(self).view()
                && final(self).depth_spec() == old(self).depth_spec()
                && final(self).snapshots_view() == old(self).snapshots_view(),
    {
        if !TRACK {
            return Err(crate::error::ContainerError::Untracked);
        }
        if !(self.frames.len() < (u32::MAX as usize)) {
            return Err(crate::error::ContainerError::DepthLimit);
        }
        Ok(self.mark(shrink))
    }

    /// Total restore: `is_valid_token` answers exactly "would `restore`
    /// succeed right now", so the wrapper is the check.
    pub fn try_restore(&mut self, token: VecToken)
        -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r is Ok ==> final(self).view()
                == old(self).snapshots_view()[token.frame_idx_spec() as int]
                && final(self).depth_spec() == token.frame_idx_spec()
                && final(self).snapshots_view()
                    == old(self).snapshots_view().subrange(0, token.frame_idx_spec() as int),
            r is Err ==> final(self).view() == old(self).view()
                && final(self).depth_spec() == old(self).depth_spec()
                && final(self).snapshots_view() == old(self).snapshots_view(),
    {
        if self.is_valid_token(&token) {
            self.restore(token);
            Ok(())
        } else {
            Err(crate::error::ContainerError::InvalidToken)
        }
    }

    /// The public token-validity check. True iff `restore(token)` would
    /// succeed at this moment. Borrows the token, matching production.
    pub fn is_valid_token(&self, token: &VecToken) -> (b: bool)
        requires self.wf(),
        ensures b == self.is_restorable_spec(*token),
    {
        if !TRACK {
            return false;
        }
        let same_container = token.container_id.eq(self.id);
        if !same_container {
            return false;
        }
        if token.frame_idx >= self.frames.len() {
            return false;
        }
        if self.frames.len() >= u32::MAX as usize {
            return false;
        }
        if self.forks.origins.len() >= u32::MAX as usize {
            return false;
        }
        let cur_depth = self.frames.len() as u32;
        self.forks.is_valid(token.branch_id, token.depth, cur_depth)
    }

    /// Restore to the state the token names: truncate `data` to the saved
    /// length and the frame/snapshot stacks to the target, then record the
    /// branch cut. Reproduces `snapshots[token.frame_idx]` exactly.
    pub(crate) fn restore(&mut self, token: VecToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).is_token_valid_spec(token),
            token.frame_idx_spec() < old(self).depth_spec(),
            old(self).depth_spec() < u32::MAX,
            old(self).fork_count_spec() + 1 <= u32::MAX,
        ensures
            final(self).wf(),
            final(self).view() == old(self).snapshots_view()[token.frame_idx_spec() as int],
            final(self).depth_spec() == token.frame_idx_spec(),
            final(self).snapshots_view() == old(self).snapshots_view().subrange(0, token.frame_idx_spec() as int),
    {
        // Check the full restorable predicate, mirroring the proven requires
        // for unverified callers, before reading
        // frames[token.frame_idx] or mutating anything. Production message
        // parity for the token cases.
        crate::guard::check_precondition(TRACK, "restore() called on untracked AppendOnlyVec");
        crate::guard::check_precondition(
            token.container_id.eq(self.id),
            "token belongs to a different container",
        );
        crate::guard::check_precondition(
            token.frame_idx < self.frames.len(),
            "token points beyond frame stack",
        );
        crate::guard::check_precondition(
            self.frames.len() < u32::MAX as usize,
            "AppendOnlyVec::restore: frame-stack depth would overflow u32",
        );
        crate::guard::check_precondition(
            self.forks.origins.len() < u32::MAX as usize,
            "AppendOnlyVec::restore: fork history exhausted (too many restores)",
        );
        crate::guard::check_precondition(
            {
                let cur_depth = self.frames.len() as u32;
                self.forks.is_valid(token.branch_id, token.depth, cur_depth)
            },
            "invalid token (abandoned future)",
        );

        let target = token.frame_idx;
        let saved_len = self.frames[target].as_usize();

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
                #[trigger] frames[k].as_nat() <= data.len() by {
                assert(frames[k] == old_frames[k]);
                assert(k < target);
                // old monotone: frames[k] <= old_frames[target] == saved_len.
                lemma_aov_frames_le(old_frames, k, target as int);
            }
            assert forall|k: int| 0 <= k < frames.len() implies
                #[trigger] snaps[k] == data.subrange(0, frames[k].as_nat() as int) by {
                assert(snaps[k] == old_snaps[k]);
                assert(old_snaps[k] == old_data.subrange(0, frames[k].as_nat() as int));
                lemma_aov_frames_le(old_frames, k, target as int);
                assert(frames[k].as_nat() <= saved_len);
                // data == old_data prefix [0,saved_len); for m < frames[k] <= saved_len
                // the two prefixes agree.
                assert(data.subrange(0, frames[k].as_nat() as int)
                    =~= old_data.subrange(0, frames[k].as_nat() as int));
            }
        }
    }
}

/// In a monotone non-decreasing frame-length sequence, `frames[k] <=
/// frames[j]` for `k <= j`. (Used to bound a surviving frame by the restore
/// target's saved length.)
pub(crate) proof fn lemma_aov_frames_le<I: IndexLike>(frames: Seq<I>, k: int, j: int)
    requires
        0 <= k <= j < frames.len(),
        forall|a: int| 0 <= a && a + 1 < frames.len() ==>
            (#[trigger] frames[a]).as_nat() <= (#[trigger] frames[a + 1]).as_nat(),
    ensures
        frames[k].as_nat() <= frames[j].as_nat(),
    decreases j - k,
{
    if k < j {
        lemma_aov_frames_le(frames, k, j - 1);
        assert(0 <= (j - 1) && (j - 1) + 1 < frames.len());
        assert(frames[(j - 1)].as_nat() <= frames[(j - 1) + 1].as_nat());  // trigger at a = j-1
    }
}

/// AppendOnlyVec capacity-only shrink: production's variant condition
/// `cap > len * factor + headroom`, target `len + headroom`. `external_body`
/// because Verus does not model `Vec::capacity`/`shrink_to`; trusted contract
/// = element sequence unchanged. Trust ledger: group B.
#[verifier::external_body]
fn shrink_aov_capacity<T>(data: &mut Vec<T>, factor: usize, headroom: usize)
    ensures final(data)@ == old(data)@,
{
    if data.capacity() > data.len().saturating_mul(factor).saturating_add(headroom) {
        data.shrink_to(data.len().saturating_add(headroom));
    }
}

} // verus!

// ---------------------------------------------------------------------------
// Trusted glue (outside verus!{}; trust ledger group E): iteration delegates
// 1:1 to the verified `as_slice` (whose contract proves the slice IS the
// view), then uses std's slice iterator. Read-only — the append-only
// invariant (no mutation of existing elements) is structurally unbreachable
// from a `&self` iterator.
// ---------------------------------------------------------------------------

impl<T, I: IndexLike, const TRACK: bool> AppendOnlyVec<T, I, TRACK> {
    /// Iterate over the elements in insertion order (production parity).
    #[inline(always)]
    pub fn iter(&self) -> core::slice::Iter<'_, T> {
        self.as_slice().iter()
    }
}

// Production-surface parity impls (production derives/ships these).
impl<T, I: IndexLike, const TRACK: bool> core::fmt::Debug for AppendOnlyVec<T, I, TRACK> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AppendOnlyVec")
            .field("len", &self.len().as_usize())
            .field("depth", &self.depth())
            .finish()
    }
}

impl<T, I: IndexLike, const TRACK: bool> Default for AppendOnlyVec<T, I, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}
