// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Shared branch history for hard-synced vectors (`doc/design/10-shared-fork-history.md`).
//!
//! `N` vectors that always `mark`/`restore` together share one `ForkHistory` and
//! one mark depth instead of each carrying an identical copy. `History` owns the
//! genealogy and depth; it is passed `&mut` to members per call and never stored
//! inside one, so there is no shared mutable aliasing for Verus. This module is
//! the extracted genealogy type (doc 10, step 1); the history-less `Vec` and the
//! `Solo`/`SyncGroup` wrappers build on it.

// Extracted genealogy type (doc 10, step 1); wired into `Vec`/`Solo`/`SyncGroup`
// in later steps, so its methods are not yet called.
#![allow(dead_code)]

use crate::diff_store::DiffStore;
use crate::index_like::IndexLike;
use crate::vec::Vec as SpVec;
use vstd::prelude::*;

verus! {

/// A version token for a synced group: the generation stamp minted at mark time
/// and the mark depth. Drops `VecToken`'s per-vector `container_id` — one token
/// names the whole group's version, validated once by `History`.
#[derive(Clone, Copy, Debug)]
pub struct GroupToken {
    pub(crate) generation: u64,
    pub(crate) depth: u32,
}

impl GroupToken {
    /// The mark depth this token names (public spec accessor; the raw fields stay
    /// crate-private so a token cannot be forged field-by-field outside).
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.depth as nat
    }

    /// Exec twin of `depth_spec`: the consumer restores every member to this
    /// depth after validating the token against the group's `History`.
    pub fn depth(&self) -> (d: u32)
        ensures d as nat == self.depth_spec(),
    {
        self.depth
    }
}

/// The shared depth-indexed generation stamps and mark depth for a synced group.
/// One instance backs all members, so the fork history is held `×1` instead of
/// `×N` — and, unlike the old append-only `origins` (which grew one entry per
/// restore, never reclaimed, O(R)), the stamp array is O(max depth): the leak fix
/// (doc 10). A token minted at depth `d` carries `stamps.stamp_at(d)`; a restore
/// diverging at `d` bumps the deeper levels, O(1)-invalidating the abandoned
/// future via `lemma_bump_invalidates`.
pub struct History {
    pub(crate) stamps: crate::gen_stamps::GenStamps,
    pub(crate) depth: u32,
}

impl History {
    /// Every live depth has a stamp level (so a live token's depth is in range).
    pub open(crate) spec fn wf(self) -> bool {
        self.stamps.levels@.len() >= self.depth as nat
    }

    pub open(crate) spec fn depth_spec(self) -> nat {
        self.depth as nat
    }

    /// Validity of `t`: its generation still matches the live stamp at its depth
    /// (O(1)). The shared analogue of `Vec::is_token_valid_spec`, minus the
    /// container check (one history, one group).
    pub open(crate) spec fn valid_spec(self, t: GroupToken) -> bool {
        self.stamps.valid(t.depth as nat, t.generation)
    }

    pub fn new() -> (r: History)
        ensures
            r.wf(),
            r.depth_spec() == 0,
    {
        History { stamps: crate::gen_stamps::GenStamps::new(0), depth: 0 }
    }

    pub fn depth(&self) -> (d: u32)
        ensures d as nat == self.depth_spec(),
    {
        self.depth
    }

    /// Open a new mark: mint the generation for the current depth (growing the
    /// stamp array the first time a depth is reached), then depth advances by one.
    /// The token is immediately valid.
    pub fn mark(&mut self) -> (t: GroupToken)
        requires
            old(self).wf(),
            old(self).depth_spec() < u32::MAX as nat,
        ensures
            final(self).wf(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            t.depth_spec() == old(self).depth_spec(),
            final(self).valid_spec(t),
    {
        let d = self.depth;
        let g = self.stamps.stamp_at(d as usize);
        self.depth = d + 1;
        GroupToken { generation: g, depth: d }
    }

    /// Is `t` valid — does its generation still match the live stamp at its depth?
    /// Computed once for the whole group (versus `N` identical walks today), O(1).
    pub fn is_valid(&self, t: GroupToken) -> (r: bool)
        requires self.wf(),
        ensures r == self.valid_spec(t),
    {
        self.stamps.is_valid(t.depth as usize, t.generation)
    }

    /// Heap bytes of the genealogy (diagnostic; no spec content). O(max depth).
    /// The H4b.3 measurement reads this: one shared instance versus the
    /// per-member `GenStamps` every column used to carry.
    pub fn heap_bytes(&self) -> usize {
        self.stamps.heap_bytes()
    }

    /// Restore to `t`: bump the levels strictly below `t.depth` (invalidating the
    /// abandoned future — every token at depth `> t.depth` — while `t` and its
    /// ancestors stay valid), and set the depth to the token's. O(1) amortized;
    /// no per-restore growth. No overflow precondition: `bump_from` uses
    /// `wrapping_add`, which changes a level unconditionally.
    pub fn restore_to(&mut self, t: GroupToken)
        requires
            old(self).wf(),
            old(self).valid_spec(t),
            t.depth_spec() < old(self).depth_spec(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == t.depth_spec(),
    {
        self.stamps.bump_from((t.depth + 1) as usize);
        self.depth = t.depth;
    }
}

/// One `Vec` bundled with its own `History`: reproduces the standalone
/// `mark`/`restore` API through the shared-history primitives (the migration
/// safety net of doc 10). A `SyncGroup` is the same shape with one `History`
/// over many members; `Solo` is the `N == 1` case and the proof that
/// `push_frame`/`restore_frame` + `History` compose to the old semantics.
pub(crate) struct Solo<T, I, S, const TRACK: bool>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    pub(crate) vec: SpVec<T, I, S, TRACK>,
    pub(crate) history: History,
}

impl<T, I, S, const TRACK: bool> Solo<T, I, S, TRACK>
where
    T: Sized + Copy,
    I: IndexLike,
    S: DiffStore<T, I, TRACK>,
{
    /// The group invariant: the member's frame depth tracks the shared history's
    /// depth exactly. This is the `N == 1` case of `SyncGroup`'s invariant.
    pub open(crate) spec fn wf(self) -> bool {
        &&& self.vec.wf()
        &&& self.history.wf()
        &&& self.vec.depth_spec() == self.history.depth_spec()
    }

    pub open(crate) spec fn view(self) -> Seq<T> {
        self.vec.view()
    }

    /// Open a mark: one genealogy write in `History`, one frame push in the
    /// member. Depth advances in lockstep, so the group invariant is maintained.
    pub(crate) fn mark(&mut self, shrink: crate::vec::ShrinkPolicy) -> (t: GroupToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).vec.depth_spec() < u32::MAX,
            old(self).vec.view().len() < I::max_nat(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).view(),
            final(self).vec.depth_spec() == old(self).vec.depth_spec() + 1,
            t.depth == old(self).history.depth,
    {
        let t = self.history.mark();
        self.vec.push_frame(shrink);
        t
    }

    /// Restore to `t`: validate once in `History`, reconstruct the member via
    /// `restore_frame`, and record the branch cut in `History`. Depth drops to
    /// `t.depth` in both, so the group invariant is maintained.
    pub(crate) fn restore(&mut self, t: GroupToken)
        where T: core::default::Default
        requires
            old(self).wf(),
            TRACK,
            old(self).history.valid_spec(t),
            (t.depth as nat) < old(self).history.depth_spec(),
        ensures
            final(self).wf(),
            final(self).view() == old(self).vec.snapshots_view()[t.depth as int],
            final(self).vec.depth_spec() == t.depth as nat,
    {
        self.vec.restore_frame(t.depth as usize);
        self.history.restore_to(t);
    }
}

/// One `History` shared across two heterogeneous members — the smallest true
/// `SyncGroup`. The e-graph's hard-synced set (~10 members of different
/// `T`/`I`/`S`) is this shape with more fields: one `History`, many members, each
/// carrying only its own diff state while the branch genealogy (which grows one
/// origin per restore and is otherwise duplicated per member) lives once. The
/// fan-out generalizes field-by-field; the two-member case verifies the pattern.
pub(crate) struct SyncPair<T1, I1, S1, T2, I2, S2, const TRACK: bool>
where
    T1: Sized + Copy, I1: IndexLike, S1: DiffStore<T1, I1, TRACK>,
    T2: Sized + Copy, I2: IndexLike, S2: DiffStore<T2, I2, TRACK>,
{
    pub(crate) a: SpVec<T1, I1, S1, TRACK>,
    pub(crate) b: SpVec<T2, I2, S2, TRACK>,
    pub(crate) history: History,
}

impl<T1, I1, S1, T2, I2, S2, const TRACK: bool> SyncPair<T1, I1, S1, T2, I2, S2, TRACK>
where
    T1: Sized + Copy, I1: IndexLike, S1: DiffStore<T1, I1, TRACK>,
    T2: Sized + Copy, I2: IndexLike, S2: DiffStore<T2, I2, TRACK>,
{
    /// The group invariant: every member's frame depth equals the shared
    /// history's depth. This is the fact that lets one token name the whole
    /// group's version.
    pub open(crate) spec fn wf(self) -> bool {
        &&& self.a.wf()
        &&& self.b.wf()
        &&& self.history.wf()
        &&& self.a.depth_spec() == self.history.depth_spec()
        &&& self.b.depth_spec() == self.history.depth_spec()
    }

    /// One genealogy write, then a frame push in each member. All depths advance
    /// together, so the group invariant holds.
    pub(crate) fn mark(&mut self, shrink: crate::vec::ShrinkPolicy) -> (t: GroupToken)
        requires
            old(self).wf(),
            TRACK,
            old(self).a.depth_spec() < u32::MAX,
            old(self).a.view().len() < I1::max_nat(),
            old(self).b.view().len() < I2::max_nat(),
        ensures
            final(self).wf(),
            final(self).a.view() == old(self).a.view(),
            final(self).b.view() == old(self).b.view(),
            final(self).a.depth_spec() == old(self).a.depth_spec() + 1,
    {
        let t = self.history.mark();
        self.a.push_frame(shrink);
        self.b.push_frame(shrink);
        t
    }

    /// Validate once, reconstruct each member via `restore_frame`, record the
    /// branch cut once. All depths drop to `t.depth`, so the invariant holds.
    pub(crate) fn restore(&mut self, t: GroupToken)
        where T1: core::default::Default, T2: core::default::Default
        requires
            old(self).wf(),
            TRACK,
            old(self).history.valid_spec(t),
            (t.depth as nat) < old(self).history.depth_spec(),
        ensures
            final(self).wf(),
            final(self).a.view() == old(self).a.snapshots_view()[t.depth as int],
            final(self).b.view() == old(self).b.snapshots_view()[t.depth as int],
            final(self).a.depth_spec() == t.depth as nat,
    {
        self.a.restore_frame(t.depth as usize);
        self.b.restore_frame(t.depth as usize);
        self.history.restore_to(t);
    }
}

} // verus!
