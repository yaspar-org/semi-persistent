// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The typed external history manager (design doc 10, "Next: one external
//! manager"): `ForkHistory<M>` owns the token authority (a `History`) and
//! exactly one typed member `M`. A standalone column is a group of one
//! (`ForkHistory::new(Vec::new())`); a consumer with several columns wraps
//! them in one forwarding struct that implements [`Member`] (`Pair` is the
//! verified two-member forwarder, nestable). Typed access is `group.member`.
//!
//! Members carry no tokens: their whole versioning surface is the structural
//! protocol (`push_frame`, `restore_frame`, `reset_frame`, `pop_frame`,
//! `depth_exec`). Tokens are minted, validated and cut by the group's
//! `History`, once per mark or restore for the whole member, whatever its
//! width — the per-column provenance constant of the group-of-one columns
//! (one stamp per column per scope) disappears here.
//!
//! Misuse is refused, not undefined: a frame pushed or popped on the member
//! behind the group's back drifts its depth away from the history's, and the
//! next group `mark`/`restore`/`pop` refuses (`None`/`false`, nothing changes)
//! because the two depths disagree. The lockstep theorem is stated once, on
//! the group: after `mark` the member's depth is the history depth; after
//! `restore(t)` the member is at `t.depth + 1` with its model equal to its
//! archived model at `t.depth`.
//!
//! The dyn group of `sync_group` (`Box<dyn SyncMember>` members) is the
//! predecessor; it stays until every consumer is on this one.

use crate::diff_store::DiffStore;
use crate::history::{GroupToken, History};
use crate::vec::ShrinkPolicy;
use vstd::prelude::*;

verus! {

/// The member protocol for a typed group: what one column, one composite, or
/// one forwarding struct of columns must provide so that a `ForkHistory<M>`
/// can push a frame on it, restore it to a depth and pop its top frame.
/// Structural only — no tokens.
pub trait Member: Sized {
    /// Abstract live contents (a `Seq<T>` for a column, a tuple of the
    /// members' models for a forwarding struct).
    type Model;

    spec fn wf(&self) -> bool;

    /// Frame-stack depth; the group invariant ties it to the history depth.
    spec fn depth_spec(&self) -> nat;

    /// Structural headroom for one more frame (impl-defined, probed at runtime).
    spec fn can_push(&self) -> bool;

    spec fn model(&self) -> Self::Model;

    /// One archived model per frame, oldest first.
    spec fn archive(&self) -> Seq<Self::Model>;

    proof fn lemma_archive_depth(&self)
        requires self.wf(),
        ensures self.archive().len() == self.depth_spec();

    fn can_push_now(&self) -> (b: bool)
        requires self.wf(),
        ensures b == self.can_push();

    /// Exec depth, so the group can check lockstep at runtime (drift refusal).
    fn depth_exec(&self) -> (d: usize)
        requires self.wf(),
        ensures d as nat == self.depth_spec();

    /// Push a frame (seal the open stratum, open a fresh one). Total: refuses
    /// when `!can_push()`.
    fn push_frame(&mut self, shrink: ShrinkPolicy)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == old(self).depth_spec() + 1,
            final(self).model() == old(self).model(),
            final(self).archive() == old(self).archive().push(old(self).model());

    /// Reconstruct to the snapshot at `depth` and drop frame `depth` with
    /// everything above it (the legacy restore; the group's
    /// `restore_and_pop`). Total: refuses when `!(depth < depth_spec())`.
    fn restore_frame(&mut self, depth: usize)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == depth as nat,
            final(self).model() == old(self).archive()[depth as int],
            final(self).archive() == old(self).archive().subrange(0, depth as int);

    /// Semantics B (design doc 08 §1): reconstruct to the snapshot at `depth`
    /// and keep frame `depth` open and empty (the depth becomes `depth + 1`).
    /// Total: refuses when `!(depth < depth_spec())` or at the u32 ceiling.
    fn reset_frame(&mut self, depth: usize)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == depth as nat + 1,
            final(self).model() == old(self).archive()[depth as int],
            final(self).archive() == old(self).archive().subrange(0, depth as int + 1);

    /// Drop the open top frame, undoing it (the SMT-LIB `pop`). Total:
    /// refuses on an empty frame stack.
    fn pop_frame(&mut self)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).depth_spec() == old(self).depth_spec() - 1,
            final(self).model() == old(self).archive()[old(self).depth_spec() - 1],
            final(self).archive() == old(self).archive().subrange(0, old(self).depth_spec() - 1);
}

/// The one external history manager: owns the token authority and exactly
/// one typed member.
pub struct ForkHistory<M: Member> {
    /// Typed access to the member: `group.member.<field>` / `group.member.<op>`.
    /// Its frame stack is the group's business: a frame pushed or popped here
    /// behind the group's back is refused at the next group operation.
    pub member: M,
    pub(crate) history: History,
}

impl<M: Member> ForkHistory<M> {
    /// Lockstep: the member is well-formed and its depth is the history depth.
    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.history.wf()
        &&& self.member.wf()
        &&& self.member.depth_spec() == self.history.depth_spec()
    }

    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.history.depth_spec()
    }

    pub open(crate) spec fn valid_spec(&self, t: GroupToken) -> bool {
        self.history.valid_spec(t)
    }

    pub open(crate) spec fn model(&self) -> M::Model {
        self.member.model()
    }

    /// Spec accessors: public contracts cannot name the fields of a datatype
    /// with a crate-private field, and the preconditions they state are the
    /// two parts' own well-formedness (`history_ref().wf()`,
    /// `member_ref().wf()`) — the invariant class, not caller obligations.
    pub open(crate) spec fn history_ref(&self) -> History {
        self.history
    }

    pub open(crate) spec fn member_ref(&self) -> M {
        self.member
    }

    pub open(crate) spec fn archive(&self) -> Seq<M::Model> {
        self.member.archive()
    }

    /// Adopt a member with no open frames. Total: a member that already has
    /// frames (marks taken on its own) is refused — the group is the only
    /// authority over its frame stack.
    pub fn new(member: M) -> (r: ForkHistory<M>)
        requires member.wf(),
        ensures
            r.wf(),
            r.depth_spec() == 0,
            r.member_ref() == member,
    {
        if !(member.depth_exec() == 0) {
            crate::guard::refuse("ForkHistory::new: the member already has open frames");
        }
        ForkHistory { member, history: History::new() }
    }

    /// The runtime lockstep check (drift refusal).
    pub fn in_lockstep(&self) -> (b: bool)
        requires self.history_ref().wf(), self.member_ref().wf(),
        ensures b == (self.member_ref().depth_spec() == self.depth_spec()),
    {
        self.member.depth_exec() == self.history.depth() as usize
    }

    /// Mint a token for the current version and push a frame on the member.
    /// `None` (nothing changes) when the member has no headroom, the depth
    /// word is full, or the member drifted.
    pub fn mark(&mut self, shrink: ShrinkPolicy) -> (r: Option<GroupToken>)
        requires old(self).history_ref().wf(), old(self).member_ref().wf(),
        ensures
            final(self).history_ref().wf(),
            final(self).member_ref().wf(),
            r matches Some(t) ==> {
                &&& old(self).wf()
                &&& final(self).wf()
                &&& final(self).depth_spec() == old(self).depth_spec() + 1
                &&& t.depth_spec() == old(self).depth_spec()
                &&& final(self).valid_spec(t)
                &&& final(self).model() == old(self).model()
                &&& final(self).archive() == old(self).archive().push(old(self).model())
            },
            r is None ==> *final(self) == *old(self),
    {
        self.history.mark_member(&mut self.member, shrink)
    }

    /// Restore to the version `t` names and keep its frame open (semantics B,
    /// design doc 08 §1). `false` (nothing changes) when `t` is foreign or
    /// cut, not below the depth, at the depth ceiling, or the member drifted.
    /// On success the group is at `t.depth + 1`, `t` stays valid and can be
    /// restored to again, every token minted after it is dead, and the member
    /// holds its archived model from that mark.
    pub fn restore(&mut self, t: GroupToken) -> (r: bool)
        requires old(self).history_ref().wf(), old(self).member_ref().wf(),
        ensures
            final(self).history_ref().wf(),
            final(self).member_ref().wf(),
            r ==> {
                &&& old(self).wf()
                &&& old(self).valid_spec(t)
                &&& t.depth_spec() < old(self).depth_spec()
                &&& final(self).wf()
                &&& final(self).depth_spec() == t.depth_spec() + 1
                &&& final(self).valid_spec(t)
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] u.depth_spec() > t.depth_spec() ==> !final(self).valid_spec(u)
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] #![trigger old(self).valid_spec(u)] u.depth_spec() <= t.depth_spec()
                    ==> final(self).valid_spec(u) == old(self).valid_spec(u)
                &&& final(self).model() == old(self).archive()[t.depth_spec() as int]
                &&& final(self).archive() == old(self).archive().subrange(0, t.depth_spec() as int + 1)
            },
            !r ==> *final(self) == *old(self),
    {
        self.history.restore_member(&mut self.member, t)
    }

    /// `restore(t)` then `pop()`, fused (the SMT-LIB pop to the level below
    /// `t`; the legacy restore): the group lands at `t.depth`, `t` and every
    /// later token die, the member holds its archived model from that mark.
    /// `false` (nothing changes) on a foreign or cut token, one not below the
    /// depth, or a drifted member.
    pub fn restore_and_pop(&mut self, t: GroupToken) -> (r: bool)
        requires old(self).history_ref().wf(), old(self).member_ref().wf(),
        ensures
            final(self).history_ref().wf(),
            final(self).member_ref().wf(),
            r ==> {
                &&& old(self).wf()
                &&& old(self).valid_spec(t)
                &&& t.depth_spec() < old(self).depth_spec()
                &&& final(self).wf()
                &&& final(self).depth_spec() == t.depth_spec()
                &&& !final(self).valid_spec(t)
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] u.depth_spec() >= t.depth_spec() ==> !final(self).valid_spec(u)
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] #![trigger old(self).valid_spec(u)] u.depth_spec() < t.depth_spec()
                    ==> final(self).valid_spec(u) == old(self).valid_spec(u)
                &&& final(self).model() == old(self).archive()[t.depth_spec() as int]
                &&& final(self).archive() == old(self).archive().subrange(0, t.depth_spec() as int)
            },
            !r ==> *final(self) == *old(self),
    {
        self.history.restore_and_pop_member(&mut self.member, t)
    }

    /// Drop the open top scope (the SMT-LIB `pop`): the member undoes and
    /// drops its top frame and the scope's token dies. `false` (nothing
    /// changes) on an empty scope stack or a drifted member. (Named for the
    /// scope: a member's element `pop` reaches through the group unshadowed.)
    pub fn pop_scope(&mut self) -> (r: bool)
        requires old(self).history_ref().wf(), old(self).member_ref().wf(),
        ensures
            final(self).history_ref().wf(),
            final(self).member_ref().wf(),
            r ==> {
                &&& old(self).wf()
                &&& old(self).depth_spec() >= 1
                &&& final(self).wf()
                &&& final(self).depth_spec() == old(self).depth_spec() - 1
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] u.depth_spec() >= old(self).depth_spec() - 1
                    ==> !final(self).valid_spec(u)
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] #![trigger old(self).valid_spec(u)] u.depth_spec() < old(self).depth_spec() - 1
                    ==> final(self).valid_spec(u) == old(self).valid_spec(u)
                &&& final(self).model() == old(self).archive()[old(self).depth_spec() - 1]
                &&& final(self).archive() == old(self).archive().subrange(0, old(self).depth_spec() - 1)
            },
            !r ==> *final(self) == *old(self),
    {
        self.history.pop_member(&mut self.member)
    }

    /// The member pushed a frame itself, by a structural variant of its own
    /// (`group.member.push_frame_adaptive(..)`, say): mint its token. `None`
    /// when the member is not exactly one frame ahead.
    pub fn mint_pushed(&mut self) -> (r: Option<GroupToken>)
        requires old(self).history_ref().wf(), old(self).member_ref().wf(),
        ensures
            final(self).history_ref().wf(),
            final(self).member_ref() == old(self).member_ref(),
            r matches Some(t) ==> {
                &&& old(self).member_ref().depth_spec() == old(self).depth_spec() + 1
                &&& final(self).wf()
                &&& t.depth_spec() == old(self).depth_spec()
                &&& final(self).valid_spec(t)
            },
            r is None ==> *final(self) == *old(self),
    {
        self.history.mint_pushed_member(&self.member)
    }

    /// Does `t` name a live version of this group (minted here, not cut)?
    pub fn is_valid(&self, t: GroupToken) -> (b: bool)
        requires self.history_ref().wf(),
        ensures b == self.valid_spec(t),
    {
        self.history.is_valid(t)
    }

    /// The scope depth (the member's frame depth when in lockstep).
    pub fn depth(&self) -> (d: usize)
        requires self.history_ref().wf(),
        ensures d as nat == self.depth_spec(),
    {
        self.history.depth() as usize
    }
}

// ---------------------------------------------------------------------------
// The group operations over a borrowed member: what a consumer whose members
// live in its own struct calls (`history.mark_member(&mut columns, shrink)`),
// and what `ForkHistory<M>` delegates to. The lockstep theorem is stated
// here, once, for every member type.
// ---------------------------------------------------------------------------

impl History {
    /// Mint a token for the current version and push a frame on `m`. `None`
    /// (nothing changes on either side) when `m` has no headroom, the depth
    /// word is full, or `m` drifted away from this history's depth.
    pub fn mark_member<M: Member>(&mut self, m: &mut M, shrink: ShrinkPolicy) -> (r: Option<GroupToken>)
        requires old(self).wf(), old(m).wf(),
        ensures
            final(self).wf(),
            final(m).wf(),
            r matches Some(t) ==> {
                &&& old(m).depth_spec() == old(self).depth_spec()
                &&& final(m).depth_spec() == final(self).depth_spec()
                &&& final(self).depth_spec() == old(self).depth_spec() + 1
                &&& t.depth_spec() == old(self).depth_spec()
                &&& final(self).valid_spec(t)
                &&& final(m).model() == old(m).model()
                &&& final(m).archive() == old(m).archive().push(old(m).model())
            },
            r is None ==> *final(self) == *old(self) && *final(m) == *old(m),
    {
        if !(m.depth_exec() == self.depth() as usize) {
            return None;
        }
        if !(self.depth() < u32::MAX) {
            return None;
        }
        if !m.can_push_now() {
            return None;
        }
        let t = self.mark();
        m.push_frame(shrink);
        Some(t)
    }

    /// Mint the token for a frame the member pushed itself, by a structural
    /// variant of its own (an adaptive or options-driven push that the plain
    /// `push_frame` does not spell): the member must sit exactly one frame
    /// above this history. `None` (nothing changes) otherwise — a member
    /// further ahead has drifted.
    pub fn mint_pushed_member<M: Member>(&mut self, m: &M) -> (r: Option<GroupToken>)
        requires old(self).wf(), m.wf(),
        ensures
            final(self).wf(),
            r matches Some(t) ==> {
                &&& m.depth_spec() == old(self).depth_spec() + 1
                &&& final(self).depth_spec() == m.depth_spec()
                &&& t.depth_spec() == old(self).depth_spec()
                &&& final(self).valid_spec(t)
            },
            r is None ==> *final(self) == *old(self),
    {
        if !(self.depth() < u32::MAX) {
            return None;
        }
        if !(m.depth_exec() == self.depth() as usize + 1) {
            return None;
        }
        Some(self.mark())
    }

    /// Restore `m` to the version `t` names and keep its frame open
    /// (semantics B). `false` (nothing changes) when `t` is foreign or cut,
    /// not below the depth, at the depth ceiling, or `m` drifted.
    pub fn restore_member<M: Member>(&mut self, m: &mut M, t: GroupToken) -> (r: bool)
        requires old(self).wf(), old(m).wf(),
        ensures
            final(self).wf(),
            final(m).wf(),
            r ==> {
                &&& old(m).depth_spec() == old(self).depth_spec()
                &&& old(self).valid_spec(t)
                &&& t.depth_spec() < old(self).depth_spec()
                &&& final(m).depth_spec() == final(self).depth_spec()
                &&& final(self).depth_spec() == t.depth_spec() + 1
                &&& final(self).valid_spec(t)
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] u.depth_spec() > t.depth_spec() ==> !final(self).valid_spec(u)
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] #![trigger old(self).valid_spec(u)] u.depth_spec() <= t.depth_spec()
                    ==> final(self).valid_spec(u) == old(self).valid_spec(u)
                &&& final(m).model() == old(m).archive()[t.depth_spec() as int]
                &&& final(m).archive() == old(m).archive().subrange(0, t.depth_spec() as int + 1)
            },
            !r ==> *final(self) == *old(self) && *final(m) == *old(m),
    {
        if !(m.depth_exec() == self.depth() as usize) {
            return false;
        }
        if !self.is_valid(t) {
            return false;
        }
        if !(t.depth() < self.depth()) {
            return false;
        }
        if !(self.depth() < u32::MAX) {
            return false;
        }
        let d = t.depth() as usize;
        m.reset_frame(d);
        self.restore_to(t);
        true
    }

    /// `restore_member` then `pop_member`, fused (the SMT-LIB pop to the
    /// level below `t`; the legacy restore, on one pop core).
    pub fn restore_and_pop_member<M: Member>(&mut self, m: &mut M, t: GroupToken) -> (r: bool)
        requires old(self).wf(), old(m).wf(),
        ensures
            final(self).wf(),
            final(m).wf(),
            r ==> {
                &&& old(m).depth_spec() == old(self).depth_spec()
                &&& old(self).valid_spec(t)
                &&& t.depth_spec() < old(self).depth_spec()
                &&& final(m).depth_spec() == final(self).depth_spec()
                &&& final(self).depth_spec() == t.depth_spec()
                &&& !final(self).valid_spec(t)
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] u.depth_spec() >= t.depth_spec() ==> !final(self).valid_spec(u)
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] #![trigger old(self).valid_spec(u)] u.depth_spec() < t.depth_spec()
                    ==> final(self).valid_spec(u) == old(self).valid_spec(u)
                &&& final(m).model() == old(m).archive()[t.depth_spec() as int]
                &&& final(m).archive() == old(m).archive().subrange(0, t.depth_spec() as int)
            },
            !r ==> *final(self) == *old(self) && *final(m) == *old(m),
    {
        if !(m.depth_exec() == self.depth() as usize) {
            return false;
        }
        if !self.is_valid(t) {
            return false;
        }
        if !(t.depth() < self.depth()) {
            return false;
        }
        let d = t.depth() as usize;
        m.restore_frame(d);
        self.restore_and_pop(t);
        true
    }

    /// Drop the open top scope of `m` (the SMT-LIB pop); the scope's token
    /// dies. `false` (nothing changes) on an empty stack or a drifted `m`.
    pub fn pop_member<M: Member>(&mut self, m: &mut M) -> (r: bool)
        requires old(self).wf(), old(m).wf(),
        ensures
            final(self).wf(),
            final(m).wf(),
            r ==> {
                &&& old(m).depth_spec() == old(self).depth_spec()
                &&& old(self).depth_spec() >= 1
                &&& final(m).depth_spec() == final(self).depth_spec()
                &&& final(self).depth_spec() == old(self).depth_spec() - 1
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] u.depth_spec() >= old(self).depth_spec() - 1
                    ==> !final(self).valid_spec(u)
                &&& forall|u: GroupToken| #![trigger final(self).valid_spec(u)] #![trigger old(self).valid_spec(u)] u.depth_spec() < old(self).depth_spec() - 1
                    ==> final(self).valid_spec(u) == old(self).valid_spec(u)
                &&& final(m).model() == old(m).archive()[old(self).depth_spec() - 1]
                &&& final(m).archive() == old(m).archive().subrange(0, old(self).depth_spec() - 1)
            },
            !r ==> *final(self) == *old(self) && *final(m) == *old(m),
    {
        if !(m.depth_exec() == self.depth() as usize) {
            return false;
        }
        if !(self.depth() >= 1) {
            return false;
        }
        m.pop_frame();
        self.pop();
        true
    }
}

// ---------------------------------------------------------------------------
// Column members.
// ---------------------------------------------------------------------------

/// Every tracked tiered `Vec` is a member; its model is its contents.
impl<T, I, S, const TRACK: bool, VC> Member for crate::vec::Vec<T, I, S, TRACK, VC>
where
    T: Sized + Copy + core::default::Default,
    I: crate::index_like::IndexLike,
    S: crate::diff_store::DiffStore<T, I, TRACK>,
    VC: crate::value_compressor::ValueCompressor<T>,
{
    type Model = Seq<T>;

    open spec fn wf(&self) -> bool {
        &&& crate::vec::Vec::wf(self)
        &&& TRACK
    }

    open spec fn depth_spec(&self) -> nat {
        crate::vec::Vec::depth_spec(self)
    }

    open spec fn can_push(&self) -> bool {
        &&& TRACK
        &&& crate::vec::Vec::depth_spec(self) < u32::MAX as nat
        &&& crate::vec::Vec::view(self).len() < I::max_nat()
    }

    open spec fn model(&self) -> Seq<T> {
        crate::vec::Vec::view(self)
    }

    open spec fn archive(&self) -> Seq<Seq<T>> {
        crate::vec::Vec::snapshots_view(self)
    }

    proof fn lemma_archive_depth(&self) {
        crate::vec::Vec::lemma_snapshots_len(self);
    }

    fn can_push_now(&self) -> (b: bool) {
        let m = <I as crate::index_like::IndexLike>::max();
        proof {
            I::lemma_max_as_nat();
            m.lemma_as_nat_bounded();
            assert(crate::vec::Vec::view(self).len() == self.store.data().len());
        }
        let depth_ok = self.depth_exec() < u32::MAX as usize;
        let len_ok = self.store.raw_len() <= m.as_usize();
        TRACK && depth_ok && len_ok
    }

    fn depth_exec(&self) -> (d: usize) {
        crate::vec::Vec::depth_exec(self)
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        if !self.can_push_now() {
            crate::guard::refuse("Member::push_frame: the column cannot open another frame");
        }
        crate::vec::Vec::push_frame(self, shrink);
    }

    fn restore_frame(&mut self, depth: usize) {
        if !(depth < crate::vec::Vec::depth_exec(self)) {
            crate::guard::refuse("Member::restore_frame: depth is not below the column's");
        }
        crate::vec::Vec::restore_frame(self, depth);
    }

    fn reset_frame(&mut self, depth: usize) {
        if !(depth < crate::vec::Vec::depth_exec(self)) {
            crate::guard::refuse("Member::reset_frame: depth is not below the column's");
        }
        if !(crate::vec::Vec::depth_exec(self) < u32::MAX as usize) {
            crate::guard::refuse("Member::reset_frame: frame-stack depth at the u32 ceiling");
        }
        crate::vec::Vec::reset_frame(self, depth);
    }

    fn pop_frame(&mut self) {
        if !(crate::vec::Vec::depth_exec(self) >= 1) {
            crate::guard::refuse("Member::pop_frame: no open frame");
        }
        crate::vec::Vec::pop_frame(self);
    }
}

/// Every tracked append-only vector is a member; its model is its contents.
impl<T, I, const TRACK: bool> Member for crate::append_only_vec::AppendOnlyVec<T, I, TRACK>
where
    I: crate::index_like::IndexLike,
{
    type Model = Seq<T>;

    open spec fn wf(&self) -> bool {
        &&& crate::append_only_vec::AppendOnlyVec::wf(self)
        &&& TRACK
    }

    open spec fn depth_spec(&self) -> nat {
        crate::append_only_vec::AppendOnlyVec::depth_spec(self)
    }

    open spec fn can_push(&self) -> bool {
        &&& TRACK
        &&& crate::append_only_vec::AppendOnlyVec::depth_spec(self) < u32::MAX as nat
    }

    open spec fn model(&self) -> Seq<T> {
        crate::append_only_vec::AppendOnlyVec::view(self)
    }

    open spec fn archive(&self) -> Seq<Seq<T>> {
        crate::append_only_vec::AppendOnlyVec::snapshots_view(self)
    }

    proof fn lemma_archive_depth(&self) {
    }

    fn can_push_now(&self) -> (b: bool) {
        TRACK && self.frames.len() < u32::MAX as usize
    }

    fn depth_exec(&self) -> (d: usize) {
        self.frames.len()
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        if !(self.frames.len() < u32::MAX as usize) {
            crate::guard::refuse("Member::push_frame: the column cannot open another frame");
        }
        crate::append_only_vec::AppendOnlyVec::push_frame(self, shrink);
    }

    fn restore_frame(&mut self, depth: usize) {
        if !(depth < self.frames.len()) {
            crate::guard::refuse("Member::restore_frame: depth is not below the column's");
        }
        crate::append_only_vec::AppendOnlyVec::restore_frame(self, depth);
    }

    fn reset_frame(&mut self, depth: usize) {
        if !(depth < self.frames.len()) {
            crate::guard::refuse("Member::reset_frame: depth is not below the column's");
        }
        if !(self.frames.len() < u32::MAX as usize) {
            crate::guard::refuse("Member::reset_frame: frame-stack depth at the u32 ceiling");
        }
        crate::append_only_vec::AppendOnlyVec::reset_frame(self, depth);
    }

    fn pop_frame(&mut self) {
        if !(self.frames.len() >= 1) {
            crate::guard::refuse("Member::pop_frame: no open frame");
        }
        crate::append_only_vec::AppendOnlyVec::pop_frame(self);
    }
}

// ---------------------------------------------------------------------------
// The forwarding struct: two members in lockstep, nestable.
// ---------------------------------------------------------------------------

/// Two members driven as one: the model is the pair of models, the archive
/// the pair of archives frame by frame. Lockstep between the two is part of
/// `wf`; a consumer with `n` columns nests pairs (or writes its own
/// forwarding struct on the same pattern).
pub struct Pair<A: Member, B: Member> {
    pub a: A,
    pub b: B,
}

impl<A: Member, B: Member> Pair<A, B> {
    /// Pair two members at the same depth. Total: members out of step are
    /// refused (each frame stack is the group's business from here on).
    pub fn new(a: A, b: B) -> (r: Pair<A, B>)
        requires a.wf(), b.wf(),
        ensures r.wf(), r.a == a, r.b == b,
    {
        if !(a.depth_exec() == b.depth_exec()) {
            crate::guard::refuse("Pair::new: the two members are not at the same depth");
        }
        Pair { a, b }
    }
}

impl<A: Member, B: Member> Member for Pair<A, B> {
    type Model = (A::Model, B::Model);

    open spec fn wf(&self) -> bool {
        &&& self.a.wf()
        &&& self.b.wf()
        &&& self.a.depth_spec() == self.b.depth_spec()
    }

    open spec fn depth_spec(&self) -> nat {
        self.a.depth_spec()
    }

    open spec fn can_push(&self) -> bool {
        &&& self.a.can_push()
        &&& self.b.can_push()
    }

    open spec fn model(&self) -> (A::Model, B::Model) {
        (self.a.model(), self.b.model())
    }

    open spec fn archive(&self) -> Seq<(A::Model, B::Model)> {
        Seq::new(self.a.archive().len(), |k: int| (self.a.archive()[k], self.b.archive()[k]))
    }

    proof fn lemma_archive_depth(&self) {
        self.a.lemma_archive_depth();
    }

    fn can_push_now(&self) -> (b: bool) {
        self.a.can_push_now() && self.b.can_push_now()
    }

    fn depth_exec(&self) -> (d: usize) {
        self.a.depth_exec()
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        // Both halves are checked before either moves, so a refusal cannot
        // leave the pair out of step.
        if !self.can_push_now() {
            crate::guard::refuse("Member::push_frame: a member of the pair cannot open another frame");
        }
        let ghost pre = *self;
        proof {
            pre.a.lemma_archive_depth();
            pre.b.lemma_archive_depth();
        }
        self.a.push_frame(shrink);
        self.b.push_frame(shrink);
        proof {
            assert(self.archive() =~= pre.archive().push(pre.model()));
        }
    }

    fn restore_frame(&mut self, depth: usize) {
        if !(depth < self.a.depth_exec()) {
            crate::guard::refuse("Member::restore_frame: depth is not below the pair's");
        }
        let ghost pre = *self;
        proof {
            pre.a.lemma_archive_depth();
            pre.b.lemma_archive_depth();
        }
        self.a.restore_frame(depth);
        self.b.restore_frame(depth);
        proof {
            assert(self.archive() =~= pre.archive().subrange(0, depth as int));
        }
    }

    fn reset_frame(&mut self, depth: usize) {
        if !(depth < self.a.depth_exec()) {
            crate::guard::refuse("Member::reset_frame: depth is not below the pair's");
        }
        if !(self.a.depth_exec() < u32::MAX as usize) {
            crate::guard::refuse("Member::reset_frame: frame-stack depth at the u32 ceiling");
        }
        let ghost pre = *self;
        proof {
            pre.a.lemma_archive_depth();
            pre.b.lemma_archive_depth();
        }
        self.a.reset_frame(depth);
        self.b.reset_frame(depth);
        proof {
            assert(self.archive() =~= pre.archive().subrange(0, depth as int + 1));
        }
    }

    fn pop_frame(&mut self) {
        if !(self.a.depth_exec() >= 1) {
            crate::guard::refuse("Member::pop_frame: no open frame");
        }
        let ghost pre = *self;
        proof {
            pre.a.lemma_archive_depth();
            pre.b.lemma_archive_depth();
        }
        self.a.pop_frame();
        self.b.pop_frame();
        proof {
            assert(self.archive() =~= pre.archive().subrange(0, pre.depth_spec() - 1));
        }
    }
}

// ---------------------------------------------------------------------------
// Composite members: the composites' token-free cores drive the same protocol.
// Each model is the tuple of the composite's abstract views; each archive the
// tuple of its snapshot stacks, frame by frame.
// ---------------------------------------------------------------------------

impl<T, Idx, S, const TRACK: bool, VC, P> Member for crate::sparse_set::SparseSet<T, Idx, S, TRACK, VC, P>
where
    T: Sized + Copy + core::default::Default,
    Idx: crate::index_like::IndexLike + crate::tagged::Tagged + core::default::Default,
    S: crate::diff_store::DiffStore<T, Idx, TRACK>,
    VC: crate::value_compressor::ValueCompressor<T>,
    P: crate::store_policy::TaggedFamily<Idx, Idx, TRACK>,
{
    type Model = (Seq<T>, Seq<Idx>, Seq<Idx>);

    open spec fn wf(&self) -> bool {
        &&& crate::sparse_set::SparseSet::wf(self)
        &&& TRACK
        &&& self.dense_depth_spec() == self.sparse_depth_spec()
        &&& self.dense_depth_spec() == self.indices_depth_spec()
    }

    open spec fn depth_spec(&self) -> nat {
        self.dense_depth_spec()
    }

    open spec fn can_push(&self) -> bool {
        self.can_mark_spec()
    }

    open spec fn model(&self) -> (Seq<T>, Seq<Idx>, Seq<Idx>) {
        (self.dense_view(), self.sparse_view(), self.indices_view())
    }

    open spec fn archive(&self) -> Seq<(Seq<T>, Seq<Idx>, Seq<Idx>)> {
        Seq::new(self.dense_snapshots_view().len(), |k: int| (
            self.dense_snapshots_view()[k],
            self.sparse_snapshots_view()[k],
            self.indices_snapshots_view()[k],
        ))
    }

    proof fn lemma_archive_depth(&self) {
        self.dense.lemma_snapshots_len();
    }

    fn can_push_now(&self) -> (b: bool) {
        self.dense.can_mark() && self.sparse.can_mark() && self.indices.can_mark()
    }

    fn depth_exec(&self) -> (d: usize) {
        self.dense.depth_exec()
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        if !self.can_push_now() {
            crate::guard::refuse("Member::push_frame: the sparse set cannot open another frame");
        }
        let ghost pre = *self;
        self.push_frames(shrink);
        proof {
            assert(self.archive() =~= pre.archive().push(pre.model()));
        }
    }

    fn restore_frame(&mut self, depth: usize) {
        if !(depth < self.dense.depth_exec()) {
            crate::guard::refuse("Member::restore_frame: depth is not below the sparse set's");
        }
        let ghost pre = *self;
        proof {
            self.dense.lemma_snapshots_len();
            assert(crate::sparse_set::sparse_set_snap_wf(
                self.dense.snapshots_view()[depth as int],
                self.sparse.snapshots_view()[depth as int],
                self.indices.snapshots_view()[depth as int]));
        }
        self.restore_frames(depth);
        proof {
            assert(self.archive() =~= pre.archive().subrange(0, depth as int));
        }
    }

    fn reset_frame(&mut self, depth: usize) {
        if !(depth < self.dense.depth_exec()) {
            crate::guard::refuse("Member::reset_frame: depth is not below the sparse set's");
        }
        if !(self.dense.depth_exec() < u32::MAX as usize) {
            crate::guard::refuse("Member::reset_frame: frame-stack depth at the u32 ceiling");
        }
        let ghost pre = *self;
        self.reset_frames(depth);
        proof {
            assert(self.archive() =~= pre.archive().subrange(0, depth as int + 1));
        }
    }

    fn pop_frame(&mut self) {
        let d = self.dense.depth_exec();
        if !(d >= 1) {
            crate::guard::refuse("Member::pop_frame: no open frame");
        }
        let ghost pre = *self;
        proof {
            self.dense.lemma_snapshots_len();
            assert(crate::sparse_set::sparse_set_snap_wf(
                self.dense.snapshots_view()[d as int - 1],
                self.sparse.snapshots_view()[d as int - 1],
                self.indices.snapshots_view()[d as int - 1]));
        }
        self.restore_frames(d - 1);
        proof {
            assert(self.archive() =~= pre.archive().subrange(0, pre.depth_spec() - 1));
        }
    }
}

impl<T, N, const TRACK: bool, P> Member for crate::circular_list::CircularList<T, N, TRACK, P>
where
    T: Sized + Copy + core::default::Default + Send,
    N: crate::opt::DenseId,
    P: crate::store_policy::TaggedFamily<
        crate::circular_list::CircularListNode<T, N>,
        <N as crate::opt::DenseId>::Index,
        TRACK,
    >,
{
    type Model = (Seq<crate::circular_list::CircularListNode<T, N>>, Seq<Seq<usize>>);

    open spec fn wf(&self) -> bool {
        &&& crate::circular_list::CircularList::wf(self)
        &&& TRACK
    }

    open spec fn depth_spec(&self) -> nat {
        crate::circular_list::CircularList::depth_spec(self)
    }

    open spec fn can_push(&self) -> bool {
        &&& TRACK
        &&& self.n_spec() < usize::MAX
        &&& crate::circular_list::CircularList::depth_spec(self) < u32::MAX as nat
    }

    open spec fn model(&self) -> (Seq<crate::circular_list::CircularListNode<T, N>>, Seq<Seq<usize>>) {
        (self.entries_view(), self.model_view())
    }

    open spec fn archive(&self) -> Seq<(Seq<crate::circular_list::CircularListNode<T, N>>, Seq<Seq<usize>>)> {
        Seq::new(self.entries_snapshots_view().len(), |k: int| (
            self.entries_snapshots_view()[k],
            self.model_snapshots_view()[k],
        ))
    }

    proof fn lemma_archive_depth(&self) {
        self.entries.lemma_snapshots_len();
    }

    fn can_push_now(&self) -> (b: bool) {
        TRACK
            && self.entries.store.raw_len() < usize::MAX
            && self.entries.depth_exec() < (u32::MAX as usize)
    }

    fn depth_exec(&self) -> (d: usize) {
        self.entries.depth_exec()
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        if !self.can_push_now() {
            crate::guard::refuse("Member::push_frame: the ring cannot open another frame");
        }
        let ghost pre = *self;
        proof { reveal(crate::circular_list::ring_archive_agrees); pre.entries.lemma_snapshots_len(); }
        self.push_frames(shrink);
        proof {
            reveal(crate::circular_list::ring_archive_agrees);
            self.entries.lemma_snapshots_len();
            assert(self.archive().len() == pre.archive().len() + 1);
            assert forall|k: int| 0 <= k < pre.archive().len()
                implies (#[trigger] self.archive()[k]) == pre.archive().push(pre.model())[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive()[pre.archive().len() as int] == pre.model());
            assert(self.archive() =~= pre.archive().push(pre.model()));
        }
    }

    fn restore_frame(&mut self, depth: usize) {
        if !(depth < self.entries.depth_exec()) {
            crate::guard::refuse("Member::restore_frame: depth is not below the ring's");
        }
        let ghost pre = *self;
        proof { reveal(crate::circular_list::ring_archive_agrees); pre.entries.lemma_snapshots_len(); }
        self.restore_frames(depth);
        proof {
            reveal(crate::circular_list::ring_archive_agrees);
            self.entries.lemma_snapshots_len();
            assert(self.archive().len() == depth as int);
            assert forall|k: int| 0 <= k < depth as int
                implies (#[trigger] self.archive()[k]) == pre.archive().subrange(0, depth as int)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, depth as int));
        }
    }

    fn reset_frame(&mut self, depth: usize) {
        if !(depth < self.entries.depth_exec()) {
            crate::guard::refuse("Member::reset_frame: depth is not below the ring's");
        }
        if !(self.entries.depth_exec() < u32::MAX as usize) {
            crate::guard::refuse("Member::reset_frame: frame-stack depth at the u32 ceiling");
        }
        let ghost pre = *self;
        proof { reveal(crate::circular_list::ring_archive_agrees); pre.entries.lemma_snapshots_len(); }
        self.reset_frames(depth);
        proof {
            reveal(crate::circular_list::ring_archive_agrees);
            self.entries.lemma_snapshots_len();
            assert(self.archive().len() == depth as int + 1);
            assert forall|k: int| 0 <= k < depth as int + 1
                implies self.archive()[k] == pre.archive().subrange(0, depth as int + 1)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, depth as int + 1));
        }
    }

    fn pop_frame(&mut self) {
        let d = self.entries.depth_exec();
        if !(d >= 1) {
            crate::guard::refuse("Member::pop_frame: no open frame");
        }
        let ghost pre = *self;
        proof { reveal(crate::circular_list::ring_archive_agrees); pre.entries.lemma_snapshots_len(); }
        self.restore_frames(d - 1);
        proof {
            reveal(crate::circular_list::ring_archive_agrees);
            self.entries.lemma_snapshots_len();
            assert(self.archive().len() == pre.depth_spec() - 1);
            assert forall|k: int| 0 <= k < pre.depth_spec() - 1
                implies self.archive()[k] == pre.archive().subrange(0, pre.depth_spec() - 1)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, pre.depth_spec() - 1));
        }
    }
}

impl<T, L, N, const TRACK: bool, P> Member for crate::list::ListArena<T, L, N, TRACK, P>
where
    T: Sized + Copy + core::default::Default + crate::tagged::Tagged,
    L: crate::opt::DenseId,
    N: crate::opt::DenseId + crate::tagged::Tagged + core::default::Default,
    P: crate::store_policy::TaggedFamily<crate::list::ListHead<N>, <L as crate::opt::DenseId>::Index, TRACK>
        + crate::store_policy::TaggedFamily<crate::list::ListNode<T, N>, <N as crate::opt::DenseId>::Index, TRACK>,
{
    type Model = (Seq<crate::list::ListHead<N>>, Seq<crate::list::ListNode<T, N>>, Seq<Seq<usize>>);

    open spec fn wf(&self) -> bool {
        &&& crate::list::ListArena::wf(self)
        &&& TRACK
        &&& self.heads_depth_spec() == self.nodes_depth_spec()
    }

    open spec fn depth_spec(&self) -> nat {
        self.heads_depth_spec()
    }

    open spec fn can_push(&self) -> bool {
        &&& TRACK
        &&& self.heads_view().len() < usize::MAX
        &&& self.nodes_view().len() < usize::MAX
        &&& self.heads_depth_spec() < u32::MAX as nat
        &&& self.nodes_depth_spec() < u32::MAX as nat
    }

    open spec fn model(&self) -> (Seq<crate::list::ListHead<N>>, Seq<crate::list::ListNode<T, N>>, Seq<Seq<usize>>) {
        (self.heads_view(), self.nodes_view(), self.model_view())
    }

    open spec fn archive(&self) -> Seq<(Seq<crate::list::ListHead<N>>, Seq<crate::list::ListNode<T, N>>, Seq<Seq<usize>>)> {
        Seq::new(self.heads_snapshots_view().len(), |k: int| (
            self.heads_snapshots_view()[k],
            self.nodes_snapshots_view()[k],
            self.model_snapshots_view()[k],
        ))
    }

    proof fn lemma_archive_depth(&self) {
        self.heads.lemma_snapshots_len();
    }

    fn can_push_now(&self) -> (b: bool) {
        let hn = self.heads.store.raw_len();
        let nn = self.nodes.store.raw_len();
        TRACK
            && hn < usize::MAX
            && nn < usize::MAX
            && self.heads.depth_exec() < u32::MAX as usize
            && self.nodes.depth_exec() < u32::MAX as usize
    }

    fn depth_exec(&self) -> (d: usize) {
        self.heads.depth_exec()
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        if !self.can_push_now() {
            crate::guard::refuse("Member::push_frame: the list arena cannot open another frame");
        }
        let ghost pre = *self;
        proof { reveal(crate::list::arena_archive_agrees); pre.heads.lemma_snapshots_len(); }
        self.push_frames(shrink);
        proof {
            reveal(crate::list::arena_archive_agrees);
            self.heads.lemma_snapshots_len();
            assert(self.archive().len() == pre.archive().len() + 1);
            assert forall|k: int| 0 <= k < pre.archive().len()
                implies (#[trigger] self.archive()[k]) == pre.archive().push(pre.model())[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive()[pre.archive().len() as int] == pre.model());
            assert(self.archive() =~= pre.archive().push(pre.model()));
        }
    }

    fn restore_frame(&mut self, depth: usize) {
        if !(depth < self.heads.depth_exec()) {
            crate::guard::refuse("Member::restore_frame: depth is not below the list arena's");
        }
        let ghost pre = *self;
        proof { reveal(crate::list::arena_archive_agrees); pre.heads.lemma_snapshots_len(); }
        self.restore_frames(depth);
        proof {
            reveal(crate::list::arena_archive_agrees);
            self.heads.lemma_snapshots_len();
            assert(self.archive().len() == depth as int);
            assert forall|k: int| 0 <= k < depth as int
                implies (#[trigger] self.archive()[k]) == pre.archive().subrange(0, depth as int)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, depth as int));
        }
    }

    fn reset_frame(&mut self, depth: usize) {
        if !(depth < self.heads.depth_exec()) {
            crate::guard::refuse("Member::reset_frame: depth is not below the list arena's");
        }
        if !(self.heads.depth_exec() < u32::MAX as usize) {
            crate::guard::refuse("Member::reset_frame: frame-stack depth at the u32 ceiling");
        }
        let ghost pre = *self;
        proof { reveal(crate::list::arena_archive_agrees); pre.heads.lemma_snapshots_len(); }
        self.reset_frames(depth);
        proof {
            reveal(crate::list::arena_archive_agrees);
            self.heads.lemma_snapshots_len();
            assert(self.archive().len() == depth as int + 1);
            assert forall|k: int| 0 <= k < depth as int + 1
                implies self.archive()[k] == pre.archive().subrange(0, depth as int + 1)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, depth as int + 1));
        }
    }

    fn pop_frame(&mut self) {
        let d = self.heads.depth_exec();
        if !(d >= 1) {
            crate::guard::refuse("Member::pop_frame: no open frame");
        }
        let ghost pre = *self;
        proof { reveal(crate::list::arena_archive_agrees); pre.heads.lemma_snapshots_len(); }
        self.restore_frames(d - 1);
        proof {
            reveal(crate::list::arena_archive_agrees);
            self.heads.lemma_snapshots_len();
            assert(self.archive().len() == pre.depth_spec() - 1);
            assert forall|k: int| 0 <= k < pre.depth_spec() - 1
                implies self.archive()[k] == pre.archive().subrange(0, pre.depth_spec() - 1)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, pre.depth_spec() - 1));
        }
    }
}

impl<T, J, const TRACK: bool, const PROOFS: bool, P> Member for crate::union_find::UnionFind<T, J, TRACK, PROOFS, P>
where
    T: crate::opt::DenseId + core::default::Default,
    J: crate::tagged::Tagged + Copy + core::default::Default,
    P: crate::store_policy::TaggedFamily<T, <T as crate::opt::DenseId>::Index, TRACK>
        + crate::store_policy::TaggedFamily<u8, <T as crate::opt::DenseId>::Index, TRACK>
        + crate::store_policy::TaggedFamily<J, <T as crate::opt::DenseId>::Index, TRACK>,
{
    /// The forest and its roots; the rank column is bookkeeping the
    /// operations keep in step (its own snapshot stack is not archived here).
    type Model = (Seq<T>, Seq<usize>);

    open spec fn wf(&self) -> bool {
        &&& crate::union_find::UnionFind::wf(self)
        &&& TRACK
        &&& self.parent_depth_spec() == self.rank_depth_spec()
    }

    open spec fn depth_spec(&self) -> nat {
        self.parent_depth_spec()
    }

    open spec fn can_push(&self) -> bool {
        &&& TRACK
        &&& self.parent_depth_spec() < u32::MAX as nat
        &&& self.parent_view().len() < <<T as crate::opt::DenseId>::Index as crate::index_like::IndexLike>::max_nat()
        &&& self.rank_depth_spec() < u32::MAX as nat
        &&& self.rank_view().len() < <<T as crate::opt::DenseId>::Index as crate::index_like::IndexLike>::max_nat()
    }

    open spec fn model(&self) -> (Seq<T>, Seq<usize>) {
        (self.parent_view(), self.roots_view())
    }

    open spec fn archive(&self) -> Seq<(Seq<T>, Seq<usize>)> {
        Seq::new(self.parent_snapshots_view().len(), |k: int| (
            self.parent_snapshots_view()[k],
            self.roots_snapshots_view()[k],
        ))
    }

    proof fn lemma_archive_depth(&self) {
        self.parent.lemma_snapshots_len();
    }

    fn can_push_now(&self) -> (b: bool) {
        self.parent.can_mark() && self.rank.can_mark()
    }

    fn depth_exec(&self) -> (d: usize) {
        self.parent.depth_exec()
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        if !self.can_push_now() {
            crate::guard::refuse("Member::push_frame: the union-find cannot open another frame");
        }
        let ghost pre = *self;
        proof { reveal(crate::union_find::uf_archive_agrees); pre.parent.lemma_snapshots_len(); }
        if PROOFS {
            // The proof columns' depth is checked at runtime, as the
            // composite's own `pop_scope` does (the archive agreement keeps
            // them in step; the check is what the cores' contracts ask for).
            match (&self.parent_proof, &self.justification) {
                (Some(pp), Some(j)) => {
                    if !(pp.depth_exec() == self.parent.depth_exec()
                        && j.depth_exec() == self.parent.depth_exec())
                    {
                        crate::guard::refuse("Member: union-find proof columns out of step");
                    }
                }
                _ => crate::guard::refuse("Member: union-find proof-column shape does not match the build"),
            }
        }
        self.push_frames(shrink);
        proof {
            reveal(crate::union_find::uf_archive_agrees);
            self.parent.lemma_snapshots_len();
            assert(self.archive().len() == pre.archive().len() + 1);
            assert forall|k: int| 0 <= k < pre.archive().len()
                implies (#[trigger] self.archive()[k]) == pre.archive().push(pre.model())[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive()[pre.archive().len() as int] == pre.model());
            assert(self.archive() =~= pre.archive().push(pre.model()));
        }
    }

    fn restore_frame(&mut self, depth: usize) {
        if !(depth < self.parent.depth_exec()) {
            crate::guard::refuse("Member::restore_frame: depth is not below the union-find's");
        }
        let ghost pre = *self;
        proof { reveal(crate::union_find::uf_archive_agrees); pre.parent.lemma_snapshots_len(); }
        if PROOFS {
            // The proof columns' depth is checked at runtime, as the
            // composite's own `pop_scope` does (the archive agreement keeps
            // them in step; the check is what the cores' contracts ask for).
            match (&self.parent_proof, &self.justification) {
                (Some(pp), Some(j)) => {
                    if !(pp.depth_exec() == self.parent.depth_exec()
                        && j.depth_exec() == self.parent.depth_exec())
                    {
                        crate::guard::refuse("Member: union-find proof columns out of step");
                    }
                }
                _ => crate::guard::refuse("Member: union-find proof-column shape does not match the build"),
            }
        }
        self.restore_frames(depth);
        proof {
            reveal(crate::union_find::uf_archive_agrees);
            self.parent.lemma_snapshots_len();
            assert(self.archive().len() == depth as int);
            assert forall|k: int| 0 <= k < depth as int
                implies (#[trigger] self.archive()[k]) == pre.archive().subrange(0, depth as int)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, depth as int));
        }
    }

    fn reset_frame(&mut self, depth: usize) {
        if !(depth < self.parent.depth_exec()) {
            crate::guard::refuse("Member::reset_frame: depth is not below the union-find's");
        }
        if !(self.parent.depth_exec() < u32::MAX as usize) {
            crate::guard::refuse("Member::reset_frame: frame-stack depth at the u32 ceiling");
        }
        let ghost pre = *self;
        proof { reveal(crate::union_find::uf_archive_agrees); pre.parent.lemma_snapshots_len(); }
        if PROOFS {
            // The proof columns' depth is checked at runtime, as the
            // composite's own `pop_scope` does (the archive agreement keeps
            // them in step; the check is what the cores' contracts ask for).
            match (&self.parent_proof, &self.justification) {
                (Some(pp), Some(j)) => {
                    if !(pp.depth_exec() == self.parent.depth_exec()
                        && j.depth_exec() == self.parent.depth_exec())
                    {
                        crate::guard::refuse("Member: union-find proof columns out of step");
                    }
                }
                _ => crate::guard::refuse("Member: union-find proof-column shape does not match the build"),
            }
        }
        self.reset_frames(depth);
        proof {
            reveal(crate::union_find::uf_archive_agrees);
            self.parent.lemma_snapshots_len();
            assert(self.archive().len() == depth as int + 1);
            assert forall|k: int| 0 <= k < depth as int + 1
                implies self.archive()[k] == pre.archive().subrange(0, depth as int + 1)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, depth as int + 1));
        }
    }

    fn pop_frame(&mut self) {
        let d = self.parent.depth_exec();
        if !(d >= 1) {
            crate::guard::refuse("Member::pop_frame: no open frame");
        }
        let ghost pre = *self;
        proof { reveal(crate::union_find::uf_archive_agrees); pre.parent.lemma_snapshots_len(); }
        if PROOFS {
            // The proof columns' depth is checked at runtime, as the
            // composite's own `pop_scope` does (the archive agreement keeps
            // them in step; the check is what the cores' contracts ask for).
            match (&self.parent_proof, &self.justification) {
                (Some(pp), Some(j)) => {
                    if !(pp.depth_exec() == self.parent.depth_exec()
                        && j.depth_exec() == self.parent.depth_exec())
                    {
                        crate::guard::refuse("Member: union-find proof columns out of step");
                    }
                }
                _ => crate::guard::refuse("Member: union-find proof-column shape does not match the build"),
            }
        }
        self.restore_frames(d - 1);
        proof {
            reveal(crate::union_find::uf_archive_agrees);
            self.parent.lemma_snapshots_len();
            assert(self.archive().len() == pre.depth_spec() - 1);
            assert forall|k: int| 0 <= k < pre.depth_spec() - 1
                implies self.archive()[k] == pre.archive().subrange(0, pre.depth_spec() - 1)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, pre.depth_spec() - 1));
        }
    }
}

impl<K, V, I, const TRACK: bool, const UNIQUE: bool, S: crate::hasher_spec::ValidHasher> Member
    for crate::map::SpMap<K, V, I, TRACK, UNIQUE, S>
where
    K: Clone + core::hash::Hash + Eq,
    I: crate::index_like::IndexLike,
{
    /// The log of insertions; the index is derived from it.
    type Model = Seq<(K, V)>;

    open spec fn wf(&self) -> bool {
        &&& crate::map::SpMap::wf(self)
        &&& TRACK
    }

    open spec fn depth_spec(&self) -> nat {
        crate::map::SpMap::depth_spec(self)
    }

    open spec fn can_push(&self) -> bool {
        &&& TRACK
        &&& crate::map::SpMap::depth_spec(self) < u32::MAX as nat
    }

    open spec fn model(&self) -> Seq<(K, V)> {
        self.log_view()
    }

    open spec fn archive(&self) -> Seq<Seq<(K, V)>> {
        self.log_snapshots_view()
    }

    proof fn lemma_archive_depth(&self) {
    }

    fn can_push_now(&self) -> (b: bool) {
        TRACK && self.log.depth() < u32::MAX as usize
    }

    fn depth_exec(&self) -> (d: usize) {
        self.log.depth()
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        if !(self.log.depth() < u32::MAX as usize) {
            crate::guard::refuse("Member::push_frame: the map cannot open another frame");
        }
        self.push_frames(shrink);
    }

    fn restore_frame(&mut self, depth: usize) {
        if !(depth < self.log.depth()) {
            crate::guard::refuse("Member::restore_frame: depth is not below the map's");
        }
        self.restore_frames(depth);
    }

    fn reset_frame(&mut self, depth: usize) {
        if !(depth < self.log.depth()) {
            crate::guard::refuse("Member::reset_frame: depth is not below the map's");
        }
        if !(self.log.depth() < u32::MAX as usize) {
            crate::guard::refuse("Member::reset_frame: frame-stack depth at the u32 ceiling");
        }
        self.reset_frames(depth);
    }

    fn pop_frame(&mut self) {
        if !(self.log.depth() >= 1) {
            crate::guard::refuse("Member::pop_frame: no open frame");
        }
        crate::map::SpMap::pop_frame(self);
    }
}

impl<K, L, S, const TRACK: bool, P> Member for crate::bplus::BPlusTreeSet<K, L, S, TRACK, P>
where
    K: crate::opt::DenseId,
    L: crate::bplus_layout::NodeLayout<Word = <K as crate::opt::DenseId>::Index>,
    S: crate::bplus_search::SearchKind,
    P: crate::store_policy::TaggedFamily<L::Node, L::ArenaIdx, TRACK>,
    L::Node: core::default::Default,
{
    /// The node arena and the ghost tree it encodes.
    type Model = (Seq<L::Node>, crate::bplus_tree::Tree);

    open spec fn wf(&self) -> bool {
        &&& crate::bplus::BPlusTreeSet::wf(self)
        &&& TRACK
    }

    open spec fn depth_spec(&self) -> nat {
        self.arena_depth_spec()
    }

    open spec fn can_push(&self) -> bool {
        &&& TRACK
        &&& self.arena_depth_spec() < u32::MAX as nat
    }

    open spec fn model(&self) -> (Seq<L::Node>, crate::bplus_tree::Tree) {
        (self.arena(), self.tree_spec())
    }

    open spec fn archive(&self) -> Seq<(Seq<L::Node>, crate::bplus_tree::Tree)> {
        Seq::new(self.arena_snapshots_view().len(), |k: int| (
            self.arena_snapshots_view()[k],
            self.tree_snapshots_spec()[k],
        ))
    }

    proof fn lemma_archive_depth(&self) {
        self.nodes.lemma_snapshots_len();
    }

    fn can_push_now(&self) -> (b: bool) {
        TRACK && self.nodes.depth_exec() < u32::MAX as usize
    }

    fn depth_exec(&self) -> (d: usize) {
        self.nodes.depth_exec()
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        if !(self.nodes.depth_exec() < u32::MAX as usize) {
            crate::guard::refuse("Member::push_frame: the tree cannot open another frame");
        }
        let ghost pre = *self;
        proof { reveal(crate::bplus::tree_archive_agrees); pre.nodes.lemma_snapshots_len(); }
        self.push_frames(shrink);
        proof {
            reveal(crate::bplus::tree_archive_agrees);
            self.nodes.lemma_snapshots_len();
            assert(self.archive().len() == pre.archive().len() + 1);
            assert forall|k: int| 0 <= k < pre.archive().len()
                implies (#[trigger] self.archive()[k]) == pre.archive().push(Member::model(&pre))[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive()[pre.archive().len() as int] == Member::model(&pre));
            assert(self.archive() =~= pre.archive().push(Member::model(&pre)));
        }
    }

    fn restore_frame(&mut self, depth: usize) {
        if !(depth < self.nodes.depth_exec()) {
            crate::guard::refuse("Member::restore_frame: depth is not below the tree's");
        }
        let ghost pre = *self;
        proof { reveal(crate::bplus::tree_archive_agrees); pre.nodes.lemma_snapshots_len(); }
        self.restore_frames(depth);
        proof {
            reveal(crate::bplus::tree_archive_agrees);
            self.nodes.lemma_snapshots_len();
            assert(self.archive().len() == depth as int);
            assert forall|k: int| 0 <= k < depth as int
                implies (#[trigger] self.archive()[k]) == pre.archive().subrange(0, depth as int)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, depth as int));
        }
    }

    fn reset_frame(&mut self, depth: usize) {
        if !(depth < self.nodes.depth_exec()) {
            crate::guard::refuse("Member::reset_frame: depth is not below the tree's");
        }
        if !(self.nodes.depth_exec() < u32::MAX as usize) {
            crate::guard::refuse("Member::reset_frame: frame-stack depth at the u32 ceiling");
        }
        let ghost pre = *self;
        proof { reveal(crate::bplus::tree_archive_agrees); pre.nodes.lemma_snapshots_len(); }
        self.reset_frames(depth);
        proof {
            reveal(crate::bplus::tree_archive_agrees);
            self.nodes.lemma_snapshots_len();
            assert(self.archive().len() == depth as int + 1);
            assert forall|k: int| 0 <= k < depth as int + 1
                implies self.archive()[k] == pre.archive().subrange(0, depth as int + 1)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, depth as int + 1));
        }
    }

    fn pop_frame(&mut self) {
        let d = self.nodes.depth_exec();
        if !(d >= 1) {
            crate::guard::refuse("Member::pop_frame: no open frame");
        }
        let ghost pre = *self;
        proof { reveal(crate::bplus::tree_archive_agrees); pre.nodes.lemma_snapshots_len(); }
        self.restore_frames(d - 1);
        proof {
            reveal(crate::bplus::tree_archive_agrees);
            self.nodes.lemma_snapshots_len();
            assert(self.archive().len() == pre.depth_spec() - 1);
            assert forall|k: int| 0 <= k < pre.depth_spec() - 1
                implies self.archive()[k] == pre.archive().subrange(0, pre.depth_spec() - 1)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, pre.depth_spec() - 1));
        }
    }
}

impl<T, K, L, N, J, const TRACK: bool, const PROOFS: bool, P> Member
    for crate::eclasses::EClasses<T, K, L, N, J, TRACK, PROOFS, P>
where
    T: crate::opt::DenseId,
    K: crate::opt::DenseId<Index = <T as crate::opt::DenseId>::Index>,
    L: crate::opt::DenseId,
    N: crate::opt::DenseId + crate::tagged::Tagged + core::default::Default,
    J: crate::tagged::Tagged + Copy + core::default::Default,
    P: crate::store_policy::TaggedFamily<crate::circular_list::CircularListNode<crate::opt::Opt<K>, T>, <T as crate::opt::DenseId>::Index, TRACK>
        + crate::store_policy::TaggedFamily<crate::eclasses::ClassData<L, T>, <T as crate::opt::DenseId>::Index, TRACK>
        + crate::store_policy::TaggedFamily<<T as crate::opt::DenseId>::Index, <T as crate::opt::DenseId>::Index, TRACK>
        + crate::store_policy::TaggedFamily<T, <T as crate::opt::DenseId>::Index, TRACK>
        + crate::store_policy::TaggedFamily<u8, <T as crate::opt::DenseId>::Index, TRACK>
        + crate::store_policy::TaggedFamily<J, <T as crate::opt::DenseId>::Index, TRACK>
        + crate::store_policy::TaggedFamily<crate::list::ListHead<N>, <L as crate::opt::DenseId>::Index, TRACK>
        + crate::store_policy::TaggedFamily<crate::list::ListNode<T, N>, <N as crate::opt::DenseId>::Index, TRACK>
        + crate::store_policy::PlainFamily<crate::opt::Opt<T>, usize, TRACK>,
{
    // TODO(abs-class-storage): add the abstract-value pool view to Model and archive, and its depth to the lockstep checks, see containers-verus/doc/design/21-abstract-value-pool.md §4
    /// Roots, ring partition, ring cells, class data, the repr set's sparse
    /// and index columns, the use lists' partition, and the pool.
    type Model = (Seq<usize>, Seq<Seq<usize>>, Seq<crate::circular_list::CircularListNode<crate::opt::Opt<K>, T>>, Seq<crate::eclasses::ClassData<L, T>>, Seq<<T as crate::opt::DenseId>::Index>, Seq<<T as crate::opt::DenseId>::Index>, Seq<Seq<usize>>, Seq<crate::opt::Opt<T>>);

    open spec fn wf(&self) -> bool {
        &&& crate::eclasses::EClasses::wf(self)
        &&& TRACK
    }

    open spec fn depth_spec(&self) -> nat {
        crate::eclasses::EClasses::depth_spec(self)
    }

    open spec fn can_push(&self) -> bool {
        &&& TRACK
        &&& crate::eclasses::EClasses::depth_spec(self) < u32::MAX as nat
    }

    open spec fn model(&self) -> (Seq<usize>, Seq<Seq<usize>>, Seq<crate::circular_list::CircularListNode<crate::opt::Opt<K>, T>>, Seq<crate::eclasses::ClassData<L, T>>, Seq<<T as crate::opt::DenseId>::Index>, Seq<<T as crate::opt::DenseId>::Index>, Seq<Seq<usize>>, Seq<crate::opt::Opt<T>>) {
        (
            self.roots_view(),
            self.entries_model_view(),
            self.entries_nodes_view(),
            self.reprs_dense_view(),
            self.reprs_sparse_view(),
            self.reprs_indices_view(),
            self.uses_model_view(),
            self.pool_view(),
        )
    }

    open spec fn archive(&self) -> Seq<(Seq<usize>, Seq<Seq<usize>>, Seq<crate::circular_list::CircularListNode<crate::opt::Opt<K>, T>>, Seq<crate::eclasses::ClassData<L, T>>, Seq<<T as crate::opt::DenseId>::Index>, Seq<<T as crate::opt::DenseId>::Index>, Seq<Seq<usize>>, Seq<crate::opt::Opt<T>>)> {
        Seq::new(self.pool_archive().len(), |k: int| (
            self.roots_archive_view()[k],
            self.entries_model_archive()[k],
            self.entries_archive()[k],
            self.reprs_dense_archive()[k],
            self.reprs_sparse_archive()[k],
            self.reprs_indices_archive()[k],
            self.uses_model_archive()[k],
            self.pool_archive()[k],
        ))
    }

    proof fn lemma_archive_depth(&self) {
    }

    fn can_push_now(&self) -> (b: bool) {
        proof { self.min_pool.lemma_snapshots_len(); }
        TRACK && self.min_pool.depth_exec() < u32::MAX as usize
    }

    fn depth_exec(&self) -> (d: usize) {
        proof { self.min_pool.lemma_snapshots_len(); }
        self.min_pool.depth_exec()
    }

    fn push_frame(&mut self, shrink: ShrinkPolicy) {
        if !self.can_push_now() {
            crate::guard::refuse("Member::push_frame: the e-classes cannot open another frame");
        }
        let ghost pre = *self;
        self.push_frames(shrink);
        proof {
            reveal(crate::eclasses::eg_archive_agrees);
            assert(self.archive().len() == pre.archive().len() + 1);
            assert forall|k: int| 0 <= k < pre.archive().len()
                implies (#[trigger] self.archive()[k]) == pre.archive().push(pre.model())[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive()[pre.archive().len() as int] == pre.model());
            assert(self.archive() =~= pre.archive().push(pre.model()));
        }
    }

    fn restore_frame(&mut self, depth: usize) {
        if !(depth < self.depth_exec()) {
            crate::guard::refuse("Member::restore_frame: depth is not below the e-classes'");
        }
        let ghost pre = *self;
        self.restore_frames(depth);
        proof {
            reveal(crate::eclasses::eg_archive_agrees);
            assert(self.archive().len() == depth as int);
            assert forall|k: int| 0 <= k < depth as int
                implies (#[trigger] self.archive()[k]) == pre.archive().subrange(0, depth as int)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, depth as int));
        }
    }

    fn reset_frame(&mut self, depth: usize) {
        if !(depth < self.depth_exec()) {
            crate::guard::refuse("Member::reset_frame: depth is not below the e-classes'");
        }
        if !(self.depth_exec() < u32::MAX as usize) {
            crate::guard::refuse("Member::reset_frame: frame-stack depth at the u32 ceiling");
        }
        let ghost pre = *self;
        self.reset_frames(depth);
        proof {
            reveal(crate::eclasses::eg_archive_agrees);
            assert(self.archive().len() == depth as int + 1);
            assert forall|k: int| 0 <= k < depth as int + 1
                implies self.archive()[k] == pre.archive().subrange(0, depth as int + 1)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, depth as int + 1));
        }
    }

    fn pop_frame(&mut self) {
        let d = self.depth_exec();
        if !(d >= 1) {
            crate::guard::refuse("Member::pop_frame: no open frame");
        }
        let ghost pre = *self;
        self.restore_frames(d - 1);
        proof {
            reveal(crate::eclasses::eg_archive_agrees);
            assert(self.archive().len() == pre.depth_spec() - 1);
            assert forall|k: int| 0 <= k < pre.depth_spec() - 1
                implies self.archive()[k] == pre.archive().subrange(0, pre.depth_spec() - 1)[k] by {
                assert(self.archive()[k] == pre.archive()[k]);
            }
            assert(self.archive() =~= pre.archive().subrange(0, pre.depth_spec() - 1));
        }
    }
}

} // verus!

// Typed access without spelling `.member`: `group.len()`, `group.set(..)`,
// `group.get(..)` reach the member (plain Rust, outside the verified
// perimeter; the group's own operations shadow nothing the member has, since
// the member carries no versioning surface of its own).
impl<M: Member> core::ops::Deref for ForkHistory<M> {
    type Target = M;
    #[inline(always)]
    fn deref(&self) -> &M {
        &self.member
    }
}

impl<M: Member> core::ops::DerefMut for ForkHistory<M> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut M {
        &mut self.member
    }
}
