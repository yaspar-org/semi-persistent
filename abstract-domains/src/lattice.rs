// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The lattice interface shared by every abstract domain.
//!
//! Domains are bottomless, as in Verasco: a `Domain` value always denotes a
//! nonempty set, and unreachability is the external `BotOr::Bot`. Operations
//! that can produce the empty set (meet, backward refinement, division by a
//! zero divisor, reduction) return `BotOr<Self>`.
//!
//! Contracts state soundness against the concretization `gamma`, following
//! Verasco's `AdomLib` (`leb_correct`, `join_correct`, `meet_correct`,
//! `widen_incr`). Widening is soundness only; analysis termination is by fuel.
//!
//! Beyond Verasco, every domain proves `lemma_canonical`: a well-formed value is
//! determined by its concretization, so structural equality is set equality
//! (fixpoint checks cannot miss stabilization; see doc/domain-traits.md).
use vstd::prelude::*;

verus! {

pub trait Domain: Sized {
    /// Concrete values.
    type C;

    /// Representation invariant. Must admit exactly one value per concretization.
    spec fn wf(&self) -> bool;

    spec fn gamma(&self, c: Self::C) -> bool;

    /// Nonempty: domains are bottomless.
    proof fn lemma_nonempty(&self)
        requires
            self.wf(),
        ensures
            exists|c: Self::C| self.gamma(c),
    ;

    /// Canonical representation: equal concretizations are equal values.
    proof fn lemma_canonical(a: &Self, b: &Self)
        requires
            a.wf(),
            b.wf(),
            forall|c: Self::C| #![trigger a.gamma(c)] a.gamma(c) == b.gamma(c),
        ensures
            *a == *b,
    ;

    /// Copy of a value (domains over big numbers are not `Copy`).
    fn dup(&self) -> (r: Self)
        ensures
            r == *self,
    ;

    fn top() -> (r: Self)
        ensures
            r.wf(),
            forall|c: Self::C| #[trigger] r.gamma(c),
    ;

    fn leq(&self, o: &Self) -> (b: bool)
        requires
            self.wf(),
            o.wf(),
        ensures
            b ==> forall|c: Self::C| #[trigger] self.gamma(c) ==> o.gamma(c),
    ;

    /// Any sound upper bound (wrapped intervals have no least one).
    fn join(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|c: Self::C| #[trigger] r.gamma(c) <== self.gamma(c) || o.gamma(c),
    ;

    /// `Bot` only when the intersection is empty.
    fn meet(&self, o: &Self) -> (r: BotOr<Self>)
        requires
            self.wf(),
            o.wf(),
        ensures
            match r {
                BotOr::Bot => forall|c: Self::C| #[trigger] self.gamma(c) ==> !o.gamma(c),
                BotOr::Val(m) => m.wf() && forall|c: Self::C| #[trigger]
                    m.gamma(c) <== self.gamma(c) && o.gamma(c),
            },
    ;

    /// Soundness only; `self` is the previous iterate.
    fn widen(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|c: Self::C| #[trigger] r.gamma(c) <== self.gamma(c) || o.gamma(c),
    ;
}

/// A domain value or bottom (Verasco's `t+⊥`, constructors `Bot` / `NotBot`).
pub enum BotOr<D> {
    Bot,
    Val(D),
}

impl<D: Domain> BotOr<D> {
    pub open spec fn wf(&self) -> bool {
        match self {
            BotOr::Bot => true,
            BotOr::Val(d) => d.wf(),
        }
    }

    pub open spec fn gamma(&self, c: D::C) -> bool {
        match self {
            BotOr::Bot => false,
            BotOr::Val(d) => d.gamma(c),
        }
    }

    pub fn is_bot(&self) -> (b: bool)
        ensures
            b == (*self is Bot),
    {
        match self {
            BotOr::Bot => true,
            BotOr::Val(_) => false,
        }
    }

    pub fn dup(&self) -> (r: Self)
        ensures
            r == *self,
    {
        match self {
            BotOr::Bot => BotOr::Bot,
            BotOr::Val(d) => BotOr::Val(d.dup()),
        }
    }

    pub fn top() -> (r: Self)
        ensures
            r.wf(),
            forall|c: D::C| #[trigger] r.gamma(c),
    {
        BotOr::Val(D::top())
    }

    pub fn leq(&self, o: &Self) -> (b: bool)
        requires
            self.wf(),
            o.wf(),
        ensures
            b ==> forall|c: D::C| #[trigger] self.gamma(c) ==> o.gamma(c),
    {
        match (self, o) {
            (BotOr::Bot, _) => true,
            (_, BotOr::Bot) => false,
            (BotOr::Val(a), BotOr::Val(b)) => a.leq(b),
        }
    }

    pub fn join(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|c: D::C| #[trigger] r.gamma(c) <== self.gamma(c) || o.gamma(c),
    {
        match (self, o) {
            (BotOr::Bot, _) => o.dup(),
            (_, BotOr::Bot) => self.dup(),
            (BotOr::Val(a), BotOr::Val(b)) => BotOr::Val(a.join(b)),
        }
    }

    pub fn meet(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|c: D::C| #[trigger] r.gamma(c) <== self.gamma(c) && o.gamma(c),
    {
        match (self, o) {
            (BotOr::Val(a), BotOr::Val(b)) => a.meet(b),
            _ => BotOr::Bot,
        }
    }

    pub fn widen(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|c: D::C| #[trigger] r.gamma(c) <== self.gamma(c) || o.gamma(c),
    {
        match (self, o) {
            (BotOr::Bot, _) => o.dup(),
            (_, BotOr::Bot) => self.dup(),
            (BotOr::Val(a), BotOr::Val(b)) => BotOr::Val(a.widen(b)),
        }
    }
}

} // verus!
