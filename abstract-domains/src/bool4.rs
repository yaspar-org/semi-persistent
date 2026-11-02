// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Bool4`: the value of a Bool e-class.
//!
//! Four values: `False`, `True`, `Top`, and the empty set as `BotOr::Bot`
//! (an e-class whose Bool value is `Bot` is a conflict). One value per
//! nonempty set of booleans, so `Bool4` is canonical, and it is its own
//! channel. The connectives are exact: sound, and every value of the result
//! is produced by some pair of operand values.
//!
//! Starting point for the Int and Bool work (doc/reduced-product.md), which adds `ite`
//! and the backward connectives.
// Proof-only bindings are erased outside Verus.
#![allow(unused_variables)]
use crate::lattice::*;
use crate::reduce::*;
use vstd::prelude::*;

verus! {

pub enum Bool4 {
    False,
    True,
    Top,
}

/// `∃ x ∈ γ(a). f(x) = z`, unrolled over `bool`.
pub open spec fn reach1(a: Bool4, f: spec_fn(bool) -> bool, z: bool) -> bool {
    (a.gamma(false) && f(false) == z) || (a.gamma(true) && f(true) == z)
}

/// `∃ x ∈ γ(a), y ∈ γ(b). f(x, y) = z`, unrolled over `bool`.
pub open spec fn reach2(a: Bool4, b: Bool4, f: spec_fn(bool, bool) -> bool, z: bool) -> bool {
    (a.gamma(false) && b.gamma(false) && f(false, false) == z) || (a.gamma(false) && b.gamma(true)
        && f(false, true) == z) || (a.gamma(true) && b.gamma(false) && f(true, false) == z) || (
    a.gamma(true) && b.gamma(true) && f(true, true) == z)
}

impl Bool4 {
    pub fn constant(b: bool) -> (r: Self)
        ensures
            forall|x: bool| #[trigger] r.gamma(x) <==> x == b,
    {
        if b {
            Bool4::True
        } else {
            Bool4::False
        }
    }

    /// `true` when every value is `true`.
    pub fn is_true(&self) -> (b: bool)
        ensures
            b <==> (self.gamma(true) && !self.gamma(false)),
    {
        matches!(self, Bool4::True)
    }

    /// `true` when every value is `false`.
    pub fn is_false(&self) -> (b: bool)
        ensures
            b <==> (self.gamma(false) && !self.gamma(true)),
    {
        matches!(self, Bool4::False)
    }

    fn same(&self, o: &Self) -> (b: bool)
        ensures
            b <==> (*self == *o),
    {
        matches!(
            (self, o),
            (Bool4::False, Bool4::False) | (Bool4::True, Bool4::True) | (Bool4::Top, Bool4::Top)
        )
    }

    pub fn not(&self) -> (r: Self)
        ensures
            forall|x: bool| #[trigger] self.gamma(x) ==> r.gamma(!x),
            forall|z: bool| #[trigger] r.gamma(z) ==> reach1(*self, |x: bool| !x, z),
    {
        match self {
            Bool4::False => Bool4::True,
            Bool4::True => Bool4::False,
            Bool4::Top => Bool4::Top,
        }
    }

    pub fn and(&self, o: &Self) -> (r: Self)
        ensures
            forall|x: bool, y: bool|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) ==> r.gamma(x && y),
            forall|z: bool| #[trigger]
                r.gamma(z) ==> reach2(*self, *o, |x: bool, y: bool| x && y, z),
    {
        match (self, o) {
            (Bool4::False, _) | (_, Bool4::False) => Bool4::False,
            (Bool4::True, Bool4::True) => Bool4::True,
            _ => Bool4::Top,
        }
    }

    pub fn or(&self, o: &Self) -> (r: Self)
        ensures
            forall|x: bool, y: bool|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) ==> r.gamma(x || y),
            forall|z: bool| #[trigger]
                r.gamma(z) ==> reach2(*self, *o, |x: bool, y: bool| x || y, z),
    {
        match (self, o) {
            (Bool4::True, _) | (_, Bool4::True) => Bool4::True,
            (Bool4::False, Bool4::False) => Bool4::False,
            _ => Bool4::Top,
        }
    }

    /// Boolean equality (SMT-LIB `=` on Bool).
    pub fn eq(&self, o: &Self) -> (r: Self)
        ensures
            forall|x: bool, y: bool|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) ==> r.gamma(x == y),
            forall|z: bool| #[trigger]
                r.gamma(z) ==> reach2(*self, *o, |x: bool, y: bool| x == y, z),
    {
        match (self, o) {
            (Bool4::Top, _) | (_, Bool4::Top) => Bool4::Top,
            _ => Bool4::constant(self.same(o)),
        }
    }
}

impl Domain for Bool4 {
    type C = bool;

    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn gamma(&self, c: bool) -> bool {
        match self {
            Bool4::False => !c,
            Bool4::True => c,
            Bool4::Top => true,
        }
    }

    fn dup(&self) -> (r: Self) {
        match self {
            Bool4::False => Bool4::False,
            Bool4::True => Bool4::True,
            Bool4::Top => Bool4::Top,
        }
    }

    fn top() -> (r: Self) {
        Bool4::Top
    }

    fn leq(&self, o: &Self) -> (b: bool) {
        matches!(o, Bool4::Top) || self.same(o)
    }

    fn join(&self, o: &Self) -> (r: Self) {
        if self.same(o) {
            self.dup()
        } else {
            Bool4::Top
        }
    }

    fn meet(&self, o: &Self) -> (r: BotOr<Self>) {
        match (self, o) {
            (Bool4::Top, _) => BotOr::Val(o.dup()),
            (_, Bool4::Top) => BotOr::Val(self.dup()),
            _ => if self.same(o) {
                BotOr::Val(self.dup())
            } else {
                BotOr::Bot
            },
        }
    }

    fn widen(&self, o: &Self) -> (r: Self) {
        if self.same(o) {
            self.dup()
        } else {
            Bool4::Top
        }
    }
}

impl Canonical for Bool4 {
    proof fn lemma_nonempty(&self) {
        assert(self.gamma(true) || self.gamma(false));
    }

    proof fn lemma_canonical(a: &Self, b: &Self) {
        assert(a.gamma(true) == b.gamma(true));
        assert(a.gamma(false) == b.gamma(false));
    }
}

impl Channel for Bool4 {
    open spec fn pre_wf(&self) -> bool {
        true
    }

    proof fn lemma_wf_pre(&self) {
    }

    fn meet_exact(&self, o: &Self) -> (r: BotOr<Self>) {
        match (self, o) {
            (Bool4::Top, _) => BotOr::Val(o.dup()),
            (_, Bool4::Top) => BotOr::Val(self.dup()),
            _ => if self.same(o) {
                BotOr::Val(self.dup())
            } else {
                BotOr::Bot
            },
        }
    }

    /// The identity: a single field has nothing to propagate.
    fn normalize(&self) -> (r: BotOr<Self>) {
        BotOr::Val(self.dup())
    }
}

/// Its own channel: `to_channel` is the identity, `refine` is the meet.
impl Refine for Bool4 {
    type F = Bool4;

    fn to_channel(&self) -> (f: BotOr<Bool4>) {
        BotOr::Val(self.dup())
    }

    fn refine(&self, f: &Bool4) -> (r: BotOr<Self>) {
        meet_normalize(self, f)
    }
}

} // verus!
