// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `FactsZ`: the channel of Int e-classes, and its forward transfers.
//!
//! Same structure as `facts::Facts<W>` (see there for how to add a field).
//! Planned fields (doc/reduced-product.md, planned work):
//! - `c: CongruenceZ`, `x ≡ r mod m` over ℤ (`m = 0` for a constant);
//! - `nz: bool`, the value is nonzero. With `itv` it expresses every Sign
//!   value (`< 0`, `<= 0`, `!= 0`, ...), so Sign needs no field of its own.
// Proof-only bindings are erased outside Verus.
#![allow(unused_variables)]
use crate::bool4::*;
use crate::interval_z::*;
use crate::lattice::*;
use crate::reduce::*;
use crate::semantics::*;
use crate::transfer::*;
use vstd::prelude::*;

verus! {

pub struct FactsZ {
    /// Bounds.
    itv: IntervalZ,
}

impl FactsZ {
    pub closed spec fn itv(&self) -> IntervalZ {
        self.itv
    }
    /// The fields agree. Trivially true with one field; the planned fields extend it.
    pub open spec fn reduced(&self) -> bool {
        true
    }

    /// The record that knows only `itv`.
    pub fn from_interval(itv: IntervalZ) -> (r: Self)
        requires
            itv.wf(),
        ensures
            r.wf(),
            r.itv() == itv,
            forall|x: int| #[trigger] r.gamma(x) == itv.gamma(x),
    {
        FactsZ { itv }
    }

    pub fn interval(&self) -> (r: IntervalZ)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.itv(),
            forall|x: int| self.gamma(x) ==> #[trigger] r.gamma(x),
    {
        self.itv.dup()
    }

}

impl Domain for FactsZ {
    type C = int;

    open spec fn wf(&self) -> bool {
        self.pre_wf() && self.reduced()
    }

    open spec fn gamma(&self, c: int) -> bool {
        self.itv().gamma(c)
    }

    fn dup(&self) -> (r: Self) {
        FactsZ { itv: self.itv.dup() }
    }

    fn top() -> (r: Self) {
        FactsZ { itv: IntervalZ::top() }
    }

    fn leq(&self, o: &Self) -> (b: bool) {
        self.itv.leq(&o.itv)
    }

    fn join(&self, o: &Self) -> (r: Self) {
        FactsZ { itv: self.itv.join(&o.itv) }
    }

    /// `meet_exact` then `normalize`, inlined field by field (see `Facts::meet`).
    fn meet(&self, o: &Self) -> (r: BotOr<Self>) {
        match self.itv.meet(&o.itv) {
            BotOr::Bot => BotOr::Bot,
            BotOr::Val(itv) => BotOr::Val(FactsZ { itv }),
        }
    }

    fn widen(&self, o: &Self) -> (r: Self) {
        FactsZ { itv: self.itv.widen(&o.itv) }
    }
}

impl Canonical for FactsZ {
    proof fn lemma_nonempty(&self) {
        self.itv.lemma_nonempty();
        let c = choose|c: int| self.itv.gamma(c);
        assert(self.gamma(c));
    }

    proof fn lemma_canonical(a: &Self, b: &Self) {
        assert forall|c: int| #![trigger a.itv.gamma(c)] a.itv.gamma(c) == b.itv.gamma(c) by {
            assert(a.gamma(c) == b.gamma(c));
        }
        IntervalZ::lemma_canonical(&a.itv, &b.itv);
    }
}

impl Channel for FactsZ {
    open spec fn pre_wf(&self) -> bool {
        self.itv().wf()
    }

    proof fn lemma_wf_pre(&self) {
    }

    fn meet_exact(&self, o: &Self) -> (r: BotOr<Self>) {
        let m = self.itv.meet_exact(&o.itv);
        match m {
            BotOr::Bot => {
                proof {
                    assert forall|c: int| #[trigger] self.gamma(c) implies !o.gamma(c) by {
                        assert(m.gamma(c) == (self.itv.gamma(c) && o.itv.gamma(c)));
                    }
                }
                BotOr::Bot
            },
            BotOr::Val(itv) => {
                let r = FactsZ { itv };
                proof {
                    assert forall|c: int| #[trigger] r.gamma(c) == (self.gamma(c) && o.gamma(c)) by {
                        assert(m.gamma(c) == (self.itv.gamma(c) && o.itv.gamma(c)));
                    }
                }
                BotOr::Val(r)
            },
        }
    }

    /// The identity: with one field there is nothing to propagate. The planned work adds
    /// interval against congruence and interval against the nonzero bit.
    fn normalize(&self) -> (r: BotOr<Self>) {
        BotOr::Val(self.dup())
    }
}

/// Its own channel: `to_channel` is the identity, `refine` is the reduced meet.
impl Refine for FactsZ {
    type F = FactsZ;

    fn to_channel(&self) -> (f: BotOr<FactsZ>) {
        BotOr::Val(self.dup())
    }

    fn refine(&self, f: &FactsZ) -> (r: BotOr<Self>) {
        meet_normalize(self, f)
    }
}

/// An interval over ℤ writes itself into the `itv` field and refines by it.
impl Refine for IntervalZ {
    type F = FactsZ;

    fn to_channel(&self) -> (f: BotOr<FactsZ>) {
        BotOr::Val(FactsZ::from_interval(self.dup()))
    }

    fn refine(&self, f: &FactsZ) -> (r: BotOr<Self>) {
        let i = f.interval();
        let r = self.meet_exact(&i);
        proof {
            assert forall|x: int| self.gamma(x) && f.gamma(x) implies #[trigger] r.gamma(x) by {
                assert(i.gamma(x));
            }
        }
        r
    }
}

/// Wraps a sound interval result as a normalized record.
fn lift(i: IntervalZ) -> (r: FactsZ)
    requires
        i.wf(),
    ensures
        r.wf(),
        forall|x: int| i.gamma(x) ==> #[trigger] r.gamma(x),
{
    let f = FactsZ::from_interval(i);
    proof {
        f.lemma_wf_pre();
    }
    let n = f.normalize();
    match n {
        BotOr::Val(r) => {
            proof {
                assert forall|x: int| i.gamma(x) implies #[trigger] r.gamma(x) by {
                    assert(f.gamma(x) && n.gamma(x));
                }
            }
            r
        },
        BotOr::Bot => {
            proof {
                assert forall|x: int| i.gamma(x) implies false by {
                    assert(f.gamma(x) && n.gamma(x));
                }
            }
            FactsZ::top()
        },
    }
}

fn lift_div(q: (BotOr<IntervalZ>, DivZero)) -> (r: (BotOr<FactsZ>, DivZero))
    requires
        q.0.wf(),
    ensures
        r.0.wf(),
        forall|x: int| q.0.gamma(x) ==> #[trigger] r.0.gamma(x),
        r.1 == q.1,
        (r.0 is Bot) <==> (q.0 is Bot),
{
    match q.0 {
        BotOr::Bot => (BotOr::Bot, q.1),
        BotOr::Val(i) => {
            let r = lift(i);
            proof {
                assert forall|x: int| q.0.gamma(x) implies #[trigger] BotOr::<FactsZ>::Val(r).gamma(
                    x,
                ) by {
                    assert(i.gamma(x));
                }
            }
            (BotOr::Val(r), q.1)
        },
    }
}

impl Arith<Euclid> for FactsZ {
    fn add(&self, o: &Self) -> (r: Self) {
        lift(<IntervalZ as Arith<Euclid>>::add(&self.interval(), &o.interval()))
    }

    fn sub(&self, o: &Self) -> (r: Self) {
        lift(<IntervalZ as Arith<Euclid>>::sub(&self.interval(), &o.interval()))
    }

    fn neg(&self) -> (r: Self) {
        lift(<IntervalZ as Arith<Euclid>>::neg(&self.interval()))
    }
}

impl Arith<Trunc> for FactsZ {
    fn add(&self, o: &Self) -> (r: Self) {
        lift(<IntervalZ as Arith<Trunc>>::add(&self.interval(), &o.interval()))
    }

    fn sub(&self, o: &Self) -> (r: Self) {
        lift(<IntervalZ as Arith<Trunc>>::sub(&self.interval(), &o.interval()))
    }

    fn neg(&self) -> (r: Self) {
        lift(<IntervalZ as Arith<Trunc>>::neg(&self.interval()))
    }
}

impl DivRem<Euclid> for FactsZ {
    fn contains_zero(&self) -> (b: bool) {
        let i = self.interval();
        <IntervalZ as DivRem<Euclid>>::contains_zero(&i)
    }

    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let (i, di) = (self.interval(), d.interval());
        lift_div(<IntervalZ as DivRem<Euclid>>::div(&i, &di))
    }

    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let (i, di) = (self.interval(), d.interval());
        lift_div(<IntervalZ as DivRem<Euclid>>::rem(&i, &di))
    }
}

impl DivRem<Trunc> for FactsZ {
    fn contains_zero(&self) -> (b: bool) {
        let i = self.interval();
        <IntervalZ as DivRem<Trunc>>::contains_zero(&i)
    }

    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let (i, di) = (self.interval(), d.interval());
        lift_div(<IntervalZ as DivRem<Trunc>>::div(&i, &di))
    }

    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let (i, di) = (self.interval(), d.interval());
        lift_div(<IntervalZ as DivRem<Trunc>>::rem(&i, &di))
    }
}

/// Stub: forward answers `Top`, backward keeps both operands. The planned work
/// replaces it with transfers on the `itv` field (doc/reduced-product.md).
impl Compare<Euclid> for FactsZ {
    fn lt(&self, o: &Self) -> (r: Bool4) {
        Bool4::Top
    }

    fn le(&self, o: &Self) -> (r: Bool4) {
        Bool4::Top
    }

    fn eq(&self, o: &Self) -> (r: Bool4) {
        Bool4::Top
    }

    fn assume_lt(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>)) {
        (BotOr::Val(self.dup()), BotOr::Val(o.dup()))
    }

    fn assume_le(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>)) {
        (BotOr::Val(self.dup()), BotOr::Val(o.dup()))
    }

    fn assume_eq(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>)) {
        (BotOr::Val(self.dup()), BotOr::Val(o.dup()))
    }
}

/// Stub: forward answers `Top`, backward keeps both operands. The planned work
/// replaces it with transfers on the `itv` field (doc/reduced-product.md).
impl Compare<Trunc> for FactsZ {
    fn lt(&self, o: &Self) -> (r: Bool4) {
        Bool4::Top
    }

    fn le(&self, o: &Self) -> (r: Bool4) {
        Bool4::Top
    }

    fn eq(&self, o: &Self) -> (r: Bool4) {
        Bool4::Top
    }

    fn assume_lt(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>)) {
        (BotOr::Val(self.dup()), BotOr::Val(o.dup()))
    }

    fn assume_le(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>)) {
        (BotOr::Val(self.dup()), BotOr::Val(o.dup()))
    }

    fn assume_eq(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>)) {
        (BotOr::Val(self.dup()), BotOr::Val(o.dup()))
    }
}

} // verus!
