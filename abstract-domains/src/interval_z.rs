// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Intervals over unbounded integers.
//!
//! Reference port of an unbounded domain onto the shared traits. Each bound is
//! an enum, so an infinite bound carries no stray number, and there is no
//! empty flag: `lo <= hi` whenever both are finite, and the empty set is
//! `BotOr::Bot`. `[-inf, +inf]` is representable, so the domain has an internal
//! top and needs no Verasco-style `t+⊤` lift.
//!
//! Division is sound but coarse here (top, with an exact zero flag); the
//! precise Euclidean and truncated transfers belong to the IntervalZ work.
// Proof-only bindings and lemma imports are erased outside Verus.
#![allow(unused_imports, unused_variables)]
use crate::ibig::*;
use crate::lattice::*;
use crate::semantics::*;
use crate::transfer::*;
use vstd::prelude::*;

verus! {

pub enum Lo {
    NegInf,
    Fin(IBig),
}

pub enum Hi {
    Fin(IBig),
    PosInf,
}

pub open spec fn lo_ok(l: Lo, c: int) -> bool {
    match l {
        Lo::NegInf => true,
        Lo::Fin(a) => a.view() <= c,
    }
}

pub open spec fn hi_ok(h: Hi, c: int) -> bool {
    match h {
        Hi::PosInf => true,
        Hi::Fin(b) => c <= b.view(),
    }
}

/// `a` is a lower bound no greater than `b`.
pub open spec fn lo_leq(a: Lo, b: Lo) -> bool {
    match (a, b) {
        (Lo::NegInf, _) => true,
        (Lo::Fin(_), Lo::NegInf) => false,
        (Lo::Fin(x), Lo::Fin(y)) => x.view() <= y.view(),
    }
}

/// `a` is an upper bound no greater than `b`.
pub open spec fn hi_leq(a: Hi, b: Hi) -> bool {
    match (a, b) {
        (_, Hi::PosInf) => true,
        (Hi::PosInf, Hi::Fin(_)) => false,
        (Hi::Fin(x), Hi::Fin(y)) => x.view() <= y.view(),
    }
}

fn dup_ibig(a: &IBig) -> (r: IBig)
    ensures
        r == *a,
{
    let b = a.dup();
    proof {
        IBig::axiom_view_injective(&b, a);
    }
    b
}

fn dup_lo(l: &Lo) -> (r: Lo)
    ensures
        r == *l,
{
    match l {
        Lo::NegInf => Lo::NegInf,
        Lo::Fin(a) => Lo::Fin(dup_ibig(a)),
    }
}

fn dup_hi(h: &Hi) -> (r: Hi)
    ensures
        r == *h,
{
    match h {
        Hi::PosInf => Hi::PosInf,
        Hi::Fin(a) => Hi::Fin(dup_ibig(a)),
    }
}

fn lo_le(a: &Lo, b: &Lo) -> (r: bool)
    ensures
        r == lo_leq(*a, *b),
        r <==> forall|c: int| #[trigger] lo_ok(*b, c) ==> lo_ok(*a, c),
{
    match (a, b) {
        (Lo::NegInf, _) => true,
        (Lo::Fin(x), Lo::NegInf) => {
            proof {
                assert(lo_ok(*b, x.view() - 1));
            }
            false
        },
        (Lo::Fin(x), Lo::Fin(y)) => {
            proof {
                assert(lo_ok(*b, y.view()));
            }
            x.le(y)
        },
    }
}

fn hi_le(a: &Hi, b: &Hi) -> (r: bool)
    ensures
        r == hi_leq(*a, *b),
        r <==> forall|c: int| #[trigger] hi_ok(*a, c) ==> hi_ok(*b, c),
{
    match (a, b) {
        (_, Hi::PosInf) => true,
        (Hi::PosInf, Hi::Fin(y)) => {
            proof {
                assert(hi_ok(*a, y.view() + 1));
            }
            false
        },
        (Hi::Fin(x), Hi::Fin(y)) => {
            proof {
                assert(hi_ok(*a, x.view()));
            }
            x.le(y)
        },
    }
}

/// `{x | lo <= x <= hi}`.
pub struct IntervalZ {
    lo: Lo,
    hi: Hi,
}

impl IntervalZ {
    pub closed spec fn lo(&self) -> Lo {
        self.lo
    }

    pub closed spec fn hi(&self) -> Hi {
        self.hi
    }

    pub fn new(lo: Lo, hi: Hi) -> (r: Option<Self>)
        ensures
            match r {
                Some(i) => i.wf() && i.lo() == lo && i.hi() == hi,
                None => match (lo, hi) {
                    (Lo::Fin(a), Hi::Fin(b)) => a.view() > b.view(),
                    _ => false,
                },
            },
    {
        let ok = match (&lo, &hi) {
            (Lo::Fin(a), Hi::Fin(b)) => a.le(b),
            _ => true,
        };
        if ok {
            Some(IntervalZ { lo, hi })
        } else {
            None
        }
    }

    pub fn constant(c: IBig) -> (r: Self)
        ensures
            r.wf(),
            forall|x: int| #[trigger] r.gamma(x) <==> x == c.view(),
    {
        IntervalZ { lo: Lo::Fin(dup_ibig(&c)), hi: Hi::Fin(c) }
    }

    fn add_int(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|x: int, y: int| self.gamma(x) && o.gamma(y) ==> #[trigger] r.gamma(x + y),
    {
        let lo = match (&self.lo, &o.lo) {
            (Lo::Fin(a), Lo::Fin(b)) => Lo::Fin(a.add(b)),
            _ => Lo::NegInf,
        };
        let hi = match (&self.hi, &o.hi) {
            (Hi::Fin(a), Hi::Fin(b)) => Hi::Fin(a.add(b)),
            _ => Hi::PosInf,
        };
        IntervalZ { lo, hi }
    }

    fn neg_int(&self) -> (r: Self)
        requires
            self.wf(),
        ensures
            r.wf(),
            forall|x: int| self.gamma(x) ==> #[trigger] r.gamma(-x),
    {
        let lo = match &self.hi {
            Hi::Fin(b) => Lo::Fin(b.neg()),
            Hi::PosInf => Lo::NegInf,
        };
        let hi = match &self.lo {
            Lo::Fin(a) => Hi::Fin(a.neg()),
            Lo::NegInf => Hi::PosInf,
        };
        IntervalZ { lo, hi }
    }

    fn sub_int(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|x: int, y: int| self.gamma(x) && o.gamma(y) ==> #[trigger] r.gamma(x - y),
    {
        let n = o.neg_int();
        let r = self.add_int(&n);
        proof {
            assert forall|x: int, y: int| self.gamma(x) && o.gamma(y) implies #[trigger] r.gamma(
                x - y,
            ) by {
                assert(n.gamma(-y));
                assert(r.gamma(x + (-y)));
            }
        }
        r
    }

    /// Zero flag shared by the placeholder divisions.
    fn div_flag(d: &Self) -> (r: (BotOr<Self>, DivZero))
        requires
            d.wf(),
        ensures
            r.0.wf(),
            forall|c: int| #[trigger] r.0.gamma(c) <== !(r.0 is Bot),
            r.1 is Never ==> !d.gamma(0),
            r.1 is Always ==> forall|y: int| #[trigger] d.gamma(y) ==> y == 0,
            (r.0 is Bot) <==> (r.1 is Always),
    {
        let zero_singleton = match (&d.lo, &d.hi) {
            (Lo::Fin(a), Hi::Fin(b)) => a.is_zero() && b.is_zero(),
            _ => false,
        };
        if zero_singleton {
            (BotOr::Bot, DivZero::Always)
        } else if d.contains_zero_int() {
            (BotOr::Val(Self::top()), DivZero::Maybe)
        } else {
            (BotOr::Val(Self::top()), DivZero::Never)
        }
    }

    fn contains_zero_int(&self) -> (b: bool)
        requires
            self.wf(),
        ensures
            b == self.gamma(0),
    {
        let lo_ok0 = match &self.lo {
            Lo::NegInf => true,
            Lo::Fin(a) => {
                let z = IBig::from_i64(0);
                a.le(&z)
            },
        };
        let hi_ok0 = match &self.hi {
            Hi::PosInf => true,
            Hi::Fin(b) => {
                let z = IBig::from_i64(0);
                z.le(b)
            },
        };
        lo_ok0 && hi_ok0
    }
}

impl Domain for IntervalZ {
    type C = int;

    open spec fn wf(&self) -> bool {
        match (self.lo(), self.hi()) {
            (Lo::Fin(a), Hi::Fin(b)) => a.view() <= b.view(),
            _ => true,
        }
    }

    open spec fn gamma(&self, c: int) -> bool {
        lo_ok(self.lo(), c) && hi_ok(self.hi(), c)
    }

    proof fn lemma_nonempty(&self) {
        match (self.lo, self.hi) {
            (Lo::Fin(a), _) => assert(self.gamma(a.view())),
            (Lo::NegInf, Hi::Fin(b)) => assert(self.gamma(b.view())),
            (Lo::NegInf, Hi::PosInf) => assert(self.gamma(0)),
        }
    }

    proof fn lemma_canonical(a: &Self, b: &Self) {
        // Each bound is fixed by the set: equal finite bounds are the extreme
        // members; a finite bound against an infinite one is refuted by a
        // member beyond it.
        match (a.lo, b.lo) {
            (Lo::Fin(x), Lo::Fin(y)) => {
                assert(a.gamma(x.view()) && b.gamma(y.view()));
                assert(a.gamma(y.view()) == b.gamma(y.view()));
                IBig::axiom_view_injective(&x, &y);
            },
            (Lo::Fin(x), Lo::NegInf) => {
                let w = match b.hi {
                    Hi::Fin(h) => if h.view() < x.view() {
                        h.view()
                    } else {
                        x.view() - 1
                    },
                    Hi::PosInf => x.view() - 1,
                };
                assert(b.gamma(w) && a.gamma(w) == b.gamma(w));
            },
            (Lo::NegInf, Lo::Fin(y)) => {
                let w = match a.hi {
                    Hi::Fin(h) => if h.view() < y.view() {
                        h.view()
                    } else {
                        y.view() - 1
                    },
                    Hi::PosInf => y.view() - 1,
                };
                assert(a.gamma(w));
            },
            _ => {},
        }
        match (a.hi, b.hi) {
            (Hi::Fin(x), Hi::Fin(y)) => {
                assert(a.gamma(x.view()) && b.gamma(y.view()));
                assert(a.gamma(y.view()) == b.gamma(y.view()));
                IBig::axiom_view_injective(&x, &y);
            },
            (Hi::Fin(x), Hi::PosInf) => {
                let w = match b.lo {
                    Lo::Fin(l) => if l.view() > x.view() {
                        l.view()
                    } else {
                        x.view() + 1
                    },
                    Lo::NegInf => x.view() + 1,
                };
                assert(b.gamma(w) && a.gamma(w) == b.gamma(w));
            },
            (Hi::PosInf, Hi::Fin(y)) => {
                let w = match a.lo {
                    Lo::Fin(l) => if l.view() > y.view() {
                        l.view()
                    } else {
                        y.view() + 1
                    },
                    Lo::NegInf => y.view() + 1,
                };
                assert(a.gamma(w));
            },
            _ => {},
        }
    }

    fn dup(&self) -> (r: Self) {
        IntervalZ { lo: dup_lo(&self.lo), hi: dup_hi(&self.hi) }
    }

    fn top() -> (r: Self) {
        IntervalZ { lo: Lo::NegInf, hi: Hi::PosInf }
    }

    fn leq(&self, o: &Self) -> (b: bool) {
        lo_le(&o.lo, &self.lo) && hi_le(&self.hi, &o.hi)
    }

    fn join(&self, o: &Self) -> (r: Self) {
        let lo = if lo_le(&self.lo, &o.lo) {
            dup_lo(&self.lo)
        } else {
            dup_lo(&o.lo)
        };
        let hi = if hi_le(&self.hi, &o.hi) {
            dup_hi(&o.hi)
        } else {
            dup_hi(&self.hi)
        };
        IntervalZ { lo, hi }
    }

    fn meet(&self, o: &Self) -> (r: BotOr<Self>) {
        let lo = if lo_le(&self.lo, &o.lo) {
            dup_lo(&o.lo)
        } else {
            dup_lo(&self.lo)
        };
        let hi = if hi_le(&self.hi, &o.hi) {
            dup_hi(&self.hi)
        } else {
            dup_hi(&o.hi)
        };
        let ok = match (&lo, &hi) {
            (Lo::Fin(a), Hi::Fin(b)) => a.le(b),
            _ => true,
        };
        if ok {
            BotOr::Val(IntervalZ { lo, hi })
        } else {
            proof {
                assert forall|c: int| #[trigger] self.gamma(c) implies !o.gamma(c) by {
                    if self.gamma(c) && o.gamma(c) {
                        assert(lo_ok(lo, c) && hi_ok(hi, c));
                    }
                }
            }
            BotOr::Bot
        }
    }

    /// Cousot-Cousot widening: an unstable bound jumps to infinity.
    fn widen(&self, o: &Self) -> (r: Self) {
        let lo = if lo_le(&self.lo, &o.lo) {
            dup_lo(&self.lo)
        } else {
            Lo::NegInf
        };
        let hi = if hi_le(&o.hi, &self.hi) {
            dup_hi(&self.hi)
        } else {
            Hi::PosInf
        };
        IntervalZ { lo, hi }
    }
}

impl Arith<Euclid> for IntervalZ {
    fn add(&self, o: &Self) -> (r: Self) {
        self.add_int(o)
    }

    fn sub(&self, o: &Self) -> (r: Self) {
        self.sub_int(o)
    }

    fn neg(&self) -> (r: Self) {
        self.neg_int()
    }
}

impl Arith<Trunc> for IntervalZ {
    fn add(&self, o: &Self) -> (r: Self) {
        self.add_int(o)
    }

    fn sub(&self, o: &Self) -> (r: Self) {
        self.sub_int(o)
    }

    fn neg(&self) -> (r: Self) {
        self.neg_int()
    }
}

impl DivRem<Euclid> for IntervalZ {
    fn contains_zero(&self) -> (b: bool) {
        self.contains_zero_int()
    }

    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        Self::div_flag(d)
    }

    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        Self::div_flag(d)
    }
}

impl DivRem<Trunc> for IntervalZ {
    fn contains_zero(&self) -> (b: bool) {
        self.contains_zero_int()
    }

    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        Self::div_flag(d)
    }

    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        Self::div_flag(d)
    }
}

} // verus!
