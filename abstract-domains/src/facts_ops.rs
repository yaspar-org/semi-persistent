// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Forward transfers on `Facts<W>`.
//!
//! Unsigned add/sub/neg transfer both interval and congruence fields, then
//! normalize their intersection. Other transfers retain their interval-based
//! behavior (doc/reduced-product.md).
// Proof-only bindings are erased outside Verus.
#![allow(unused_variables)]
use crate::bool4::*;
use crate::congruence::Congruence;
use crate::facts::*;
use crate::interval::*;
use crate::lattice::*;
use crate::reduce::*;
use crate::semantics::*;
use crate::transfer::*;
use crate::word::*;
use vstd::prelude::*;

verus! {

/// Wraps a sound interval result as a normalized record. A `Bot` from
/// `normalize` means the result set is empty, so any value is sound.
fn lift<W: Word>(u: Interval<W>) -> (r: Facts<W>)
    requires
        u.wf(),
    ensures
        r.wf(),
        forall|x: W| u.gamma(x) ==> #[trigger] r.gamma(x),
{
    let f = Facts::from_interval(u);
    proof {
        f.lemma_wf_pre();
    }
    let n = f.normalize();
    match n {
        BotOr::Val(r) => {
            proof {
                assert forall|x: W| u.gamma(x) implies #[trigger] r.gamma(x) by {
                    assert(f.gamma(x) && n.gamma(x));
                }
            }
            r
        },
        BotOr::Bot => {
            proof {
                assert forall|x: W| u.gamma(x) implies false by {
                    assert(f.gamma(x) && n.gamma(x));
                }
            }
            Facts::top()
        },
    }
}

/// Combine independently sound fields. An empty intersection has no concrete
/// result to preserve, so Top is a sound fallback for the bottomless return type.
fn lift_parts<W: Word>(u: Interval<W>, c: Congruence<W>) -> (r: Facts<W>)
    requires
        u.wf(),
        c.wf(),
    ensures
        r.wf(),
        forall|x: W| u.gamma(x) && c.gamma(x) ==> #[trigger] r.gamma(x),
{
    let n = Facts::from_parts(u, c);
    match n {
        BotOr::Val(r) => {
            proof {
                assert forall|x: W| u.gamma(x) && c.gamma(x) implies #[trigger] r.gamma(x) by {
                    assert(n.gamma(x));
                }
            }
            r
        },
        BotOr::Bot => {
            proof {
                assert forall|x: W| u.gamma(x) && c.gamma(x) implies false by {
                    assert(n.gamma(x));
                }
            }
            Facts::top()
        },
    }
}

/// Lifts a division result from the `u` field.
fn lift_div<W: Word>(q: (BotOr<Interval<W>>, DivZero)) -> (r: (BotOr<Facts<W>>, DivZero))
    requires
        q.0.wf(),
    ensures
        r.0.wf(),
        forall|x: W| q.0.gamma(x) ==> #[trigger] r.0.gamma(x),
        r.1 == q.1,
        (r.0 is Bot) <==> (q.0 is Bot),
{
    match q.0 {
        BotOr::Bot => (BotOr::Bot, q.1),
        BotOr::Val(u) => {
            let r = lift(u);
            proof {
                assert forall|x: W| q.0.gamma(x) implies #[trigger] BotOr::<Facts<W>>::Val(
                    r,
                ).gamma(x) by {
                    assert(u.gamma(x));
                }
            }
            (BotOr::Val(r), q.1)
        },
    }
}

impl<W: Word> Arith<Unsigned<W>> for Facts<W> {
    fn add(&self, o: &Self) -> (r: Self) {
        let (ua, ub) = (self.interval(), o.interval());
        let (ca, cb) = (self.congruence(), o.congruence());
        let u = <Interval<W> as Arith<Unsigned<W>>>::add(&ua, &ub);
        let c = ca.add(&cb);
        let r = lift_parts(u, c);
        proof {
            assert forall|x: W, y: W| self.gamma(x) && o.gamma(y)
                implies #[trigger] r.gamma(Unsigned::<W>::add(x, y)) by {
                assert(ua.gamma(x) && ub.gamma(y));
                assert(ca.has(x) && cb.has(y));
                assert(u.gamma(Unsigned::<W>::add(x, y)));
                assert(c.has(Unsigned::<W>::add(x, y)));
            }
        }
        r
    }

    fn sub(&self, o: &Self) -> (r: Self) {
        let (ua, ub) = (self.interval(), o.interval());
        let (ca, cb) = (self.congruence(), o.congruence());
        let u = <Interval<W> as Arith<Unsigned<W>>>::sub(&ua, &ub);
        let c = ca.sub(&cb);
        let r = lift_parts(u, c);
        proof {
            assert forall|x: W, y: W| self.gamma(x) && o.gamma(y)
                implies #[trigger] r.gamma(Unsigned::<W>::sub(x, y)) by {
                assert(ua.gamma(x) && ub.gamma(y));
                assert(ca.has(x) && cb.has(y));
                assert(u.gamma(Unsigned::<W>::sub(x, y)));
                assert(c.has(Unsigned::<W>::sub(x, y)));
            }
        }
        r
    }

    fn neg(&self) -> (r: Self) {
        let ua = self.interval();
        let ca = self.congruence();
        let u = <Interval<W> as Arith<Unsigned<W>>>::neg(&ua);
        let c = ca.neg();
        let r = lift_parts(u, c);
        proof {
            assert forall|x: W| self.gamma(x) implies #[trigger] r.gamma(Unsigned::<W>::neg(x)) by {
                assert(ua.gamma(x) && ca.has(x));
                assert(u.gamma(Unsigned::<W>::neg(x)));
                assert(c.has(Unsigned::<W>::neg(x)));
            }
        }
        r
    }
}

impl<W: Word> Mul<Unsigned<W>> for Facts<W> {
    fn mul(&self, o: &Self) -> (r: Self) {
        lift(<Interval<W> as Mul<Unsigned<W>>>::mul(&self.interval(), &o.interval()))
    }
}

impl<W: Word> DivRem<Unsigned<W>> for Facts<W> {
    fn contains_zero(&self) -> (b: bool) {
        let u = self.interval();
        let z = W::zero();
        proof {
            W::lemma_modulus();
            W::lemma_from_int(0);
            W::lemma_view_injective(z, W::from_int(0));
        }
        <Interval<W> as DivRem<Unsigned<W>>>::contains_zero(&u) && self.congruence().contains(z)
    }

    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let (u, du) = (self.interval(), d.interval());
        lift_div(<Interval<W> as DivRem<Unsigned<W>>>::div(&u, &du))
    }

    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let (u, du) = (self.interval(), d.interval());
        lift_div(<Interval<W> as DivRem<Unsigned<W>>>::rem(&u, &du))
    }
}

impl<W: Word> DivRem<Signed<W>> for Facts<W> {
    fn contains_zero(&self) -> (b: bool) {
        let u = self.interval();
        let z = W::zero();
        proof {
            W::lemma_modulus();
            W::lemma_from_int(0);
            W::lemma_view_injective(z, W::from_int(0));
        }
        <Interval<W> as DivRem<Signed<W>>>::contains_zero(&u) && self.congruence().contains(z)
    }

    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let (u, du) = (self.interval(), d.interval());
        lift_div(<Interval<W> as DivRem<Signed<W>>>::div(&u, &du))
    }

    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero)) {
        let (u, du) = (self.interval(), d.interval());
        lift_div(<Interval<W> as DivRem<Signed<W>>>::rem(&u, &du))
    }
}

/// Stub: forward answers `Top`, backward keeps both operands. The planned work
/// replaces it with transfers on the `u` field (doc/reduced-product.md).
impl<W: Word> Compare<Unsigned<W>> for Facts<W> {
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
/// replaces it with transfers on the `u` field (doc/reduced-product.md).
impl<W: Word> Compare<Signed<W>> for Facts<W> {
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
