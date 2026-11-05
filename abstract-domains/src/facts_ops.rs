// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Forward transfers on `Facts<W>`.
//!
//! Starting point for the BitVec transfers (doc/reduced-product.md): each transfer
//! applies the `u` field's transfer and normalizes. A transfer for a new field
//! computes that field from the operands' fields; `normalize` then combines it
//! with the others.
// Proof-only bindings are erased outside Verus.
#![allow(unused_variables)]
use crate::bool4::*;
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

// TODO(abs-domain-registry): add Bitwise (bvand bvor bvxor bvnot) and Shift (bvshl bvlshr bvashr) impls for Facts<W>, and backward transfers for every operator here, see abstract-domains/doc/future/registry-task.md §4
impl<W: Word> Arith<Unsigned<W>> for Facts<W> {
    fn add(&self, o: &Self) -> (r: Self) {
        lift(<Interval<W> as Arith<Unsigned<W>>>::add(&self.interval(), &o.interval()))
    }

    fn sub(&self, o: &Self) -> (r: Self) {
        lift(<Interval<W> as Arith<Unsigned<W>>>::sub(&self.interval(), &o.interval()))
    }

    fn neg(&self) -> (r: Self) {
        lift(<Interval<W> as Arith<Unsigned<W>>>::neg(&self.interval()))
    }
}

impl<W: Word> Mul<Unsigned<W>> for Facts<W> {
    fn mul(&self, o: &Self) -> (r: Self) {
        lift(<Interval<W> as Mul<Unsigned<W>>>::mul(&self.interval(), &o.interval()))
    }
}

// TODO(abs-domain-registry): bvudiv/bvurem: the contract excludes zero divisors; the registry joins the SMT-LIB value (all ones, x) when the flag is not Never, see abstract-domains/doc/future/registry-task.md §4
impl<W: Word> DivRem<Unsigned<W>> for Facts<W> {
    fn contains_zero(&self) -> (b: bool) {
        let u = self.interval();
        <Interval<W> as DivRem<Unsigned<W>>>::contains_zero(&u)
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

// TODO(abs-domain-registry): bvsdiv/bvsrem read a placeholder (top); bvsmod has no transfer and no Semantics operator, see abstract-domains/doc/future/registry-task.md §4
impl<W: Word> DivRem<Signed<W>> for Facts<W> {
    fn contains_zero(&self) -> (b: bool) {
        let u = self.interval();
        <Interval<W> as DivRem<Signed<W>>>::contains_zero(&u)
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

// TODO(abs-domain-registry): replace this stub (bvult, bvule, `=`) with forward and backward transfers on `u`, see abstract-domains/doc/future/registry-task.md §4
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

// TODO(abs-domain-registry): replace this stub (bvslt, bvsle) with forward and backward transfers on `u` and the planned `s`, see abstract-domains/doc/future/registry-task.md §4
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
