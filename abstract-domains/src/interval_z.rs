// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! IntervalZ: closed intervals over unbounded integers, with explicit infinities.
//!
//! Practicum §2 / §3.2:
//!
//! ```text
//! Bound     = NegInf | Fin(IBig) | PosInf
//! IntervalZ = { empty, lo: Bound, hi: Bound }
//! values    = every integer z with lo <= z <= hi   (empty has none)
//! ```
//!
//! Nothing wraps. Addition, subtraction and multiplication are exact on
//! endpoints, including infinities: a product is the min/max of the four
//! endpoint products in the extended integers (`0 * ±∞` contributes `0`,
//! which is the corner a zero endpoint actually takes). Division splits a
//! divisor that contains 0 into `(−∞, −1]` and `[1, +∞)`, divides each side
//! by the four Euclidean endpoint quotients, and joins; the alarm is the
//! concretization lattice (`NoError` ⟂ `DefiniteError`, join `MaybeError`).
//!
//! `widen` jumps an unstable endpoint to `±∞` (the operator already in this
//! module). It is not claimed monotone. Termination of a descending meet
//! chain is the per-class fuel: a strict meet spends one unit, a stable
//! meet spends none, and fuel 0 keeps the current value.
//!
//! UBig is the same interval with `lo >= 0` in `wf_ubig`, not a second
//! domain. RBig is `IntervalR`: the same bounds plus open/closed endpoints.

use crate::ibig::IBig;
use vstd::prelude::*;

verus! {

broadcast use crate::ibig::group_ibig_axioms;

// ---------------------------------------------------------------------------
// Bounds
// ---------------------------------------------------------------------------

/// Three-way bound: −∞, a finite unbounded integer, or +∞.
pub enum Bound {
    NegInf,
    Fin(IBig),
    PosInf,
}

pub open spec fn bound_le(a: Bound, b: Bound) -> bool {
    match (a, b) {
        (Bound::NegInf, _) => true,
        (_, Bound::PosInf) => true,
        (Bound::PosInf, Bound::NegInf) => false,
        (Bound::PosInf, Bound::Fin(_)) => false,
        (Bound::Fin(_), Bound::NegInf) => false,
        (Bound::Fin(x), Bound::Fin(y)) => x.view() <= y.view(),
    }
}

pub open spec fn bound_eq(a: Bound, b: Bound) -> bool {
    match (a, b) {
        (Bound::NegInf, Bound::NegInf) => true,
        (Bound::PosInf, Bound::PosInf) => true,
        (Bound::Fin(x), Bound::Fin(y)) => x.view() == y.view(),
        _ => false,
    }
}

pub open spec fn bound_lt(a: Bound, b: Bound) -> bool {
    bound_le(a, b) && !bound_eq(a, b)
}

pub open spec fn bound_min(a: Bound, b: Bound) -> Bound {
    if bound_le(a, b) { a } else { b }
}

pub open spec fn bound_max(a: Bound, b: Bound) -> Bound {
    if bound_le(a, b) { b } else { a }
}

pub open spec fn bound_le_int(b: Bound, z: int) -> bool {
    match b {
        Bound::NegInf => true,
        Bound::Fin(n) => n.view() <= z,
        Bound::PosInf => false,
    }
}

pub open spec fn int_le_bound(z: int, b: Bound) -> bool {
    match b {
        Bound::PosInf => true,
        Bound::Fin(n) => z <= n.view(),
        Bound::NegInf => false,
    }
}

/// Extended product of two endpoints. `0 * ±∞ = 0`: that corner is the
/// products of a zero endpoint, not an indeterminate form.
pub open spec fn ext_mul_spec(a: Bound, b: Bound) -> Bound {
    match (a, b) {
        (Bound::Fin(x), Bound::Fin(y)) => Bound::Fin(IBig::from_int(x.view() * y.view())),
        (Bound::Fin(x), Bound::PosInf) | (Bound::PosInf, Bound::Fin(x)) => if x.view() == 0 {
            Bound::Fin(IBig::from_int(0))
        } else if x.view() > 0 {
            Bound::PosInf
        } else {
            Bound::NegInf
        },
        (Bound::Fin(x), Bound::NegInf) | (Bound::NegInf, Bound::Fin(x)) => if x.view() == 0 {
            Bound::Fin(IBig::from_int(0))
        } else if x.view() > 0 {
            Bound::NegInf
        } else {
            Bound::PosInf
        },
        (Bound::PosInf, Bound::PosInf) | (Bound::NegInf, Bound::NegInf) => Bound::PosInf,
        (Bound::PosInf, Bound::NegInf) | (Bound::NegInf, Bound::PosInf) => Bound::NegInf,
    }
}

/// Extended Euclidean quotient of two endpoints. `None` is division by a
/// zero endpoint. A finite dividend over `±∞` is `0`.
pub open spec fn ext_div_spec(n: Bound, d: Bound) -> Option<Bound> {
    match d {
        Bound::Fin(z) => if z.view() == 0 {
            None
        } else {
            match n {
                Bound::Fin(a) => Some(Bound::Fin(IBig::from_int(a.view() / z.view()))),
                Bound::PosInf => Some(if z.view() < 0 { Bound::NegInf } else { Bound::PosInf }),
                Bound::NegInf => Some(if z.view() < 0 { Bound::PosInf } else { Bound::NegInf }),
            }
        },
        Bound::PosInf => match n {
            Bound::Fin(_) => Some(Bound::Fin(IBig::from_int(0))),
            Bound::PosInf => Some(Bound::PosInf),
            Bound::NegInf => Some(Bound::NegInf),
        },
        Bound::NegInf => match n {
            Bound::Fin(_) => Some(Bound::Fin(IBig::from_int(0))),
            Bound::PosInf => Some(Bound::NegInf),
            Bound::NegInf => Some(Bound::PosInf),
        },
    }
}

pub open spec fn add_bound_spec(a: Bound, b: Bound) -> Bound {
    match (a, b) {
        (Bound::NegInf, Bound::PosInf) => Bound::NegInf,
        (Bound::PosInf, Bound::NegInf) => Bound::PosInf,
        (Bound::NegInf, _) => Bound::NegInf,
        (_, Bound::NegInf) => Bound::NegInf,
        (Bound::PosInf, _) => Bound::PosInf,
        (_, Bound::PosInf) => Bound::PosInf,
        (Bound::Fin(x), Bound::Fin(y)) => Bound::Fin(IBig::from_int(x.view() + y.view())),
    }
}

pub open spec fn neg_bound_spec(a: Bound) -> Bound {
    match a {
        Bound::NegInf => Bound::PosInf,
        Bound::PosInf => Bound::NegInf,
        Bound::Fin(n) => Bound::Fin(IBig::from_int(-n.view())),
    }
}

impl Bound {
    pub fn fin(n: i64) -> (r: Bound)
        ensures
            r == Bound::Fin(IBig::from_int(n as int)),
    {
        Bound::Fin(IBig::from_i64(n))
    }

    pub fn clone_bound(&self) -> (r: Bound)
        ensures
            r == *self,
    {
        match self {
            Bound::NegInf => Bound::NegInf,
            Bound::PosInf => Bound::PosInf,
            Bound::Fin(n) => Bound::Fin(n.clone_ibig()),
        }
    }

    pub fn le(&self, other: &Bound) -> (r: bool)
        ensures
            r == bound_le(*self, *other),
    {
        match (self, other) {
            (Bound::NegInf, _) => true,
            (_, Bound::PosInf) => true,
            (Bound::PosInf, Bound::NegInf) => false,
            (Bound::PosInf, Bound::Fin(_)) => false,
            (Bound::Fin(_), Bound::NegInf) => false,
            (Bound::Fin(x), Bound::Fin(y)) => x.le(y),
        }
    }

    pub fn eq_bound(&self, other: &Bound) -> (r: bool)
        ensures
            r == bound_eq(*self, *other),
    {
        match (self, other) {
            (Bound::NegInf, Bound::NegInf) => true,
            (Bound::PosInf, Bound::PosInf) => true,
            (Bound::Fin(x), Bound::Fin(y)) => x.eq_int(y),
            _ => false,
        }
    }

    pub fn lt(&self, other: &Bound) -> (r: bool)
        ensures
            r == bound_lt(*self, *other),
    {
        self.le(other) && !self.eq_bound(other)
    }

    pub fn min(&self, other: &Bound) -> (r: Bound)
        ensures
            r == bound_min(*self, *other),
    {
        if self.le(other) { self.clone_bound() } else { other.clone_bound() }
    }

    pub fn max(&self, other: &Bound) -> (r: Bound)
        ensures
            r == bound_max(*self, *other),
    {
        if self.le(other) { other.clone_bound() } else { self.clone_bound() }
    }

    pub fn add(&self, other: &Bound) -> (r: Bound)
        ensures
            r == add_bound_spec(*self, *other),
    {
        match (self, other) {
            (Bound::NegInf, Bound::PosInf) => Bound::NegInf,
            (Bound::PosInf, Bound::NegInf) => Bound::PosInf,
            (Bound::NegInf, _) => Bound::NegInf,
            (_, Bound::NegInf) => Bound::NegInf,
            (Bound::PosInf, _) => Bound::PosInf,
            (_, Bound::PosInf) => Bound::PosInf,
            (Bound::Fin(x), Bound::Fin(y)) => Bound::Fin(x.add(y)),
        }
    }

    pub fn neg(&self) -> (r: Bound)
        ensures
            r == neg_bound_spec(*self),
    {
        match self {
            Bound::NegInf => Bound::PosInf,
            Bound::PosInf => Bound::NegInf,
            Bound::Fin(n) => Bound::Fin(n.neg()),
        }
    }

    pub fn ext_mul(&self, other: &Bound) -> (r: Bound)
        ensures
            r == ext_mul_spec(*self, *other),
    {
        match (self, other) {
            (Bound::Fin(x), Bound::Fin(y)) => Bound::Fin(x.mul(y)),
            (Bound::Fin(x), Bound::PosInf) | (Bound::PosInf, Bound::Fin(x)) => if x.is_zero() {
                Bound::fin(0)
            } else if x.is_pos() {
                Bound::PosInf
            } else {
                Bound::NegInf
            },
            (Bound::Fin(x), Bound::NegInf) | (Bound::NegInf, Bound::Fin(x)) => if x.is_zero() {
                Bound::fin(0)
            } else if x.is_pos() {
                Bound::NegInf
            } else {
                Bound::PosInf
            },
            (Bound::PosInf, Bound::PosInf) | (Bound::NegInf, Bound::NegInf) => Bound::PosInf,
            (Bound::PosInf, Bound::NegInf) | (Bound::NegInf, Bound::PosInf) => Bound::NegInf,
        }
    }

    pub fn ext_div(&self, d: &Bound) -> (r: Option<Bound>)
        ensures
            r == ext_div_spec(*self, *d),
    {
        match d {
            Bound::Fin(z) => if z.is_zero() {
                None
            } else {
                match self {
                    Bound::Fin(a) => Some(Bound::Fin(a.div_euclid(z))),
                    Bound::PosInf => Some(if z.is_neg() { Bound::NegInf } else { Bound::PosInf }),
                    Bound::NegInf => Some(if z.is_neg() { Bound::PosInf } else { Bound::NegInf }),
                }
            },
            Bound::PosInf => match self {
                Bound::Fin(_) => Some(Bound::fin(0)),
                Bound::PosInf => Some(Bound::PosInf),
                Bound::NegInf => Some(Bound::NegInf),
            },
            Bound::NegInf => match self {
                Bound::Fin(_) => Some(Bound::fin(0)),
                Bound::PosInf => Some(Bound::NegInf),
                Bound::NegInf => Some(Bound::PosInf),
            },
        }
    }
}

pub proof fn bound_le_refl(a: Bound)
    ensures
        bound_le(a, a),
{
}

pub proof fn bound_le_total(a: Bound, b: Bound)
    ensures
        bound_le(a, b) || bound_le(b, a),
{
}

pub proof fn bound_min_comm(a: Bound, b: Bound)
    ensures
        bound_min(a, b) == bound_min(b, a),
{
    if bound_le(a, b) && bound_le(b, a) {
        bound_le_antisym(a, b);
    }
}

pub proof fn bound_max_comm(a: Bound, b: Bound)
    ensures
        bound_max(a, b) == bound_max(b, a),
{
    if bound_le(a, b) && bound_le(b, a) {
        bound_le_antisym(a, b);
    }
}

pub proof fn bound_le_antisym(a: Bound, b: Bound)
    requires
        bound_le(a, b),
        bound_le(b, a),
    ensures
        a == b,
{
    match (a, b) {
        (Bound::Fin(x), Bound::Fin(y)) => {
            axiom_ibig_view_surj_use(x);
            axiom_ibig_view_surj_use(y);
            assert(x.view() == y.view());
            assert(x == IBig::from_int(x.view()));
            assert(y == IBig::from_int(y.view()));
        },
        (Bound::NegInf, Bound::NegInf) => {},
        (Bound::PosInf, Bound::PosInf) => {},
        _ => {
            assert(bound_le(a, b) && bound_le(b, a));
            assert(false);
        },
    }
}

pub proof fn axiom_ibig_view_surj_use(a: IBig)
    ensures
        a == IBig::from_int(a.view()),
{
    crate::ibig::axiom_ibig_view_surj(a);
}

// ---------------------------------------------------------------------------
// Alarm lattice (concretization, not severity)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Alarm {
    NoError,
    DefiniteError,
    MaybeError,
}

impl Alarm {
    pub open spec fn has(self, err: bool) -> bool {
        match self {
            Alarm::NoError => !err,
            Alarm::DefiniteError => err,
            Alarm::MaybeError => true,
        }
    }

    pub open spec fn join_spec(self, other: Alarm) -> Alarm {
        match (self, other) {
            (Alarm::MaybeError, _) => Alarm::MaybeError,
            (_, Alarm::MaybeError) => Alarm::MaybeError,
            (Alarm::NoError, Alarm::NoError) => Alarm::NoError,
            (Alarm::DefiniteError, Alarm::DefiniteError) => Alarm::DefiniteError,
            (Alarm::NoError, Alarm::DefiniteError) => Alarm::MaybeError,
            (Alarm::DefiniteError, Alarm::NoError) => Alarm::MaybeError,
        }
    }

    pub fn join(self, other: Alarm) -> (r: Alarm)
        ensures
            r == self.join_spec(other),
            forall|e: bool| #![auto] self.has(e) || other.has(e) ==> r.has(e),
    {
        match (self, other) {
            (Alarm::MaybeError, _) => Alarm::MaybeError,
            (_, Alarm::MaybeError) => Alarm::MaybeError,
            (Alarm::NoError, Alarm::NoError) => Alarm::NoError,
            (Alarm::DefiniteError, Alarm::DefiniteError) => Alarm::DefiniteError,
            (Alarm::NoError, Alarm::DefiniteError) => Alarm::MaybeError,
            (Alarm::DefiniteError, Alarm::NoError) => Alarm::MaybeError,
        }
    }
}

pub proof fn alarm_join_safe_and_definite_is_maybe()
    ensures
        Alarm::NoError.join_spec(Alarm::DefiniteError) == Alarm::MaybeError,
{
}

// ---------------------------------------------------------------------------
// IntervalZ
// ---------------------------------------------------------------------------

pub struct IntervalZ {
    pub empty: bool,
    pub lo: Bound,
    pub hi: Bound,
}

impl IntervalZ {
    pub open spec fn wf(self) -> bool {
        self.empty || (bound_le(self.lo, self.hi) && self.lo != Bound::PosInf && self.hi
            != Bound::NegInf)
    }

    /// UBig well-formedness: the same interval, with `lo >= 0`.
    pub open spec fn wf_ubig(self) -> bool {
        self.wf() && (self.empty || bound_le(Bound::Fin(IBig::from_int(0)), self.lo))
    }

    pub open spec fn has(self, z: int) -> bool {
        !self.empty && bound_le_int(self.lo, z) && int_le_bound(z, self.hi)
    }

    pub open spec fn refines(self, other: IntervalZ) -> bool {
        forall|z: int| #![auto] self.has(z) ==> other.has(z)
    }

    pub open spec fn eq_abs(self, other: IntervalZ) -> bool {
        (self.empty && other.empty) || (!self.empty && !other.empty && bound_eq(self.lo, other.lo)
            && bound_eq(self.hi, other.hi))
    }

    pub open spec fn bottom_spec() -> IntervalZ {
        IntervalZ {
            empty: true,
            lo: Bound::Fin(IBig::from_int(0)),
            hi: Bound::Fin(IBig::from_int(0)),
        }
    }

    pub open spec fn top_spec() -> IntervalZ {
        IntervalZ { empty: false, lo: Bound::NegInf, hi: Bound::PosInf }
    }

    pub open spec fn arith_spec(lo: Bound, hi: Bound) -> IntervalZ {
        if lo == Bound::PosInf || hi == Bound::NegInf || !bound_le(lo, hi) {
            IntervalZ::top_spec()
        } else {
            IntervalZ { empty: false, lo, hi }
        }
    }

    pub fn bottom() -> (r: IntervalZ)
        ensures
            r.wf(),
            r == IntervalZ::bottom_spec(),
            forall|z: int| #![auto] !r.has(z),
    {
        IntervalZ { empty: true, lo: Bound::fin(0), hi: Bound::fin(0) }
    }

    pub fn top() -> (r: IntervalZ)
        ensures
            r.wf(),
            r == IntervalZ::top_spec(),
            forall|z: int| #![auto] r.has(z),
    {
        IntervalZ { empty: false, lo: Bound::NegInf, hi: Bound::PosInf }
    }

    pub fn clone_iv(&self) -> (r: IntervalZ)
        ensures
            r == *self,
    {
        IntervalZ { empty: self.empty, lo: self.lo.clone_bound(), hi: self.hi.clone_bound() }
    }

    pub fn constant(n: i64) -> (r: IntervalZ)
        ensures
            r.wf(),
            !r.empty,
            r.has(n as int),
            r.lo == Bound::Fin(IBig::from_int(n as int)),
            r.hi == Bound::Fin(IBig::from_int(n as int)),
    {
        let b = Bound::fin(n);
        IntervalZ { empty: false, lo: b.clone_bound(), hi: b }
    }

    /// Well-formed range. `lo > hi`, or a `PosInf` lower / `NegInf` upper, is bottom.
    pub fn range(lo: Bound, hi: Bound) -> (r: IntervalZ)
        ensures
            r.wf(),
            !bound_le(lo, hi) || lo == Bound::PosInf || hi == Bound::NegInf ==> r.empty,
            bound_le(lo, hi) && lo != Bound::PosInf && hi != Bound::NegInf ==> !r.empty && r.lo
                == lo && r.hi == hi,
    {
        if lo.le(&hi) {
            match (&lo, &hi) {
                (Bound::PosInf, _) => IntervalZ::bottom(),
                (_, Bound::NegInf) => IntervalZ::bottom(),
                _ => IntervalZ { empty: false, lo, hi },
            }
        } else {
            IntervalZ::bottom()
        }
    }

    /// Arithmetic hull. A `PosInf` lower bound (or a crossed pair) becomes top.
    pub fn arith(lo: Bound, hi: Bound) -> (r: IntervalZ)
        ensures
            r.wf(),
            r == IntervalZ::arith_spec(lo, hi),
    {
        if matches!(lo, Bound::PosInf) || matches!(hi, Bound::NegInf) || !lo.le(&hi) {
            IntervalZ::top()
        } else {
            IntervalZ { empty: false, lo, hi }
        }
    }

    pub fn contains(&self, x: i64) -> (r: bool)
        ensures
            r == self.has(x as int),
    {
        if self.empty {
            false
        } else {
            bound_le_int_exec(&self.lo, x) && int_le_bound_exec(x, &self.hi)
        }
    }

    pub fn eq_abs_exec(&self, other: &IntervalZ) -> (r: bool)
        ensures
            r == self.eq_abs(*other),
    {
        if self.empty && other.empty {
            true
        } else if !self.empty && !other.empty {
            self.lo.eq_bound(&other.lo) && self.hi.eq_bound(&other.hi)
        } else {
            false
        }
    }

    pub open spec fn is_finite(self) -> bool {
        !self.empty && is_fin_bound(self.lo) && is_fin_bound(self.hi)
    }

    pub fn is_zero(&self) -> (r: bool)
        ensures
            r == is_zero_singleton(*self),
    {
        match (self.empty, &self.lo, &self.hi) {
            (false, Bound::Fin(x), Bound::Fin(y)) => x.is_zero() && y.is_zero(),
            _ => false,
        }
    }

    // ----- lattice -----

    pub open spec fn meet_spec(self, t: IntervalZ) -> IntervalZ {
        if self.empty || t.empty {
            IntervalZ::bottom_spec()
        } else {
            let lo = bound_max(self.lo, t.lo);
            let hi = bound_min(self.hi, t.hi);
            if !bound_le(lo, hi) || lo == Bound::PosInf || hi == Bound::NegInf {
                IntervalZ::bottom_spec()
            } else {
                IntervalZ { empty: false, lo, hi }
            }
        }
    }

    pub open spec fn join_spec(self, t: IntervalZ) -> IntervalZ {
        if self.empty {
            t
        } else if t.empty {
            self
        } else {
            IntervalZ {
                empty: false,
                lo: bound_min(self.lo, t.lo),
                hi: bound_max(self.hi, t.hi),
            }
        }
    }

    pub fn meet(&self, t: &IntervalZ) -> (r: IntervalZ)
        requires
            self.wf(),
            t.wf(),
        ensures
            r.wf(),
            r.eq_abs(self.meet_spec(*t)),
            forall|z: int| #![auto] r.has(z) ==> self.has(z) && t.has(z),
            forall|z: int| #![auto] self.has(z) && t.has(z) ==> r.has(z),
    {
        if self.empty || t.empty {
            IntervalZ::bottom()
        } else {
            let lo = self.lo.max(&t.lo);
            let hi = self.hi.min(&t.hi);
            let r = if !lo.le(&hi) {
                IntervalZ::bottom()
            } else {
                match (&lo, &hi) {
                    (Bound::PosInf, _) => IntervalZ::bottom(),
                    (_, Bound::NegInf) => IntervalZ::bottom(),
                    _ => IntervalZ { empty: false, lo, hi },
                }
            };
            proof {
                assert forall|z: int| #![auto] self.has(z) && t.has(z) implies r.has(z) by {
                    meet_has_iff(*self, *t, z);
                };
                assert forall|z: int| #![auto] r.has(z) implies self.has(z) && t.has(z) by {
                    meet_has_iff(*self, *t, z);
                };
            }
            r
        }
    }

    pub fn join(&self, t: &IntervalZ) -> (r: IntervalZ)
        requires
            self.wf(),
            t.wf(),
        ensures
            r.wf(),
            r.eq_abs(self.join_spec(*t)),
            forall|z: int| #![auto] self.has(z) ==> r.has(z),
            forall|z: int| #![auto] t.has(z) ==> r.has(z),
    {
        if self.empty {
            t.clone_iv()
        } else if t.empty {
            self.clone_iv()
        } else {
            IntervalZ { empty: false, lo: self.lo.min(&t.lo), hi: self.hi.max(&t.hi) }
        }
    }

    // ----- arithmetic -----

    pub open spec fn add_spec(self, t: IntervalZ) -> IntervalZ {
        if self.empty || t.empty {
            IntervalZ::bottom_spec()
        } else {
            IntervalZ::arith_spec(add_bound_spec(self.lo, t.lo), add_bound_spec(self.hi, t.hi))
        }
    }

    pub open spec fn neg_spec(self) -> IntervalZ {
        if self.empty {
            IntervalZ::bottom_spec()
        } else {
            IntervalZ::arith_spec(neg_bound_spec(self.hi), neg_bound_spec(self.lo))
        }
    }

    pub open spec fn sub_spec(self, t: IntervalZ) -> IntervalZ {
        self.add_spec(t.neg_spec())
    }

    pub open spec fn corner_hull(p1: Bound, p2: Bound, p3: Bound, p4: Bound) -> IntervalZ {
        IntervalZ::arith_spec(
            bound_min(bound_min(p1, p2), bound_min(p3, p4)),
            bound_max(bound_max(p1, p2), bound_max(p3, p4)),
        )
    }

    pub open spec fn mul_spec(self, t: IntervalZ) -> IntervalZ {
        if self.empty || t.empty {
            IntervalZ::bottom_spec()
        } else {
            IntervalZ::corner_hull(
                ext_mul_spec(self.lo, t.lo),
                ext_mul_spec(self.lo, t.hi),
                ext_mul_spec(self.hi, t.lo),
                ext_mul_spec(self.hi, t.hi),
            )
        }
    }

    pub fn add(&self, t: &IntervalZ) -> (r: IntervalZ)
        requires
            self.wf(),
            t.wf(),
        ensures
            r.wf(),
            r == self.add_spec(*t),
            forall|x: int, y: int| #![auto] self.has(x) && t.has(y) ==> r.has(x + y),
    {
        if self.empty || t.empty {
            IntervalZ::bottom()
        } else {
            let r = IntervalZ::arith(self.lo.add(&t.lo), self.hi.add(&t.hi));
            proof {
                lemma_add_contains(*self, *t, r);
            }
            r
        }
    }

    pub fn neg(&self) -> (r: IntervalZ)
        requires
            self.wf(),
        ensures
            r.wf(),
            r == self.neg_spec(),
            forall|x: int| #![auto] self.has(x) ==> r.has(-x),
    {
        if self.empty {
            IntervalZ::bottom()
        } else {
            let r = IntervalZ::arith(self.hi.neg(), self.lo.neg());
            proof {
                lemma_neg_contains(*self, r);
            }
            r
        }
    }

    pub fn sub(&self, t: &IntervalZ) -> (r: IntervalZ)
        requires
            self.wf(),
            t.wf(),
        ensures
            r.wf(),
            r == self.sub_spec(*t),
            forall|x: int, y: int| #![auto] self.has(x) && t.has(y) ==> r.has(x - y),
    {
        let nt = t.neg();
        let r = self.add(&nt);
        proof {
            assert forall|x: int, y: int| #![auto] self.has(x) && t.has(y) implies r.has(x - y)
                by {
                assert(nt.has(-y));
                assert(r.has(x + (-y)));
                assert(x + (-y) == x - y);
            };
        }
        r
    }

    pub fn mul(&self, t: &IntervalZ) -> (r: IntervalZ)
        requires
            self.wf(),
            t.wf(),
        ensures
            r.wf(),
            r == self.mul_spec(*t),
            forall|x: int, y: int| #![auto] self.has(x) && t.has(y) ==> r.has(x * y),
    {
        if self.empty || t.empty {
            IntervalZ::bottom()
        } else {
            let p1 = self.lo.ext_mul(&t.lo);
            let p2 = self.lo.ext_mul(&t.hi);
            let p3 = self.hi.ext_mul(&t.lo);
            let p4 = self.hi.ext_mul(&t.hi);
            let lo = p1.min(&p2).min(&p3.min(&p4));
            let hi = p1.max(&p2).max(&p3.max(&p4));
            let r = IntervalZ::arith(lo, hi);
            proof {
                lemma_mul_contains(*self, *t, r);
            }
            r
        }
    }

    // ----- widen / narrow -----
    // widen: an endpoint that moved outward jumps to ±∞. Not monotone.

    pub open spec fn widen_spec(self, t: IntervalZ) -> IntervalZ {
        if self.empty {
            t
        } else if t.empty {
            self
        } else {
            let lo = if bound_lt(t.lo, self.lo) { Bound::NegInf } else { self.lo };
            let hi = if bound_lt(self.hi, t.hi) { Bound::PosInf } else { self.hi };
            IntervalZ { empty: false, lo, hi }
        }
    }

    pub open spec fn narrow_spec(self, t: IntervalZ) -> IntervalZ {
        if self.empty || t.empty {
            IntervalZ::bottom_spec()
        } else {
            let lo = if self.lo == Bound::NegInf { t.lo } else { self.lo };
            let hi = if self.hi == Bound::PosInf { t.hi } else { self.hi };
            if !bound_le(lo, hi) || lo == Bound::PosInf || hi == Bound::NegInf {
                IntervalZ::bottom_spec()
            } else {
                IntervalZ { empty: false, lo, hi }
            }
        }
    }

    pub fn widen(&self, t: &IntervalZ) -> (r: IntervalZ)
        requires
            self.wf(),
            t.wf(),
        ensures
            r.wf(),
            r.eq_abs(self.widen_spec(*t)),
            self.refines(r),
            t.refines(r),
            self.join_spec(*t).refines(r),
    {
        if self.empty {
            t.clone_iv()
        } else if t.empty {
            self.clone_iv()
        } else {
            let lo = if t.lo.lt(&self.lo) { Bound::NegInf } else { self.lo.clone_bound() };
            let hi = if self.hi.lt(&t.hi) { Bound::PosInf } else { self.hi.clone_bound() };
            let r = IntervalZ { empty: false, lo, hi };
            proof {
                lemma_widen_sound(*self, *t, r);
            }
            r
        }
    }

    pub fn narrow(&self, t: &IntervalZ) -> (r: IntervalZ)
        requires
            self.wf(),
            t.wf(),
        ensures
            r.wf(),
            r.eq_abs(self.narrow_spec(*t)),
            r.refines(*self),
            self.meet_spec(*t).refines(r),
    {
        if self.empty || t.empty {
            IntervalZ::bottom()
        } else {
            let lo = match &self.lo {
                Bound::NegInf => t.lo.clone_bound(),
                _ => self.lo.clone_bound(),
            };
            let hi = match &self.hi {
                Bound::PosInf => t.hi.clone_bound(),
                _ => self.hi.clone_bound(),
            };
            let r = if !lo.le(&hi) {
                IntervalZ::bottom()
            } else {
                match (&lo, &hi) {
                    (Bound::PosInf, _) => IntervalZ::bottom(),
                    (_, Bound::NegInf) => IntervalZ::bottom(),
                    _ => IntervalZ { empty: false, lo, hi },
                }
            };
            proof {
                lemma_narrow_above_meet(*self, *t, r);
            }
            r
        }
    }

    /// One step of the §4.5 fuel. Fuel 0 keeps `self`. A strict meet spends
    /// one unit; a meet that does not change the value spends none.
    pub open spec fn refine_value(self, fact: IntervalZ, budget: nat) -> IntervalZ {
        if budget == 0 { self } else { self.meet_spec(fact) }
    }

    pub open spec fn refine_fuel(self, fact: IntervalZ, budget: nat) -> nat {
        if budget == 0 {
            0
        } else if self.meet_spec(fact).eq_abs(self) {
            budget
        } else {
            (budget - 1) as nat
        }
    }

    pub fn refine(&self, fact: &IntervalZ, budget: u8) -> (r: (IntervalZ, u8))
        requires
            self.wf(),
            fact.wf(),
        ensures
            r.0.wf(),
            r.0.eq_abs(self.refine_value(*fact, budget as nat)),
            r.1 as nat == self.refine_fuel(*fact, budget as nat),
            r.0.refines(*self),
            budget == 0 ==> r.0.eq_abs(*self) && r.1 == 0,
    {
        if budget == 0 {
            (self.clone_iv(), 0)
        } else {
            let m = self.meet(fact);
            if self.eq_abs_exec(&m) {
                (m, budget)
            } else {
                (m, budget - 1)
            }
        }
    }

    pub fn within(&self, lo: i64, hi: i64) -> (r: bool)
        requires
            self.wf(),
            lo <= hi,
        ensures
            r ==> forall|z: int| #![auto] self.has(z) ==> lo as int <= z && z <= hi as int,
    {
        if self.empty {
            false
        } else {
            Bound::fin(lo).le(&self.lo) && self.hi.le(&Bound::fin(hi))
        }
    }

    pub fn nonzero(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r ==> forall|z: int| #![auto] self.has(z) ==> z != 0,
    {
        if self.empty { false } else { !self.contains(0) }
    }

    /// Every concrete value is `>= 0`, including `[0, +∞)`.
    pub fn nonneg(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r ==> forall|z: int| #![auto] self.has(z) ==> z >= 0,
    {
        if self.empty { false } else { Bound::fin(0).le(&self.lo) }
    }

    pub fn fits_u8(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r ==> forall|z: int| #![auto] self.has(z) ==> 0 <= z && z <= 255,
    {
        self.within(0, 255)
    }

    pub fn check_ubig(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r == self.wf_ubig(),
    {
        self.empty || Bound::fin(0).le(&self.lo)
    }

    pub open spec fn div_one_spec(self, d: IntervalZ) -> IntervalZ {
        if self.empty || d.empty {
            IntervalZ::bottom_spec()
        } else {
            match (
                ext_div_spec(self.lo, d.lo),
                ext_div_spec(self.lo, d.hi),
                ext_div_spec(self.hi, d.lo),
                ext_div_spec(self.hi, d.hi),
            ) {
                (Some(a), Some(b), Some(c), Some(e)) => IntervalZ::corner_hull(a, b, c, e),
                _ => IntervalZ::top_spec(),
            }
        }
    }

    pub open spec fn div_spec(self, d: IntervalZ) -> (IntervalZ, Alarm) {
        if self.empty || d.empty {
            (IntervalZ::bottom_spec(), Alarm::NoError)
        } else if is_zero_singleton(d) {
            (IntervalZ::bottom_spec(), Alarm::DefiniteError)
        } else if d.has(0) {
            let dneg = d.meet_spec(neg_unit_ray());
            let dpos = d.meet_spec(pos_unit_ray());
            (
                self.div_one_spec(dneg).join_spec(self.div_one_spec(dpos)),
                Alarm::MaybeError,
            )
        } else {
            (self.div_one_spec(d), Alarm::NoError)
        }
    }

    pub fn div_one(&self, d: &IntervalZ) -> (r: IntervalZ)
        requires
            self.wf(),
            d.wf(),
        ensures
            r.wf(),
            r == self.div_one_spec(*d),
            !d.has(0) ==> forall|x: int, y: int|
                #![auto]
                self.has(x) && d.has(y) && y != 0 ==> r.has(x / y),
    {
        if self.empty || d.empty {
            IntervalZ::bottom()
        } else {
            let q1 = self.lo.ext_div(&d.lo);
            let q2 = self.lo.ext_div(&d.hi);
            let q3 = self.hi.ext_div(&d.lo);
            let q4 = self.hi.ext_div(&d.hi);
            let r = match (q1, q2, q3, q4) {
                (Some(a), Some(b), Some(c), Some(e)) => {
                    let lo = a.min(&b).min(&c.min(&e));
                    let hi = a.max(&b).max(&c.max(&e));
                    IntervalZ::arith(lo, hi)
                },
                _ => IntervalZ::top(),
            };
            proof {
                if !d.has(0) {
                    lemma_div_one_contains(*self, *d, r);
                }
            }
            r
        }
    }

    pub fn div(&self, d: &IntervalZ) -> (r: (IntervalZ, Alarm))
        requires
            self.wf(),
            d.wf(),
        ensures
            r.0.wf(),
            r.0.eq_abs(self.div_spec(*d).0),
            r.1 == self.div_spec(*d).1,
            forall|x: int, y: int| #![auto] self.has(x) && d.has(y) && y != 0 ==> r.0.has(x / y),
            forall|x: int, y: int| #![auto] self.has(x) && d.has(y) ==> r.1.has(y == 0),
    {
        if self.empty || d.empty {
            (IntervalZ::bottom(), Alarm::NoError)
        } else if d.is_zero() {
            (IntervalZ::bottom(), Alarm::DefiniteError)
        } else if d.contains(0) {
            let negi = IntervalZ::range(Bound::NegInf, Bound::fin(-1));
            let posi = IntervalZ::range(Bound::fin(1), Bound::PosInf);
            let dneg = d.meet(&negi);
            let dpos = d.meet(&posi);
            let r = self.div_one(&dneg).join(&self.div_one(&dpos));
            proof {
                lemma_div_split_contains(*self, *d, dneg, dpos, r);
            }
            (r, Alarm::MaybeError)
        } else {
            let r = self.div_one(d);
            proof {
                lemma_not_contains_zero(*d);
            }
            (r, Alarm::NoError)
        }
    }
}

pub open spec fn neg_unit_ray() -> IntervalZ {
    IntervalZ { empty: false, lo: Bound::NegInf, hi: Bound::Fin(IBig::from_int(-1)) }
}

pub open spec fn pos_unit_ray() -> IntervalZ {
    IntervalZ { empty: false, lo: Bound::Fin(IBig::from_int(1)), hi: Bound::PosInf }
}

pub open spec fn is_fin_bound(b: Bound) -> bool {
    match b {
        Bound::Fin(_) => true,
        _ => false,
    }
}

pub open spec fn is_zero_singleton(a: IntervalZ) -> bool {
    !a.empty && a.lo == Bound::Fin(IBig::from_int(0)) && a.hi == Bound::Fin(IBig::from_int(0))
}

pub fn bound_le_int_exec(b: &Bound, x: i64) -> (r: bool)
    ensures
        r == bound_le_int(*b, x as int),
{
    match b {
        Bound::NegInf => true,
        Bound::Fin(n) => n.le(&IBig::from_i64(x)),
        Bound::PosInf => false,
    }
}

pub fn int_le_bound_exec(x: i64, b: &Bound) -> (r: bool)
    ensures
        r == int_le_bound(x as int, *b),
{
    match b {
        Bound::PosInf => true,
        Bound::Fin(n) => IBig::from_i64(x).le(n),
        Bound::NegInf => false,
    }
}

/// A chain of meets. Fuel 0 keeps `cur`. A strict meet spends one unit; a
/// meet that does not change the value spends none. The chain therefore
/// either stabilises or stops when the fuel is gone.
pub open spec fn meet_chain(cur: IntervalZ, facts: Seq<IntervalZ>, fuel: nat) -> IntervalZ
    decreases facts.len(),
{
    if facts.len() == 0 || fuel == 0 {
        cur
    } else {
        let next = cur.meet_spec(facts[0]);
        if next.eq_abs(cur) {
            meet_chain(cur, facts.skip(1), fuel)
        } else {
            meet_chain(next, facts.skip(1), (fuel - 1) as nat)
        }
    }
}

pub open spec fn interval_r_bottom() -> IntervalR {
    IntervalR {
        empty: true,
        lo: Bound::Fin(IBig::from_int(0)),
        hi: Bound::Fin(IBig::from_int(0)),
        lo_closed: true,
        hi_closed: true,
    }
}

pub open spec fn interval_r_new_spec(lo: Bound, lo_closed: bool, hi: Bound, hi_closed: bool) -> IntervalR {
    let lo_closed = if lo == Bound::NegInf { false } else { lo_closed };
    let hi_closed = if hi == Bound::PosInf { false } else { hi_closed };
    if bound_le(lo, hi) && lo != Bound::PosInf && hi != Bound::NegInf && (!bound_eq(lo, hi) || (
        lo_closed && hi_closed)) {
        IntervalR { empty: false, lo: lo, hi: hi, lo_closed: lo_closed, hi_closed: hi_closed }
    } else {
        interval_r_bottom()
    }
}

proof fn lemma_interval_r_new_bot(
    lo: Bound,
    lo_closed: bool,
    hi: Bound,
    hi_closed: bool,
    lo_c: bool,
    hi_c: bool,
)
    requires
        lo_c == (if lo == Bound::NegInf { false } else { lo_closed }),
        hi_c == (if hi == Bound::PosInf { false } else { hi_closed }),
        !bound_le(lo, hi) || lo == Bound::PosInf || hi == Bound::NegInf || (bound_eq(lo, hi) && !(
        lo_c && hi_c)),
    ensures
        interval_r_new_spec(lo, lo_closed, hi, hi_closed) == interval_r_bottom(),
{
    let sl = if lo == Bound::NegInf { false } else { lo_closed };
    let sh = if hi == Bound::PosInf { false } else { hi_closed };
    assert(sl == lo_c && sh == hi_c);
    assert(!(bound_le(lo, hi) && lo != Bound::PosInf && hi != Bound::NegInf && (!bound_eq(lo, hi)
        || (sl && sh))));
}

proof fn lemma_interval_r_new_ok(
    lo: Bound,
    lo_closed: bool,
    hi: Bound,
    hi_closed: bool,
    lo_c: bool,
    hi_c: bool,
)
    requires
        lo_c == (if lo == Bound::NegInf { false } else { lo_closed }),
        hi_c == (if hi == Bound::PosInf { false } else { hi_closed }),
        bound_le(lo, hi),
        lo != Bound::PosInf,
        hi != Bound::NegInf,
        !bound_eq(lo, hi) || (lo_c && hi_c),
    ensures
        ({
            let built = IntervalR {
                empty: false,
                lo: lo,
                hi: hi,
                lo_closed: lo_c,
                hi_closed: hi_c,
            };
            built.wf() && built == interval_r_new_spec(lo, lo_closed, hi, hi_closed)
        }),
{
    let sl = if lo == Bound::NegInf { false } else { lo_closed };
    let sh = if hi == Bound::PosInf { false } else { hi_closed };
    assert(sl == lo_c && sh == hi_c);
    let built = IntervalR { empty: false, lo: lo, hi: hi, lo_closed: lo_c, hi_closed: hi_c };
    assert(built == interval_r_new_spec(lo, lo_closed, hi, hi_closed));
    if bound_eq(lo, hi) {
        assert(lo_c && hi_c);
        assert(lo != Bound::NegInf);
        assert(hi != Bound::PosInf);
        assert(is_fin_bound(lo));
    } else {
        assert(lo != Bound::NegInf || !lo_c);
        assert(hi != Bound::PosInf || !hi_c);
    }
    assert(built.wf());
}

// ---------------------------------------------------------------------------
// IntervalR: RBig bounds with open and closed endpoints
// ---------------------------------------------------------------------------

/// Interval over the rationals. Endpoints carry an open/closed flag.
/// Infinities are never closed. Integer membership excludes an open endpoint.
pub struct IntervalR {
    pub empty: bool,
    pub lo: Bound,
    pub hi: Bound,
    pub lo_closed: bool,
    pub hi_closed: bool,
}

impl IntervalR {
    pub open spec fn wf(self) -> bool {
        if self.empty {
            true
        } else if self.lo == Bound::PosInf || self.hi == Bound::NegInf || !bound_le(self.lo, self.hi) {
            false
        } else if bound_eq(self.lo, self.hi) {
            self.lo_closed && self.hi_closed && is_fin_bound(self.lo)
        } else {
            (self.lo != Bound::NegInf || !self.lo_closed) && (self.hi != Bound::PosInf
                || !self.hi_closed)
        }
    }

    pub open spec fn has_int(self, z: int) -> bool {
        !self.empty && r_above(self.lo, self.lo_closed, z) && r_below(self.hi, self.hi_closed, z)
    }

    pub fn bottom() -> (r: IntervalR)
        ensures
            r.wf(),
            r == interval_r_bottom(),
            forall|z: int| #![auto] !r.has_int(z),
    {
        IntervalR { empty: true, lo: Bound::fin(0), hi: Bound::fin(0), lo_closed: true, hi_closed: true }
    }

    pub fn new(lo: Bound, lo_closed: bool, hi: Bound, hi_closed: bool) -> (r: IntervalR)
        ensures
            r.wf(),
            r == interval_r_new_spec(lo, lo_closed, hi, hi_closed),
    {
        let lo_c = if matches!(lo, Bound::NegInf) { false } else { lo_closed };
        let hi_c = if matches!(hi, Bound::PosInf) { false } else { hi_closed };
        let le = lo.le(&hi);
        let eq = lo.eq_bound(&hi);
        proof {
            assert(lo_c == (if lo == Bound::NegInf { false } else { lo_closed }));
            assert(hi_c == (if hi == Bound::PosInf { false } else { hi_closed }));
            assert(le == bound_le(lo, hi));
            assert(eq == bound_eq(lo, hi));
        }
        if !le {
            let r = IntervalR::bottom();
            proof {
                assert(!bound_le(lo, hi));
                lemma_interval_r_new_bot(lo, lo_closed, hi, hi_closed, lo_c, hi_c);
                assert(r == interval_r_new_spec(lo, lo_closed, hi, hi_closed));
            }
            r
        } else if matches!(lo, Bound::PosInf) {
            let r = IntervalR::bottom();
            proof {
                assert(lo == Bound::PosInf);
                lemma_interval_r_new_bot(lo, lo_closed, hi, hi_closed, lo_c, hi_c);
                assert(r == interval_r_new_spec(lo, lo_closed, hi, hi_closed));
            }
            r
        } else if matches!(hi, Bound::NegInf) {
            let r = IntervalR::bottom();
            proof {
                assert(hi == Bound::NegInf);
                lemma_interval_r_new_bot(lo, lo_closed, hi, hi_closed, lo_c, hi_c);
                assert(r == interval_r_new_spec(lo, lo_closed, hi, hi_closed));
            }
            r
        } else if eq && !lo_c {
            let r = IntervalR::bottom();
            proof {
                assert(bound_eq(lo, hi));
                assert(!lo_c);
                assert(!(lo_c && hi_c));
                lemma_interval_r_new_bot(lo, lo_closed, hi, hi_closed, lo_c, hi_c);
                assert(r == interval_r_new_spec(lo, lo_closed, hi, hi_closed));
            }
            r
        } else if eq && !hi_c {
            let r = IntervalR::bottom();
            proof {
                assert(bound_eq(lo, hi));
                assert(!hi_c);
                assert(!(lo_c && hi_c));
                lemma_interval_r_new_bot(lo, lo_closed, hi, hi_closed, lo_c, hi_c);
                assert(r == interval_r_new_spec(lo, lo_closed, hi, hi_closed));
            }
            r
        } else {
            let r = IntervalR {
                empty: false,
                lo: lo.clone_bound(),
                hi: hi.clone_bound(),
                lo_closed: lo_c,
                hi_closed: hi_c,
            };
            proof {
                assert(bound_le(lo, hi));
                assert(lo != Bound::PosInf);
                assert(hi != Bound::NegInf);
                assert(!eq || lo_c);
                assert(!eq || hi_c);
                assert(!bound_eq(lo, hi) || (lo_c && hi_c));
                lemma_interval_r_new_ok(lo, lo_closed, hi, hi_closed, lo_c, hi_c);
                assert(r.lo == lo && r.hi == hi && r.lo_closed == lo_c && r.hi_closed == hi_c
                    && !r.empty);
                assert(r == interval_r_new_spec(lo, lo_closed, hi, hi_closed));
            }
            r
        }
    }

    pub fn contains_int(&self, z: i64) -> (r: bool)
        ensures
            r == self.has_int(z as int),
    {
        if self.empty {
            false
        } else {
            above_exec(&self.lo, self.lo_closed, z) && below_exec(&self.hi, self.hi_closed, z)
        }
    }

    /// Meet keeps the tighter endpoint; a shared endpoint stays closed only
    /// when both sides include it.
    pub fn meet(&self, other: &IntervalR) -> (r: IntervalR)
        requires
            self.wf(),
            other.wf(),
        ensures
            r.wf(),
            forall|z: int| #![auto] self.has_int(z) && other.has_int(z) ==> r.has_int(z),
    {
        if self.empty || other.empty {
            IntervalR::bottom()
        } else {
            let (lo, lo_closed) = tighter_lo(self, other);
            let (hi, hi_closed) = tighter_hi(self, other);
            let r = IntervalR::new(lo, lo_closed, hi, hi_closed);
            proof {
                assert forall|z: int| #![auto] self.has_int(z) && other.has_int(z) implies r.has_int(z)
                    by {
                    lemma_interval_r_new_has(lo, lo_closed, hi, hi_closed, z);
                };
            }
            r
        }
    }
}

pub open spec fn r_above(b: Bound, closed: bool, z: int) -> bool {
    match b {
        Bound::NegInf => true,
        Bound::PosInf => false,
        Bound::Fin(n) => if closed { n.view() <= z } else { n.view() < z },
    }
}

pub open spec fn r_below(b: Bound, closed: bool, z: int) -> bool {
    match b {
        Bound::PosInf => true,
        Bound::NegInf => false,
        Bound::Fin(n) => if closed { z <= n.view() } else { z < n.view() },
    }
}

fn above_exec(b: &Bound, closed: bool, z: i64) -> (r: bool)
    ensures
        r == r_above(*b, closed, z as int),
{
    match b {
        Bound::NegInf => true,
        Bound::PosInf => false,
        Bound::Fin(n) => if closed { n.le(&IBig::from_i64(z)) } else { n.lt(&IBig::from_i64(z)) },
    }
}

fn below_exec(b: &Bound, closed: bool, z: i64) -> (r: bool)
    ensures
        r == r_below(*b, closed, z as int),
{
    match b {
        Bound::PosInf => true,
        Bound::NegInf => false,
        Bound::Fin(n) => if closed { IBig::from_i64(z).le(n) } else { IBig::from_i64(z).lt(n) },
    }
}

fn tighter_lo(a: &IntervalR, b: &IntervalR) -> (r: (Bound, bool))
    requires
        a.wf(),
        b.wf(),
        !a.empty,
        !b.empty,
    ensures
        forall|z: int|
            r_above(a.lo, a.lo_closed, z) && r_above(b.lo, b.lo_closed, z) ==> #[trigger] r_above(
                r.0,
                r.1,
                z,
            ),
{
    if a.lo.lt(&b.lo) {
        (b.lo.clone_bound(), b.lo_closed)
    } else if b.lo.lt(&a.lo) {
        (a.lo.clone_bound(), a.lo_closed)
    } else {
        let r = (a.lo.clone_bound(), a.lo_closed && b.lo_closed);
        proof {
            bound_le_total(a.lo, b.lo);
            assert(bound_le(a.lo, b.lo) && bound_le(b.lo, a.lo));
            bound_le_antisym(a.lo, b.lo);
            assert(a.lo == b.lo);
            assert forall|z: int|
                r_above(a.lo, a.lo_closed, z) && r_above(b.lo, b.lo_closed, z) implies r_above(
                r.0,
                r.1,
                z,
            ) by {
                if a.lo_closed && b.lo_closed {
                } else if !a.lo_closed {
                } else {
                    assert(!b.lo_closed);
                }
            };
        }
        r
    }
}

fn tighter_hi(a: &IntervalR, b: &IntervalR) -> (r: (Bound, bool))
    requires
        a.wf(),
        b.wf(),
        !a.empty,
        !b.empty,
    ensures
        forall|z: int|
            r_below(a.hi, a.hi_closed, z) && r_below(b.hi, b.hi_closed, z) ==> #[trigger] r_below(
                r.0,
                r.1,
                z,
            ),
{
    if a.hi.lt(&b.hi) {
        (a.hi.clone_bound(), a.hi_closed)
    } else if b.hi.lt(&a.hi) {
        (b.hi.clone_bound(), b.hi_closed)
    } else {
        let r = (a.hi.clone_bound(), a.hi_closed && b.hi_closed);
        proof {
            bound_le_total(a.hi, b.hi);
            assert(bound_le(a.hi, b.hi) && bound_le(b.hi, a.hi));
            bound_le_antisym(a.hi, b.hi);
            assert(a.hi == b.hi);
            assert forall|z: int|
                r_below(a.hi, a.hi_closed, z) && r_below(b.hi, b.hi_closed, z) implies r_below(
                r.0,
                r.1,
                z,
            ) by {
                if a.hi_closed && b.hi_closed {
                } else if !a.hi_closed {
                } else {
                    assert(!b.hi_closed);
                }
            };
        }
        r
    }
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

pub proof fn lemma_add_bound_lower(a: Bound, b: Bound, x: int, y: int)
    requires
        bound_le_int(a, x),
        bound_le_int(b, y),
        a != Bound::PosInf,
        b != Bound::PosInf,
    ensures
        bound_le_int(add_bound_spec(a, b), x + y),
{
}

pub proof fn lemma_add_bound_upper(a: Bound, b: Bound, x: int, y: int)
    requires
        int_le_bound(x, a),
        int_le_bound(y, b),
        a != Bound::NegInf,
        b != Bound::NegInf,
    ensures
        int_le_bound(x + y, add_bound_spec(a, b)),
{
}

pub proof fn lemma_add_contains(a: IntervalZ, b: IntervalZ, r: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        !a.empty,
        !b.empty,
        r == a.add_spec(b),
    ensures
        forall|x: int, y: int| #![auto] a.has(x) && b.has(y) ==> r.has(x + y),
{
    assert forall|x: int, y: int| #![auto] a.has(x) && b.has(y) implies r.has(x + y) by {
        lemma_add_bound_lower(a.lo, b.lo, x, y);
        lemma_add_bound_upper(a.hi, b.hi, x, y);
    };
}

pub proof fn lemma_neg_low(b: Bound, x: int)
    requires
        int_le_bound(x, b),
    ensures
        bound_le_int(neg_bound_spec(b), -x),
{
}

pub proof fn lemma_neg_high(b: Bound, x: int)
    requires
        bound_le_int(b, x),
    ensures
        int_le_bound(-x, neg_bound_spec(b)),
{
}

pub proof fn lemma_neg_contains(a: IntervalZ, r: IntervalZ)
    requires
        a.wf(),
        !a.empty,
        r == a.neg_spec(),
    ensures
        forall|x: int| #![auto] a.has(x) ==> r.has(-x),
{
    assert forall|x: int| #![auto] a.has(x) implies r.has(-x) by {
        lemma_neg_low(a.hi, x);
        lemma_neg_high(a.lo, x);
    };
}

pub open spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn spec_max(a: int, b: int) -> int {
    if a <= b { b } else { a }
}

pub open spec fn spec_min4(a: int, b: int, c: int, d: int) -> int {
    spec_min(spec_min(a, b), spec_min(c, d))
}

pub open spec fn spec_max4(a: int, b: int, c: int, d: int) -> int {
    spec_max(spec_max(a, b), spec_max(c, d))
}

pub proof fn lemma_lin_mul(alo: int, ahi: int, x: int, y: int)
    requires
        alo <= x <= ahi,
    ensures
        spec_min(alo * y, ahi * y) <= x * y <= spec_max(alo * y, ahi * y),
{
    if y >= 0 {
        vstd::arithmetic::mul::lemma_mul_inequality(alo, x, y);
        vstd::arithmetic::mul::lemma_mul_inequality(x, ahi, y);
    } else {
        vstd::arithmetic::mul::lemma_mul_unary_negation(alo, y);
        vstd::arithmetic::mul::lemma_mul_unary_negation(x, y);
        vstd::arithmetic::mul::lemma_mul_unary_negation(ahi, y);
        vstd::arithmetic::mul::lemma_mul_inequality(alo, x, -y);
        vstd::arithmetic::mul::lemma_mul_inequality(x, ahi, -y);
        assert(alo * (-y) <= x * (-y) <= ahi * (-y));
        assert(alo * (-y) == -(alo * y));
        assert(x * (-y) == -(x * y));
        assert(ahi * (-y) == -(ahi * y));
        assert(-(alo * y) <= -(x * y) <= -(ahi * y));
        assert(ahi * y <= x * y <= alo * y);
    }
}

pub proof fn lemma_mul_corners(alo: int, ahi: int, blo: int, bhi: int, x: int, y: int)
    requires
        alo <= x <= ahi,
        blo <= y <= bhi,
    ensures
        spec_min4(alo * blo, alo * bhi, ahi * blo, ahi * bhi) <= x * y,
        x * y <= spec_max4(alo * blo, alo * bhi, ahi * blo, ahi * bhi),
{
    lemma_lin_mul(alo, ahi, x, y);
    lemma_lin_mul(blo, bhi, y, alo);
    lemma_lin_mul(blo, bhi, y, ahi);
    vstd::arithmetic::mul::lemma_mul_is_commutative(alo, blo);
    vstd::arithmetic::mul::lemma_mul_is_commutative(alo, bhi);
    vstd::arithmetic::mul::lemma_mul_is_commutative(ahi, blo);
    vstd::arithmetic::mul::lemma_mul_is_commutative(ahi, bhi);
    vstd::arithmetic::mul::lemma_mul_is_commutative(alo, y);
    vstd::arithmetic::mul::lemma_mul_is_commutative(ahi, y);
    let lo = spec_min(alo * y, ahi * y);
    let hi = spec_max(alo * y, ahi * y);
    assert(spec_min(alo * blo, alo * bhi) <= alo * y <= spec_max(alo * blo, alo * bhi));
    assert(spec_min(ahi * blo, ahi * bhi) <= ahi * y <= spec_max(ahi * blo, ahi * bhi));
    assert(spec_min4(alo * blo, alo * bhi, ahi * blo, ahi * bhi) <= lo);
    assert(hi <= spec_max4(alo * blo, alo * bhi, ahi * blo, ahi * bhi));
    assert(lo <= x * y <= hi);
}

pub proof fn lemma_bound_le_trans(a: Bound, b: Bound, c: Bound)
    requires
        bound_le(a, b),
        bound_le(b, c),
    ensures
        bound_le(a, c),
{
    match (a, b, c) {
        (Bound::Fin(x), Bound::Fin(y), Bound::Fin(z)) => {},
        _ => {},
    }
}

pub proof fn lemma_bound_le_int_weaken(p: Bound, q: Bound, z: int)
    requires
        bound_le(p, q),
        bound_le_int(q, z),
    ensures
        bound_le_int(p, z),
{
    match (p, q) {
        (Bound::Fin(a), Bound::Fin(b)) => {},
        (Bound::NegInf, _) => {},
        (Bound::Fin(_), Bound::PosInf) => {
            assert(!bound_le_int(q, z));
        },
        (Bound::PosInf, _) => {
            assert(!bound_le(p, q));
        },
        (Bound::Fin(_), Bound::NegInf) => {
            assert(!bound_le(p, q));
        },
    }
}

pub proof fn lemma_int_le_bound_weaken(z: int, q: Bound, p: Bound)
    requires
        bound_le(q, p),
        int_le_bound(z, q),
    ensures
        int_le_bound(z, p),
{
    match (q, p) {
        (Bound::Fin(a), Bound::Fin(b)) => {},
        (_, Bound::PosInf) => {},
        (Bound::NegInf, _) => {
            assert(!int_le_bound(z, q));
        },
        (Bound::Fin(_), Bound::NegInf) => {
            assert(!bound_le(q, p));
        },
        (Bound::PosInf, Bound::Fin(_)) => {
            assert(!bound_le(q, p));
        },
        (Bound::PosInf, Bound::NegInf) => {
            assert(!bound_le(q, p));
        },
    }
}

pub proof fn lemma_bound_min_le(a: Bound, b: Bound)
    ensures
        bound_le(bound_min(a, b), a),
        bound_le(bound_min(a, b), b),
{
    if bound_le(a, b) {
        bound_le_refl(a);
    } else {
        bound_le_total(a, b);
        bound_le_refl(b);
    }
}

pub proof fn lemma_bound_max_ge(a: Bound, b: Bound)
    ensures
        bound_le(a, bound_max(a, b)),
        bound_le(b, bound_max(a, b)),
{
    if bound_le(a, b) {
        bound_le_refl(b);
    } else {
        bound_le_total(a, b);
        bound_le_refl(a);
    }
}

pub proof fn lemma_min4_le(p1: Bound, p2: Bound, p3: Bound, p4: Bound, c: Bound)
    requires
        c == p1 || c == p2 || c == p3 || c == p4,
    ensures
        bound_le(bound_min(bound_min(p1, p2), bound_min(p3, p4)), c),
{
    let m12 = bound_min(p1, p2);
    let m34 = bound_min(p3, p4);
    let m = bound_min(m12, m34);
    lemma_bound_min_le(p1, p2);
    lemma_bound_min_le(p3, p4);
    lemma_bound_min_le(m12, m34);
    if c == p1 {
        lemma_bound_le_trans(m, m12, p1);
    } else if c == p2 {
        lemma_bound_le_trans(m, m12, p2);
    } else if c == p3 {
        lemma_bound_le_trans(m, m34, p3);
    } else {
        lemma_bound_le_trans(m, m34, p4);
    }
}

pub proof fn lemma_max4_ge(p1: Bound, p2: Bound, p3: Bound, p4: Bound, c: Bound)
    requires
        c == p1 || c == p2 || c == p3 || c == p4,
    ensures
        bound_le(c, bound_max(bound_max(p1, p2), bound_max(p3, p4))),
{
    let m12 = bound_max(p1, p2);
    let m34 = bound_max(p3, p4);
    let m = bound_max(m12, m34);
    lemma_bound_max_ge(p1, p2);
    lemma_bound_max_ge(p3, p4);
    lemma_bound_max_ge(m12, m34);
    if c == p1 {
        lemma_bound_le_trans(p1, m12, m);
    } else if c == p2 {
        lemma_bound_le_trans(p2, m12, m);
    } else if c == p3 {
        lemma_bound_le_trans(p3, m34, m);
    } else {
        lemma_bound_le_trans(p4, m34, m);
    }
}

pub proof fn lemma_bounds_ordered(lo: Bound, hi: Bound, z: int)
    requires
        bound_le_int(lo, z),
        int_le_bound(z, hi),
    ensures
        bound_le(lo, hi),
        lo != Bound::PosInf,
        hi != Bound::NegInf,
{
    match (lo, hi) {
        (Bound::Fin(a), Bound::Fin(b)) => {
            assert(a.view() <= z && z <= b.view());
        },
        (Bound::NegInf, Bound::Fin(_)) => {},
        (Bound::NegInf, Bound::PosInf) => {},
        (Bound::Fin(_), Bound::PosInf) => {},
        (Bound::NegInf, Bound::NegInf) => {
            assert(!int_le_bound(z, hi));
        },
        (Bound::PosInf, _) => {
            assert(!bound_le_int(lo, z));
        },
        (Bound::Fin(_), Bound::NegInf) => {
            assert(!int_le_bound(z, hi));
        },
    }
}

pub proof fn lemma_arith_has(lo: Bound, hi: Bound, z: int)
    requires
        bound_le_int(lo, z),
        int_le_bound(z, hi),
    ensures
        IntervalZ::arith_spec(lo, hi).has(z),
{
    lemma_bounds_ordered(lo, hi, z);
}

pub proof fn lemma_hull_has(
    p1: Bound,
    p2: Bound,
    p3: Bound,
    p4: Bound,
    lower: Bound,
    upper: Bound,
    z: int,
)
    requires
        lower == p1 || lower == p2 || lower == p3 || lower == p4,
        upper == p1 || upper == p2 || upper == p3 || upper == p4,
        bound_le_int(lower, z),
        int_le_bound(z, upper),
    ensures
        IntervalZ::corner_hull(p1, p2, p3, p4).has(z),
{
    let lo = bound_min(bound_min(p1, p2), bound_min(p3, p4));
    let hi = bound_max(bound_max(p1, p2), bound_max(p3, p4));
    lemma_min4_le(p1, p2, p3, p4, lower);
    lemma_max4_ge(p1, p2, p3, p4, upper);
    lemma_bound_le_int_weaken(lo, lower, z);
    lemma_int_le_bound_weaken(z, upper, hi);
    lemma_arith_has(lo, hi, z);
}

pub proof fn lemma_ext_mul_comm(a: Bound, b: Bound)
    ensures
        ext_mul_spec(a, b) == ext_mul_spec(b, a),
{
    match (a, b) {
        (Bound::Fin(x), Bound::Fin(y)) => {
            vstd::arithmetic::mul::lemma_mul_is_commutative(x.view(), y.view());
        },
        _ => {},
    }
}

pub proof fn lemma_nn_upper(ah: Bound, bh: Bound, x: int, y: int)
    requires
        int_le_bound(x, ah),
        int_le_bound(y, bh),
        x >= 0,
        y >= 0,
        ah != Bound::NegInf,
        bh != Bound::NegInf,
    ensures
        int_le_bound(x * y, ext_mul_spec(ah, bh)),
{
    match (ah, bh) {
        (Bound::Fin(a), Bound::Fin(b)) => {
            assert(a.view() >= 0 && b.view() >= 0);
            vstd::arithmetic::mul::lemma_mul_inequality(x, a.view(), y);
            vstd::arithmetic::mul::lemma_mul_inequality(y, b.view(), a.view());
            vstd::arithmetic::mul::lemma_mul_is_commutative(a.view(), y);
            vstd::arithmetic::mul::lemma_mul_is_commutative(a.view(), b.view());
            assert(x * y <= a.view() * b.view());
            assert(IBig::from_int(a.view() * b.view()).view() == a.view() * b.view());
        },
        (Bound::Fin(a), Bound::PosInf) => {
            if a.view() > 0 {
            } else if a.view() == 0 {
                assert(x == 0);
                vstd::arithmetic::mul::lemma_mul_basics(x);
                vstd::arithmetic::mul::lemma_mul_basics(y);
                assert(x * y == 0);
            } else {
                assert(x <= a.view());
                assert(false);
            }
        },
        (Bound::PosInf, Bound::Fin(b)) => {
            if b.view() > 0 {
            } else if b.view() == 0 {
                assert(y == 0);
                vstd::arithmetic::mul::lemma_mul_basics(x);
                vstd::arithmetic::mul::lemma_mul_basics(y);
                assert(x * y == 0);
            } else {
                assert(y <= b.view());
                assert(false);
            }
        },
        (Bound::PosInf, Bound::PosInf) => {},
        _ => {
            assert(false);
        },
    }
}

pub proof fn lemma_nn_lower_pos(al: Bound, bl: Bound, x: int, y: int)
    requires
        bound_le_int(al, x),
        bound_le_int(bl, y),
        bound_le(Bound::Fin(IBig::from_int(0)), al),
        bound_le(Bound::Fin(IBig::from_int(0)), bl),
        x >= 0,
        y >= 0,
    ensures
        bound_le_int(ext_mul_spec(al, bl), x * y),
{
    match (al, bl) {
        (Bound::Fin(a), Bound::Fin(b)) => {
            assert(a.view() >= 0 && b.view() >= 0);
            vstd::arithmetic::mul::lemma_mul_inequality(a.view(), x, y);
            vstd::arithmetic::mul::lemma_mul_inequality(b.view(), y, a.view());
            vstd::arithmetic::mul::lemma_mul_is_commutative(a.view(), y);
            vstd::arithmetic::mul::lemma_mul_is_commutative(a.view(), b.view());
            assert(a.view() * b.view() <= x * y);
            assert(IBig::from_int(a.view() * b.view()).view() == a.view() * b.view());
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn lemma_nn_lower_neg(al: Bound, bh: Bound, x: int, y: int)
    requires
        !bound_le(Bound::Fin(IBig::from_int(0)), al),
        int_le_bound(y, bh),
        x >= 0,
        y >= 0,
        al != Bound::PosInf,
        bh != Bound::NegInf,
    ensures
        bound_le_int(ext_mul_spec(al, bh), x * y),
{
    vstd::arithmetic::mul::lemma_mul_nonnegative(x, y);
    match (al, bh) {
        (Bound::NegInf, Bound::PosInf) => {},
        (Bound::NegInf, Bound::Fin(h)) => {
            if h.view() > 0 {
            } else if h.view() == 0 {
                assert(y == 0);
                vstd::arithmetic::mul::lemma_mul_basics(x);
                vstd::arithmetic::mul::lemma_mul_basics(y);
                assert(x * y == 0);
            } else {
                assert(y <= h.view());
                assert(false);
            }
        },
        (Bound::Fin(a), Bound::PosInf) => {
            assert(a.view() < 0);
        },
        (Bound::Fin(a), Bound::Fin(h)) => {
            assert(a.view() < 0);
            assert(h.view() >= y && y >= 0);
            vstd::arithmetic::mul::lemma_mul_unary_negation(a.view(), h.view());
            vstd::arithmetic::mul::lemma_mul_nonnegative(-a.view(), h.view());
            assert((-a.view()) * h.view() == -(a.view() * h.view()));
            assert(a.view() * h.view() <= 0);
            assert(a.view() * h.view() <= x * y);
            assert(IBig::from_int(a.view() * h.view()).view() == a.view() * h.view());
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn lemma_pos_neg_lower(ah: Bound, bl: Bound, x: int, y: int)
    requires
        int_le_bound(x, ah),
        bound_le_int(bl, y),
        x >= 0,
        y < 0,
        ah != Bound::NegInf,
        bl != Bound::PosInf,
    ensures
        bound_le_int(ext_mul_spec(ah, bl), x * y),
{
    match (ah, bl) {
        (Bound::Fin(a), Bound::Fin(b)) => {
            assert(a.view() >= x && x >= 0);
            assert(b.view() <= y && y < 0);
            vstd::arithmetic::mul::lemma_mul_unary_negation(x, y);
            vstd::arithmetic::mul::lemma_mul_unary_negation(a.view(), y);
            vstd::arithmetic::mul::lemma_mul_unary_negation(a.view(), b.view());
            vstd::arithmetic::mul::lemma_mul_inequality(x, a.view(), -y);
            vstd::arithmetic::mul::lemma_mul_inequality(b.view(), y, a.view());
            vstd::arithmetic::mul::lemma_mul_is_commutative(a.view(), y);
            vstd::arithmetic::mul::lemma_mul_is_commutative(a.view(), b.view());
            assert(x * (-y) <= a.view() * (-y));
            assert(a.view() * b.view() <= a.view() * y);
            assert(a.view() * y <= x * y);
            assert(a.view() * b.view() <= x * y);
            assert(IBig::from_int(a.view() * b.view()).view() == a.view() * b.view());
        },
        (Bound::PosInf, Bound::Fin(b)) => {
            assert(b.view() <= y && y < 0);
        },
        (Bound::PosInf, Bound::NegInf) => {},
        (Bound::Fin(a), Bound::NegInf) => {
            if a.view() > 0 {
            } else if a.view() == 0 {
                assert(x == 0);
                vstd::arithmetic::mul::lemma_mul_basics(x);
                vstd::arithmetic::mul::lemma_mul_basics(y);
                assert(x * y == 0);
            } else {
                assert(x <= a.view());
                assert(false);
            }
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn lemma_pos_neg_upper_hi_neg(al: Bound, bh: Bound, x: int, y: int)
    requires
        bound_le_int(al, x),
        int_le_bound(y, bh),
        x >= 0,
        y < 0,
        !bound_le(Bound::Fin(IBig::from_int(0)), bh),
        al != Bound::PosInf,
        bh != Bound::NegInf,
    ensures
        int_le_bound(x * y, ext_mul_spec(al, bh)),
{
    vstd::arithmetic::mul::lemma_mul_unary_negation(x, y);
    vstd::arithmetic::mul::lemma_mul_nonnegative(x, -y);
    assert(x * y <= 0);
    match (al, bh) {
        (Bound::Fin(a), Bound::Fin(h)) => {
            assert(h.view() < 0);
            if a.view() >= 0 {
                vstd::arithmetic::mul::lemma_mul_unary_negation(a.view(), y);
                vstd::arithmetic::mul::lemma_mul_inequality(a.view(), x, -y);
                vstd::arithmetic::mul::lemma_mul_inequality(y, h.view(), a.view());
                vstd::arithmetic::mul::lemma_mul_is_commutative(a.view(), y);
                vstd::arithmetic::mul::lemma_mul_is_commutative(a.view(), h.view());
                assert(x * y <= a.view() * y);
                assert(a.view() * y <= a.view() * h.view());
            } else {
                vstd::arithmetic::mul::lemma_mul_cancels_negatives(a.view(), h.view());
                vstd::arithmetic::mul::lemma_mul_nonnegative(-a.view(), -h.view());
                assert(a.view() * h.view() >= 0);
            }
            assert(x * y <= a.view() * h.view());
            assert(IBig::from_int(a.view() * h.view()).view() == a.view() * h.view());
        },
        (Bound::NegInf, Bound::Fin(h)) => {
            assert(h.view() < 0);
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn lemma_pos_neg_upper_hi_nonneg(ah: Bound, bh: Bound, x: int, y: int)
    requires
        int_le_bound(x, ah),
        int_le_bound(y, bh),
        x >= 0,
        y < 0,
        bound_le(Bound::Fin(IBig::from_int(0)), bh),
        ah != Bound::NegInf,
        bh != Bound::NegInf,
    ensures
        int_le_bound(x * y, ext_mul_spec(ah, bh)),
{
    vstd::arithmetic::mul::lemma_mul_unary_negation(x, y);
    vstd::arithmetic::mul::lemma_mul_nonnegative(x, -y);
    assert(x * y <= 0);
    match (ah, bh) {
        (Bound::Fin(a), Bound::Fin(h)) => {
            assert(a.view() >= 0 && h.view() >= 0);
            vstd::arithmetic::mul::lemma_mul_nonnegative(a.view(), h.view());
            assert(x * y <= a.view() * h.view());
            assert(IBig::from_int(a.view() * h.view()).view() == a.view() * h.view());
        },
        (Bound::Fin(a), Bound::PosInf) => {
            if a.view() == 0 {
                assert(x == 0);
                vstd::arithmetic::mul::lemma_mul_basics(x);
                vstd::arithmetic::mul::lemma_mul_basics(y);
                assert(x * y == 0);
            }
        },
        (Bound::PosInf, Bound::Fin(h)) => {
            if h.view() == 0 {
                assert(x * y <= 0);
            }
        },
        (Bound::PosInf, Bound::PosInf) => {},
        _ => {
            assert(false);
        },
    }
}

pub proof fn lemma_neg_neg_lower_hi(ah: Bound, bh: Bound, x: int, y: int)
    requires
        int_le_bound(x, ah),
        int_le_bound(y, bh),
        x < 0,
        y < 0,
        !bound_le(Bound::Fin(IBig::from_int(0)), ah),
        !bound_le(Bound::Fin(IBig::from_int(0)), bh),
    ensures
        bound_le_int(ext_mul_spec(ah, bh), x * y),
{
    match (ah, bh) {
        (Bound::Fin(a), Bound::Fin(b)) => {
            assert(a.view() < 0 && b.view() < 0);
            assert(x <= a.view() && y <= b.view());
            vstd::arithmetic::mul::lemma_mul_cancels_negatives(x, y);
            vstd::arithmetic::mul::lemma_mul_cancels_negatives(a.view(), b.view());
            vstd::arithmetic::mul::lemma_mul_inequality(-a.view(), -x, -y);
            vstd::arithmetic::mul::lemma_mul_inequality(-b.view(), -y, -a.view());
            vstd::arithmetic::mul::lemma_mul_is_commutative(-a.view(), -y);
            vstd::arithmetic::mul::lemma_mul_is_commutative(-a.view(), -b.view());
            assert((-a.view()) * (-b.view()) <= (-x) * (-y));
            assert(a.view() * b.view() <= x * y);
            assert(IBig::from_int(a.view() * b.view()).view() == a.view() * b.view());
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn lemma_neg_neg_lower_cross(u: Bound, v: Bound, x: int, y: int)
    requires
        bound_le(Bound::Fin(IBig::from_int(0)), u),
        bound_le_int(v, y),
        x < 0,
        y < 0,
        u != Bound::NegInf,
        v != Bound::PosInf,
    ensures
        bound_le_int(ext_mul_spec(u, v), x * y),
{
    vstd::arithmetic::mul::lemma_mul_cancels_negatives(x, y);
    vstd::arithmetic::mul::lemma_mul_nonnegative(-x, -y);
    assert(0 <= x * y);
    match (u, v) {
        (Bound::PosInf, Bound::NegInf) => {},
        (Bound::PosInf, Bound::Fin(b)) => {
            assert(b.view() <= y && y < 0);
        },
        (Bound::Fin(a), Bound::NegInf) => {
            assert(a.view() >= 0);
            if a.view() == 0 {
                assert(0 <= x * y);
            }
        },
        (Bound::Fin(a), Bound::Fin(b)) => {
            assert(a.view() >= 0);
            assert(b.view() <= y && y < 0);
            if a.view() == 0 || b.view() == 0 {
                vstd::arithmetic::mul::lemma_mul_basics(a.view());
                vstd::arithmetic::mul::lemma_mul_basics(b.view());
                assert(a.view() * b.view() == 0);
            } else {
                vstd::arithmetic::mul::lemma_mul_unary_negation(a.view(), b.view());
                vstd::arithmetic::mul::lemma_mul_nonnegative(a.view(), -b.view());
                assert(a.view() * b.view() <= 0);
            }
            assert(a.view() * b.view() <= x * y);
            assert(IBig::from_int(a.view() * b.view()).view() == a.view() * b.view());
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn lemma_neg_neg_upper(al: Bound, bl: Bound, x: int, y: int)
    requires
        bound_le_int(al, x),
        bound_le_int(bl, y),
        x < 0,
        y < 0,
        al != Bound::PosInf,
        bl != Bound::PosInf,
    ensures
        int_le_bound(x * y, ext_mul_spec(al, bl)),
{
    match (al, bl) {
        (Bound::Fin(a), Bound::Fin(b)) => {
            assert(a.view() <= x && x < 0);
            assert(b.view() <= y && y < 0);
            vstd::arithmetic::mul::lemma_mul_cancels_negatives(x, y);
            vstd::arithmetic::mul::lemma_mul_cancels_negatives(a.view(), b.view());
            vstd::arithmetic::mul::lemma_mul_inequality(-x, -a.view(), -y);
            vstd::arithmetic::mul::lemma_mul_inequality(-y, -b.view(), -a.view());
            vstd::arithmetic::mul::lemma_mul_is_commutative(-a.view(), -y);
            vstd::arithmetic::mul::lemma_mul_is_commutative(-a.view(), -b.view());
            assert((-x) * (-y) <= (-a.view()) * (-b.view()));
            assert(x * y <= a.view() * b.view());
            assert(IBig::from_int(a.view() * b.view()).view() == a.view() * b.view());
        },
        (Bound::NegInf, _) => {},
        (_, Bound::NegInf) => {},
        _ => {
            assert(false);
        },
    }
}

pub proof fn lemma_mul_by_signs(a: IntervalZ, b: IntervalZ, x: int, y: int)
    requires
        a.wf(),
        b.wf(),
        a.has(x),
        b.has(y),
    ensures
        a.mul_spec(b).has(x * y),
{
    let p1 = ext_mul_spec(a.lo, b.lo);
    let p2 = ext_mul_spec(a.lo, b.hi);
    let p3 = ext_mul_spec(a.hi, b.lo);
    let p4 = ext_mul_spec(a.hi, b.hi);
    let zero = Bound::Fin(IBig::from_int(0));
    if x >= 0 && y >= 0 {
        lemma_nn_upper(a.hi, b.hi, x, y);
        if bound_le(zero, a.lo) && bound_le(zero, b.lo) {
            lemma_nn_lower_pos(a.lo, b.lo, x, y);
            lemma_hull_has(p1, p2, p3, p4, p1, p4, x * y);
        } else if !bound_le(zero, a.lo) {
            lemma_nn_lower_neg(a.lo, b.hi, x, y);
            lemma_hull_has(p1, p2, p3, p4, p2, p4, x * y);
        } else {
            lemma_nn_lower_neg(b.lo, a.hi, y, x);
            lemma_ext_mul_comm(a.hi, b.lo);
            vstd::arithmetic::mul::lemma_mul_is_commutative(x, y);
            lemma_hull_has(p1, p2, p3, p4, p3, p4, x * y);
        }
    } else if x >= 0 && y < 0 {
        lemma_pos_neg_lower(a.hi, b.lo, x, y);
        if !bound_le(zero, b.hi) {
            lemma_pos_neg_upper_hi_neg(a.lo, b.hi, x, y);
            lemma_hull_has(p1, p2, p3, p4, p3, p2, x * y);
        } else {
            lemma_pos_neg_upper_hi_nonneg(a.hi, b.hi, x, y);
            lemma_hull_has(p1, p2, p3, p4, p3, p4, x * y);
        }
    } else if x < 0 && y >= 0 {
        lemma_pos_neg_lower(b.hi, a.lo, y, x);
        lemma_ext_mul_comm(a.lo, b.hi);
        vstd::arithmetic::mul::lemma_mul_is_commutative(x, y);
        if !bound_le(zero, a.hi) {
            lemma_pos_neg_upper_hi_neg(b.lo, a.hi, y, x);
            lemma_ext_mul_comm(a.hi, b.lo);
            lemma_hull_has(p1, p2, p3, p4, p2, p3, x * y);
        } else {
            lemma_pos_neg_upper_hi_nonneg(b.hi, a.hi, y, x);
            lemma_ext_mul_comm(a.hi, b.hi);
            lemma_hull_has(p1, p2, p3, p4, p2, p4, x * y);
        }
    } else {
        lemma_neg_neg_upper(a.lo, b.lo, x, y);
        if !bound_le(zero, a.hi) && !bound_le(zero, b.hi) {
            lemma_neg_neg_lower_hi(a.hi, b.hi, x, y);
            lemma_hull_has(p1, p2, p3, p4, p4, p1, x * y);
        } else if bound_le(zero, a.hi) {
            assert(bound_le_int(b.lo, y));
            lemma_neg_neg_lower_cross(a.hi, b.lo, x, y);
            lemma_hull_has(p1, p2, p3, p4, p3, p1, x * y);
        } else {
            assert(bound_le(zero, b.hi));
            assert(bound_le_int(a.lo, x));
            lemma_neg_neg_lower_cross(b.hi, a.lo, y, x);
            lemma_ext_mul_comm(a.lo, b.hi);
            vstd::arithmetic::mul::lemma_mul_is_commutative(x, y);
            lemma_hull_has(p1, p2, p3, p4, p2, p1, x * y);
        }
    }
}

pub proof fn lemma_euclid_neg_div(x: int, d: int)
    requires
        d > 0,
    ensures
        x / (-d) == -(x / d),
{
    assert(x / (-d) == -(x / d)) by (nonlinear_arith)
        requires
            d > 0,
    ;
}

pub proof fn lemma_div_denom_mono_neg(x: int, a: int, b: int)
    requires
        x < 0,
        1 <= a <= b,
    ensures
        x / a <= x / b,
{
    assert(x / a <= x / b) by (nonlinear_arith)
        requires
            x < 0,
            1 <= a,
            a <= b,
    ;
}

pub proof fn lemma_mul_contains(a: IntervalZ, b: IntervalZ, r: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        !a.empty,
        !b.empty,
        r == a.mul_spec(b),
    ensures
        forall|x: int, y: int| #![auto] a.has(x) && b.has(y) ==> r.has(x * y),
{
    assert forall|x: int, y: int| #![auto] a.has(x) && b.has(y) implies r.has(x * y) by {
        lemma_mul_concrete_in_hull(a, b, x, y);
    };
}

pub proof fn lemma_mul_concrete_in_hull(a: IntervalZ, b: IntervalZ, x: int, y: int)
    requires
        a.wf(),
        b.wf(),
        a.has(x),
        b.has(y),
    ensures
        a.mul_spec(b).has(x * y),
{
    if a.is_finite() && b.is_finite() {
        lemma_mul_finite_in_hull(a, b, x, y);
    } else {
        lemma_mul_unbounded_in_hull(a, b, x, y);
    }
}

pub open spec fn fin_view(b: Bound) -> int
    recommends
        is_fin_bound(b),
{
    match b {
        Bound::Fin(n) => n.view(),
        _ => 0,
    }
}

pub proof fn lemma_mul_finite_in_hull(a: IntervalZ, b: IntervalZ, x: int, y: int)
    requires
        a.wf(),
        b.wf(),
        a.is_finite(),
        b.is_finite(),
        a.has(x),
        b.has(y),
    ensures
        a.mul_spec(b).has(x * y),
{
    lemma_mul_by_signs(a, b, x, y);
}

pub proof fn lemma_mul_unbounded_in_hull(a: IntervalZ, b: IntervalZ, x: int, y: int)
    requires
        a.wf(),
        b.wf(),
        a.has(x),
        b.has(y),
        !(a.is_finite() && b.is_finite()),
    ensures
        a.mul_spec(b).has(x * y),
{
    lemma_mul_by_signs(a, b, x, y);
}

pub proof fn lemma_div_one_contains(a: IntervalZ, d: IntervalZ, r: IntervalZ)
    requires
        a.wf(),
        d.wf(),
        !d.has(0),
        r == a.div_one_spec(d),
    ensures
        forall|x: int, y: int| #![auto] a.has(x) && d.has(y) && y != 0 ==> r.has(x / y),
{
    assert forall|x: int, y: int| #![auto] a.has(x) && d.has(y) && y != 0 implies r.has(x / y)
        by {
        if !a.empty && !d.empty {
            lemma_div_concrete_in_hull(a, d, x, y);
        }
    };
}

pub proof fn lemma_ext_div_some(n: Bound, d: Bound)
    requires
        match d {
            Bound::Fin(z) => z.view() != 0,
            _ => true,
        },
    ensures
        matches!(ext_div_spec(n, d), Some(_)),
{
}

pub proof fn lemma_pos_denom(d: IntervalZ, y: int)
    requires
        d.wf(),
        d.has(y),
        !d.has(0),
        y > 0,
    ensures
        d.lo != Bound::NegInf,
        d.lo != Bound::PosInf,
        fin_view(d.lo) >= 1,
        fin_view(d.lo) <= y,
        d.hi == Bound::PosInf || fin_view(d.hi) >= y,
{
    match d.lo {
        Bound::NegInf => {
            if int_le_bound(0, d.hi) {
                assert(d.has(0));
            } else {
                assert(!d.has(y));
            }
            assert(false);
        },
        Bound::PosInf => {
            assert(false);
        },
        Bound::Fin(n) => {
            if n.view() <= 0 {
                assert(bound_le_int(d.lo, 0));
                assert(int_le_bound(0, d.hi));
                assert(d.has(0));
                assert(false);
            }
            assert(n.view() >= 1);
        },
    }
}

pub proof fn lemma_quot_hi_nonneg(ah: int, n: int, x: int, y: int)
    requires
        x <= ah,
        ah >= 0,
        1 <= n <= y,
    ensures
        x / y <= ah / n,
{
    if x >= 0 {
        vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(x, n, y);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(x, ah, n);
    } else {
        vstd::arithmetic::div_mod::lemma_div_of0(y);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(x, 0, y);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(ah, n);
        assert(x / y <= 0);
        assert(0 <= ah / n);
    }
}

pub proof fn lemma_quot_hi_neg(ah: int, m: int, x: int, y: int)
    requires
        x <= ah < 0,
        1 <= y <= m,
    ensures
        x / y <= ah / m,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x, ah, y);
    lemma_div_denom_mono_neg(ah, y, m);
}

pub proof fn lemma_quot_lo_neg(al: int, n: int, x: int, y: int)
    requires
        al <= x,
        al < 0,
        1 <= n <= y,
    ensures
        al / n <= x / y,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered(al, x, y);
    lemma_div_denom_mono_neg(al, n, y);
}

pub proof fn lemma_quot_lo_nonneg(al: int, m: int, x: int, y: int)
    requires
        0 <= al <= x,
        1 <= y <= m,
    ensures
        al / m <= x / y,
{
    vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(x, y, m);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(al, x, m);
}

pub proof fn lemma_quot_nonneg_over_pos(x: int, y: int)
    requires
        x >= 0,
        y > 0,
    ensures
        0 <= x / y,
{
    vstd::arithmetic::div_mod::lemma_div_of0(y);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(0, x, y);
}

pub proof fn lemma_quot_neg_over_pos(x: int, y: int)
    requires
        x < 0,
        y > 0,
    ensures
        x / y <= 0,
{
    vstd::arithmetic::div_mod::lemma_div_of0(y);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(x, 0, y);
}

pub proof fn lemma_div_pos(a: IntervalZ, d: IntervalZ, x: int, y: int)
    requires
        a.wf(),
        d.wf(),
        a.has(x),
        d.has(y),
        y > 0,
        !d.has(0),
    ensures
        a.div_one_spec(d).has(x / y),
{
    lemma_pos_denom(d, y);
    lemma_ext_div_some(a.lo, d.lo);
    lemma_ext_div_some(a.lo, d.hi);
    lemma_ext_div_some(a.hi, d.lo);
    lemma_ext_div_some(a.hi, d.hi);
    let b1 = match ext_div_spec(a.lo, d.lo) {
        Some(b) => b,
        None => {
            assert(false);
            Bound::NegInf
        },
    };
    let b2 = match ext_div_spec(a.lo, d.hi) {
        Some(b) => b,
        None => {
            assert(false);
            Bound::NegInf
        },
    };
    let b3 = match ext_div_spec(a.hi, d.lo) {
        Some(b) => b,
        None => {
            assert(false);
            Bound::NegInf
        },
    };
    let b4 = match ext_div_spec(a.hi, d.hi) {
        Some(b) => b,
        None => {
            assert(false);
            Bound::NegInf
        },
    };
    let n = fin_view(d.lo);
    assert(1 <= n <= y);
    let lower = match a.lo {
        Bound::NegInf => b1,
        Bound::Fin(al) => if al.view() < 0 {
            lemma_quot_lo_neg(al.view(), n, x, y);
            assert(IBig::from_int(al.view() / n).view() == al.view() / n);
            b1
        } else {
            match d.hi {
                Bound::PosInf => {
                    lemma_quot_nonneg_over_pos(x, y);
                    b2
                },
                Bound::Fin(h) => {
                    lemma_quot_lo_nonneg(al.view(), h.view(), x, y);
                    assert(IBig::from_int(al.view() / h.view()).view() == al.view() / h.view());
                    b2
                },
                Bound::NegInf => {
                    assert(false);
                    b2
                },
            }
        },
        Bound::PosInf => {
            assert(false);
            b1
        },
    };
    let upper = match a.hi {
        Bound::PosInf => b3,
        Bound::Fin(ah) => if ah.view() >= 0 {
            lemma_quot_hi_nonneg(ah.view(), n, x, y);
            assert(IBig::from_int(ah.view() / n).view() == ah.view() / n);
            b3
        } else {
            match d.hi {
                Bound::PosInf => {
                    lemma_quot_neg_over_pos(x, y);
                    b4
                },
                Bound::Fin(h) => {
                    lemma_quot_hi_neg(ah.view(), h.view(), x, y);
                    assert(IBig::from_int(ah.view() / h.view()).view() == ah.view() / h.view());
                    b4
                },
                Bound::NegInf => {
                    assert(false);
                    b4
                },
            }
        },
        Bound::NegInf => {
            assert(false);
            b3
        },
    };
    assert(bound_le_int(lower, x / y));
    assert(int_le_bound(x / y, upper));
    lemma_hull_has(b1, b2, b3, b4, lower, upper, x / y);
    assert(a.div_one_spec(d) == IntervalZ::corner_hull(b1, b2, b3, b4));
}

pub proof fn lemma_neg_anti(p: Bound, q: Bound)
    requires
        bound_le(p, q),
    ensures
        bound_le(neg_bound_spec(q), neg_bound_spec(p)),
{
    match (p, q) {
        (Bound::Fin(x), Bound::Fin(y)) => {
            assert(-y.view() <= -x.view());
            assert(IBig::from_int(-x.view()).view() == -x.view());
            assert(IBig::from_int(-y.view()).view() == -y.view());
        },
        _ => {},
    }
}

pub proof fn lemma_neg_shaped(a: IntervalZ)
    requires
        a.wf(),
        !a.empty,
    ensures
        !a.neg_spec().empty,
        a.neg_spec().lo == neg_bound_spec(a.hi),
        a.neg_spec().hi == neg_bound_spec(a.lo),
{
    lemma_neg_anti(a.lo, a.hi);
}

pub proof fn lemma_ext_div_neg(n: Bound, e: Bound)
    ensures
        match (ext_div_spec(n, e), ext_div_spec(n, neg_bound_spec(e))) {
            (Some(b), Some(c)) => c == neg_bound_spec(b),
            (None, None) => true,
            _ => false,
        },
{
    match (n, e) {
        (Bound::Fin(a), Bound::Fin(z)) => {
            if z.view() > 0 {
                lemma_euclid_neg_div(a.view(), z.view());
                assert(a.view() / (-z.view()) == -(a.view() / z.view()));
            } else if z.view() < 0 {
                lemma_euclid_neg_div(a.view(), -z.view());
                assert(a.view() / z.view() == -(a.view() / (-z.view())));
                assert(a.view() / (-z.view()) == -(a.view() / z.view()));
            }
        },
        _ => {},
    }
}

pub proof fn lemma_div_neg(a: IntervalZ, d: IntervalZ, x: int, y: int)
    requires
        a.wf(),
        d.wf(),
        a.has(x),
        d.has(y),
        y < 0,
        !d.has(0),
    ensures
        a.div_one_spec(d).has(x / y),
{
    let nd = d.neg_spec();
    lemma_neg_shaped(d);
    lemma_neg_contains(d, nd);
    assert(nd.has(-y));
    assert(-y > 0);
    lemma_euclid_neg_div(x, -y);
    assert(x / y == -(x / (-y)));
    lemma_div_pos(a, nd, x, -y);
    lemma_div_neg_transfer(a, d, x / (-y));
}

pub proof fn lemma_div_neg_transfer(a: IntervalZ, d: IntervalZ, q: int)
    requires
        a.wf(),
        d.wf(),
        !a.empty,
        !d.empty,
        a.div_one_spec(d.neg_spec()).has(q),
    ensures
        a.div_one_spec(d).has(-q),
{
    let nd = d.neg_spec();
    lemma_neg_shaped(d);
    lemma_ext_div_neg(a.lo, d.lo);
    lemma_ext_div_neg(a.lo, d.hi);
    lemma_ext_div_neg(a.hi, d.lo);
    lemma_ext_div_neg(a.hi, d.hi);
    lemma_neg_contains(a.div_one_spec(nd), a.div_one_spec(nd).neg_spec());
    assert(a.div_one_spec(nd).neg_spec().has(-q));
    assert(a.div_one_spec(d).eq_abs(a.div_one_spec(nd).neg_spec()) || a.div_one_spec(d).has(-q));
}

pub proof fn lemma_div_concrete_in_hull(a: IntervalZ, d: IntervalZ, x: int, y: int)
    requires
        a.wf(),
        d.wf(),
        a.has(x),
        d.has(y),
        y != 0,
        !d.has(0),
    ensures
        a.div_one_spec(d).has(x / y),
{
    if a.is_finite() && d.is_finite() {
        lemma_div_finite_in_hull(a, d, x, y);
    } else if y > 0 {
        lemma_div_pos(a, d, x, y);
    } else {
        lemma_div_neg(a, d, x, y);
    }
}

pub proof fn lemma_div_finite_in_hull(a: IntervalZ, d: IntervalZ, x: int, y: int)
    requires
        a.wf(),
        d.wf(),
        a.is_finite(),
        d.is_finite(),
        a.has(x),
        d.has(y),
        y != 0,
        !d.has(0),
    ensures
        a.div_one_spec(d).has(x / y),
{
    lemma_div_corners(fin_view(a.lo), fin_view(a.hi), fin_view(d.lo), fin_view(d.hi), x, y);
}

pub proof fn lemma_div_corners(alo: int, ahi: int, dlo: int, dhi: int, x: int, y: int)
    requires
        alo <= x <= ahi,
        dlo <= y <= dhi,
        y != 0,
        dlo > 0 || dhi < 0,
    ensures
        spec_min4(alo / dlo, alo / dhi, ahi / dlo, ahi / dhi) <= x / y,
        x / y <= spec_max4(alo / dlo, alo / dhi, ahi / dlo, ahi / dhi),
{
    lemma_lin_div(alo, ahi, x, y);
    lemma_div_in_denom(alo, dlo, dhi, y);
    lemma_div_in_denom(ahi, dlo, dhi, y);
    let lo = spec_min(alo / y, ahi / y);
    let hi = spec_max(alo / y, ahi / y);
    assert(spec_min(alo / dlo, alo / dhi) <= alo / y <= spec_max(alo / dlo, alo / dhi));
    assert(spec_min(ahi / dlo, ahi / dhi) <= ahi / y <= spec_max(ahi / dlo, ahi / dhi));
    assert(spec_min4(alo / dlo, alo / dhi, ahi / dlo, ahi / dhi) <= lo);
    assert(hi <= spec_max4(alo / dlo, alo / dhi, ahi / dlo, ahi / dhi));
    assert(lo <= x / y <= hi);
}

pub proof fn lemma_lin_div(alo: int, ahi: int, x: int, y: int)
    requires
        y != 0,
        alo <= x <= ahi,
    ensures
        spec_min(alo / y, ahi / y) <= x / y <= spec_max(alo / y, ahi / y),
{
    if y > 0 {
        vstd::arithmetic::div_mod::lemma_div_is_ordered(alo, x, y);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(x, ahi, y);
    } else {
        lemma_euclid_neg_div(alo, -y);
        lemma_euclid_neg_div(x, -y);
        lemma_euclid_neg_div(ahi, -y);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(alo, x, -y);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(x, ahi, -y);
        assert(alo / y == -(alo / (-y)));
        assert(x / y == -(x / (-y)));
        assert(ahi / y == -(ahi / (-y)));
        assert(ahi / y <= x / y <= alo / y);
    }
}

pub proof fn lemma_div_in_denom(x: int, dlo: int, dhi: int, y: int)
    requires
        dlo <= y <= dhi,
        y != 0,
        dlo > 0 || dhi < 0,
    ensures
        spec_min(x / dlo, x / dhi) <= x / y <= spec_max(x / dlo, x / dhi),
{
    if dlo > 0 {
        if x >= 0 {
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(x, dlo, y);
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(x, y, dhi);
        } else {
            lemma_div_denom_mono_neg(x, dlo, y);
            lemma_div_denom_mono_neg(x, y, dhi);
        }
    } else {
        lemma_euclid_neg_div(x, -dlo);
        lemma_euclid_neg_div(x, -y);
        lemma_euclid_neg_div(x, -dhi);
        let pd_lo = -dhi;
        let pd_hi = -dlo;
        let py = -y;
        assert(1 <= pd_lo && pd_lo <= py && py <= pd_hi);
        if x >= 0 {
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(x, pd_lo, py);
            vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator(x, py, pd_hi);
        } else {
            lemma_div_denom_mono_neg(x, pd_lo, py);
            lemma_div_denom_mono_neg(x, py, pd_hi);
        }
        assert(x / dlo == -(x / pd_hi));
        assert(x / dhi == -(x / pd_lo));
        assert(x / y == -(x / py));
    }
}

pub proof fn lemma_not_contains_zero(d: IntervalZ)
    requires
        d.wf(),
        !d.empty,
        !d.has(0),
    ensures
        forall|y: int| #![auto] d.has(y) ==> y != 0,
{
}

pub proof fn lemma_div_split_contains(
    a: IntervalZ,
    d: IntervalZ,
    dneg: IntervalZ,
    dpos: IntervalZ,
    r: IntervalZ,
)
    requires
        a.wf(),
        d.wf(),
        d.has(0),
        !is_zero_singleton(d),
        dneg.wf(),
        dpos.wf(),
        dneg.eq_abs(d.meet_spec(neg_unit_ray())),
        dpos.eq_abs(d.meet_spec(pos_unit_ray())),
        r.eq_abs(a.div_one_spec(dneg).join_spec(a.div_one_spec(dpos))),
    ensures
        forall|x: int, y: int| #![auto] a.has(x) && d.has(y) && y != 0 ==> r.has(x / y),
{
    assert forall|x: int, y: int| #![auto] a.has(x) && d.has(y) && y != 0 implies r.has(x / y)
        by {
        if y <= -1 {
            assert(IBig::from_int(-1).view() == -1);
            assert(neg_unit_ray().has(y));
            assert(!neg_unit_ray().has(0));
            meet_has_iff(d, neg_unit_ray(), y);
            meet_has_iff(d, neg_unit_ray(), 0);
            lemma_eq_abs_has(dneg, d.meet_spec(neg_unit_ray()), y);
            lemma_eq_abs_has(dneg, d.meet_spec(neg_unit_ray()), 0);
            lemma_div_one_contains(a, dneg, a.div_one_spec(dneg));
            assert(a.div_one_spec(dneg).has(x / y));
            lemma_div_one_wf(a, dneg);
            lemma_div_one_wf(a, dpos);
            lemma_join_has_side(a.div_one_spec(dneg), a.div_one_spec(dpos), x / y);
            lemma_eq_abs_has(r, a.div_one_spec(dneg).join_spec(a.div_one_spec(dpos)), x / y);
        } else {
            assert(y >= 1);
            assert(IBig::from_int(1).view() == 1);
            assert(pos_unit_ray().has(y));
            assert(!pos_unit_ray().has(0));
            meet_has_iff(d, pos_unit_ray(), y);
            meet_has_iff(d, pos_unit_ray(), 0);
            lemma_eq_abs_has(dpos, d.meet_spec(pos_unit_ray()), y);
            lemma_eq_abs_has(dpos, d.meet_spec(pos_unit_ray()), 0);
            lemma_div_one_contains(a, dpos, a.div_one_spec(dpos));
            assert(a.div_one_spec(dpos).has(x / y));
            lemma_div_one_wf(a, dneg);
            lemma_div_one_wf(a, dpos);
            lemma_join_has_side(a.div_one_spec(dpos), a.div_one_spec(dneg), x / y);
            lemma_eq_abs_has(r, a.div_one_spec(dneg).join_spec(a.div_one_spec(dpos)), x / y);
        }
    };
}

pub proof fn lemma_widen_sound(a: IntervalZ, b: IntervalZ, r: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        !a.empty,
        !b.empty,
        r.eq_abs(a.widen_spec(b)),
    ensures
        a.refines(r),
        b.refines(r),
        a.join_spec(b).refines(r),
{
}

pub proof fn lemma_narrow_above_meet(a: IntervalZ, t: IntervalZ, r: IntervalZ)
    requires
        a.wf(),
        t.wf(),
        !a.empty,
        !t.empty,
        r.eq_abs(a.narrow_spec(t)),
        r.wf(),
    ensures
        a.meet_spec(t).refines(r),
        r.refines(a),
{
}

pub proof fn lemma_interval_r_new_has(
    lo: Bound,
    lo_closed: bool,
    hi: Bound,
    hi_closed: bool,
    z: int,
)
    requires
        r_above(lo, lo_closed, z),
        r_below(hi, hi_closed, z),
    ensures
        interval_r_new_spec(lo, lo_closed, hi, hi_closed).has_int(z),
{
    assert(lo != Bound::PosInf);
    assert(hi != Bound::NegInf);
    match (lo, hi) {
        (Bound::Fin(a), Bound::Fin(b)) => {
            if lo_closed {
                assert(a.view() <= z);
            } else {
                assert(a.view() < z);
            }
            if hi_closed {
                assert(z <= b.view());
            } else {
                assert(z < b.view());
            }
            assert(a.view() <= b.view());
        },
        _ => {},
    }
    let lo_c = if lo == Bound::NegInf {
        false
    } else {
        lo_closed
    };
    let hi_c = if hi == Bound::PosInf {
        false
    } else {
        hi_closed
    };
    if bound_eq(lo, hi) {
        match (lo, hi) {
            (Bound::Fin(a), Bound::Fin(b)) => {
                assert(a.view() == b.view());
                if !lo_closed {
                    assert(a.view() < z);
                    assert(false);
                }
                if !hi_closed {
                    assert(z < b.view());
                    assert(false);
                }
            },
            _ => {
                assert(false);
            },
        }
    }
    assert(r_above(lo, lo_c, z));
    assert(r_below(hi, hi_c, z));
}

pub proof fn lemma_bound_eq_ord(a: Bound, b: Bound, z: int)
    requires
        bound_eq(a, b),
    ensures
        bound_le_int(a, z) == bound_le_int(b, z),
        int_le_bound(z, a) == int_le_bound(z, b),
{
    match (a, b) {
        (Bound::Fin(x), Bound::Fin(y)) => {
            assert(x.view() == y.view());
        },
        _ => {},
    }
}

pub proof fn lemma_eq_abs_has(a: IntervalZ, b: IntervalZ, z: int)
    requires
        a.eq_abs(b),
    ensures
        a.has(z) == b.has(z),
{
    if !a.empty && !b.empty {
        lemma_bound_eq_ord(a.lo, b.lo, z);
        lemma_bound_eq_ord(a.hi, b.hi, z);
    }
}

pub proof fn lemma_div_one_wf(a: IntervalZ, d: IntervalZ)
    requires
        a.wf(),
        d.wf(),
    ensures
        a.div_one_spec(d).wf(),
{
}

pub proof fn lemma_join_has_side(a: IntervalZ, b: IntervalZ, z: int)
    requires
        a.wf(),
        b.wf(),
        a.has(z),
    ensures
        a.join_spec(b).has(z),
{
    if !b.empty {
        lemma_bound_min_le(a.lo, b.lo);
        lemma_bound_le_int_weaken(bound_min(a.lo, b.lo), a.lo, z);
        lemma_bound_max_ge(a.hi, b.hi);
        lemma_int_le_bound_weaken(z, a.hi, bound_max(a.hi, b.hi));
    }
}

pub proof fn meet_has_iff(a: IntervalZ, b: IntervalZ, z: int)
    requires
        a.wf(),
        b.wf(),
    ensures
        a.meet_spec(b).has(z) <==> a.has(z) && b.has(z),
{
}

// ---------------------------------------------------------------------------
// §3.5
// ---------------------------------------------------------------------------

pub proof fn meet_comm(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
    ensures
        a.meet_spec(b).eq_abs(b.meet_spec(a)),
{
    if !a.empty && !b.empty {
        bound_max_comm(a.lo, b.lo);
        bound_min_comm(a.hi, b.hi);
    }
}

pub proof fn meet_idempotent(a: IntervalZ)
    requires
        a.wf(),
    ensures
        a.meet_spec(a).eq_abs(a),
{
}

pub proof fn meet_assoc(a: IntervalZ, b: IntervalZ, c: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
    ensures
        a.meet_spec(b).meet_spec(c).eq_abs(a.meet_spec(b.meet_spec(c))),
{
}

pub proof fn meet_top(a: IntervalZ)
    requires
        a.wf(),
    ensures
        a.meet_spec(IntervalZ::top_spec()).eq_abs(a),
{
}

pub proof fn meet_bottom(a: IntervalZ)
    requires
        a.wf(),
    ensures
        a.meet_spec(IntervalZ::bottom_spec()).eq_abs(IntervalZ::bottom_spec()),
{
}

pub proof fn join_comm(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
    ensures
        a.join_spec(b).eq_abs(b.join_spec(a)),
{
}

pub proof fn join_idempotent(a: IntervalZ)
    requires
        a.wf(),
    ensures
        a.join_spec(a).eq_abs(a),
{
}

pub proof fn join_assoc(a: IntervalZ, b: IntervalZ, c: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
    ensures
        a.join_spec(b).join_spec(c).eq_abs(a.join_spec(b.join_spec(c))),
{
}

pub proof fn join_bottom(a: IntervalZ)
    requires
        a.wf(),
    ensures
        a.join_spec(IntervalZ::bottom_spec()).eq_abs(a),
{
}

pub proof fn join_top(a: IntervalZ)
    requires
        a.wf(),
    ensures
        a.join_spec(IntervalZ::top_spec()).eq_abs(IntervalZ::top_spec()),
{
}

pub proof fn meet_monotone(a: IntervalZ, b: IntervalZ, c: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        a.refines(b),
    ensures
        a.meet_spec(c).refines(b.meet_spec(c)),
{
    assert forall|z: int| #![auto] a.meet_spec(c).has(z) implies b.meet_spec(c).has(z) by {
        meet_has_iff(a, c, z);
        meet_has_iff(b, c, z);
    };
}

pub proof fn lemma_witness(a: IntervalZ) -> (z: int)
    requires
        a.wf(),
        !a.empty,
    ensures
        a.has(z),
{
    match (a.lo, a.hi) {
        (Bound::Fin(n), _) => {
            assert(a.has(n.view()));
            n.view()
        },
        (Bound::NegInf, Bound::Fin(h)) => {
            assert(a.has(h.view()));
            h.view()
        },
        (Bound::NegInf, Bound::PosInf) => {
            assert(a.has(0));
            0
        },
        _ => {
            assert(false);
            0
        },
    }
}

pub proof fn lemma_refines_nonempty(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        !a.empty,
        a.refines(b),
    ensures
        !b.empty,
{
    let z = lemma_witness(a);
    assert(b.has(z));
}

pub proof fn lemma_below(a: IntervalZ, b: IntervalZ) -> (z: int)
    requires
        a.wf(),
        b.wf(),
        !a.empty,
        !b.empty,
        bound_lt(a.lo, b.lo),
    ensures
        a.has(z),
        !b.has(z),
{
    match (a.lo, b.lo) {
        (Bound::Fin(n), Bound::Fin(m)) => {
            assert(n.view() < m.view());
            assert(a.has(n.view()));
            n.view()
        },
        (Bound::Fin(n), Bound::PosInf) => {
            assert(a.has(n.view()));
            n.view()
        },
        (Bound::NegInf, Bound::Fin(m)) => {
            let z = m.view() - 1;
            if bound_le(b.lo, a.hi) {
                assert(a.has(z));
                z
            } else {
                match a.hi {
                    Bound::Fin(h) => {
                        assert(a.has(h.view()));
                        h.view()
                    },
                    _ => {
                        assert(false);
                        z
                    },
                }
            }
        },
        _ => {
            assert(false);
            0
        },
    }
}

pub proof fn lemma_above(a: IntervalZ, b: IntervalZ) -> (z: int)
    requires
        a.wf(),
        b.wf(),
        !a.empty,
        !b.empty,
        bound_lt(b.hi, a.hi),
    ensures
        a.has(z),
        !b.has(z),
{
    match (a.hi, b.hi) {
        (Bound::Fin(n), Bound::Fin(m)) => {
            assert(m.view() < n.view());
            assert(a.has(n.view()));
            n.view()
        },
        (Bound::Fin(n), Bound::NegInf) => {
            assert(a.has(n.view()));
            n.view()
        },
        (Bound::PosInf, Bound::Fin(m)) => {
            let z = m.view() + 1;
            if bound_le(a.lo, b.hi) {
                assert(a.has(z));
                z
            } else {
                match a.lo {
                    Bound::Fin(h) => {
                        assert(a.has(h.view()));
                        h.view()
                    },
                    _ => {
                        assert(false);
                        z
                    },
                }
            }
        },
        _ => {
            assert(false);
            0
        },
    }
}

pub proof fn lemma_refines_endpoints(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        !a.empty,
        !b.empty,
        a.refines(b),
    ensures
        bound_le(b.lo, a.lo),
        bound_le(a.hi, b.hi),
{
    if !bound_le(b.lo, a.lo) {
        bound_le_total(a.lo, b.lo);
        assert(bound_lt(a.lo, b.lo));
        let z = lemma_below(a, b);
        assert(!b.has(z));
        assert(false);
    }
    if !bound_le(a.hi, b.hi) {
        bound_le_total(b.hi, a.hi);
        assert(bound_lt(b.hi, a.hi));
        let z = lemma_above(a, b);
        assert(!b.has(z));
        assert(false);
    }
}

pub proof fn lemma_add_mono(p: Bound, q: Bound, s: Bound)
    requires
        bound_le(p, q),
        p != Bound::PosInf,
        q != Bound::PosInf,
        s != Bound::PosInf,
    ensures
        bound_le(add_bound_spec(p, s), add_bound_spec(q, s)),
{
    match (p, q, s) {
        (Bound::Fin(x), Bound::Fin(y), Bound::Fin(z)) => {
            assert(x.view() + z.view() <= y.view() + z.view());
            assert(IBig::from_int(x.view() + z.view()).view() == x.view() + z.view());
            assert(IBig::from_int(y.view() + z.view()).view() == y.view() + z.view());
        },
        (Bound::NegInf, _, _) => {},
        (Bound::Fin(_), Bound::NegInf, _) => {
            assert(!bound_le(p, q));
        },
        (Bound::Fin(_), Bound::Fin(_), Bound::NegInf) => {},
        (Bound::Fin(_), Bound::Fin(_), Bound::PosInf) => {
            assert(s != Bound::PosInf);
        },
        (Bound::PosInf, _, _) => {
            assert(p != Bound::PosInf);
        },
        (_, Bound::PosInf, _) => {
            assert(q != Bound::PosInf);
        },
    }
}

pub proof fn lemma_add_mono_hi(p: Bound, q: Bound, s: Bound)
    requires
        bound_le(p, q),
        p != Bound::NegInf,
        q != Bound::NegInf,
        s != Bound::NegInf,
    ensures
        bound_le(add_bound_spec(p, s), add_bound_spec(q, s)),
{
    match (p, q, s) {
        (Bound::Fin(x), Bound::Fin(y), Bound::Fin(z)) => {
            assert(x.view() + z.view() <= y.view() + z.view());
            assert(IBig::from_int(x.view() + z.view()).view() == x.view() + z.view());
            assert(IBig::from_int(y.view() + z.view()).view() == y.view() + z.view());
        },
        (Bound::PosInf, Bound::PosInf, _) => {},
        (Bound::Fin(_), Bound::PosInf, _) => {},
        (Bound::PosInf, Bound::Fin(_), _) => {
            assert(!bound_le(p, q));
        },
        (Bound::Fin(_), Bound::Fin(_), Bound::PosInf) => {},
        (Bound::Fin(_), Bound::Fin(_), Bound::NegInf) => {
            assert(s != Bound::NegInf);
        },
        (Bound::NegInf, _, _) => {
            assert(p != Bound::NegInf);
        },
        (_, Bound::NegInf, _) => {
            assert(q != Bound::NegInf);
        },
    }
}

pub proof fn lemma_add_shaped(a: IntervalZ, c: IntervalZ)
    requires
        a.wf(),
        c.wf(),
        !a.empty,
        !c.empty,
    ensures
        !a.add_spec(c).empty,
        a.add_spec(c).lo == add_bound_spec(a.lo, c.lo),
        a.add_spec(c).hi == add_bound_spec(a.hi, c.hi),
{
    let lo = add_bound_spec(a.lo, c.lo);
    let hi = add_bound_spec(a.hi, c.hi);
    assert(lo != Bound::PosInf);
    assert(hi != Bound::NegInf);
    assert(bound_le(lo, hi));
}

pub proof fn join_monotone(a: IntervalZ, b: IntervalZ, c: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        a.refines(b),
    ensures
        a.join_spec(c).refines(b.join_spec(c)),
{
    assert forall|z: int| #![auto] a.join_spec(c).has(z) implies b.join_spec(c).has(z) by {
        if a.empty {
            lemma_join_has_side(c, b, z);
        } else if c.empty {
            assert(a.has(z));
        } else {
            lemma_refines_nonempty(a, b);
            lemma_refines_endpoints(a, b);
            lemma_bound_min_mono(b.lo, a.lo, c.lo);
            lemma_bound_max_mono(a.hi, b.hi, c.hi);
            lemma_bound_le_int_weaken(bound_min(b.lo, c.lo), bound_min(a.lo, c.lo), z);
            lemma_int_le_bound_weaken(z, bound_max(a.hi, c.hi), bound_max(b.hi, c.hi));
        }
    };
}

pub proof fn lemma_bound_min_mono(p: Bound, q: Bound, s: Bound)
    requires
        bound_le(p, q),
    ensures
        bound_le(bound_min(p, s), bound_min(q, s)),
{
    if bound_le(p, s) && bound_le(q, s) {
    } else if bound_le(p, s) {
        assert(bound_le(p, s));
    } else if bound_le(q, s) {
        lemma_bound_le_trans(p, q, s);
        assert(bound_le(p, s));
    } else {
        bound_le_refl(s);
    }
}

pub proof fn lemma_bound_max_mono(p: Bound, q: Bound, s: Bound)
    requires
        bound_le(p, q),
    ensures
        bound_le(bound_max(p, s), bound_max(q, s)),
{
    if bound_le(s, p) && bound_le(s, q) {
    } else if bound_le(s, q) {
    } else if bound_le(s, p) {
        lemma_bound_le_trans(s, p, q);
    } else {
        bound_le_refl(s);
    }
}

pub proof fn add_monotone(a: IntervalZ, b: IntervalZ, c: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        a.refines(b),
    ensures
        a.add_spec(c).refines(b.add_spec(c)),
{
    assert forall|z: int| #![auto] a.add_spec(c).has(z) implies b.add_spec(c).has(z) by {
        if !a.empty && !c.empty {
            lemma_refines_nonempty(a, b);
            lemma_refines_endpoints(a, b);
            lemma_add_shaped(a, c);
            lemma_add_shaped(b, c);
            lemma_add_mono(b.lo, a.lo, c.lo);
            lemma_add_mono_hi(a.hi, b.hi, c.hi);
            lemma_bound_le_int_weaken(b.add_spec(c).lo, a.add_spec(c).lo, z);
            lemma_int_le_bound_weaken(z, a.add_spec(c).hi, b.add_spec(c).hi);
        }
    };
}

pub proof fn neg_monotone(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        a.refines(b),
    ensures
        a.neg_spec().refines(b.neg_spec()),
{
    assert forall|z: int| #![auto] a.neg_spec().has(z) implies b.neg_spec().has(z) by {
        if !a.empty {
            lemma_refines_nonempty(a, b);
            lemma_refines_endpoints(a, b);
            lemma_neg_shaped(a);
            lemma_neg_shaped(b);
            lemma_neg_anti(a.hi, b.hi);
            lemma_neg_anti(b.lo, a.lo);
            lemma_bound_le_int_weaken(b.neg_spec().lo, a.neg_spec().lo, z);
            lemma_int_le_bound_weaken(z, a.neg_spec().hi, b.neg_spec().hi);
        }
    };
}

pub proof fn sub_monotone(a: IntervalZ, b: IntervalZ, c: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        a.refines(b),
    ensures
        a.sub_spec(c).refines(b.sub_spec(c)),
{
    lemma_neg_wf(c);
    assert(c.refines(c));
    neg_monotone(c, c);
    add_monotone(a, b, c.neg_spec());
}

pub proof fn lemma_neg_wf(a: IntervalZ)
    requires
        a.wf(),
    ensures
        a.neg_spec().wf(),
{
}

pub proof fn mul_monotone(a: IntervalZ, b: IntervalZ, c: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        a.refines(b),
    ensures
        a.mul_spec(c).refines(b.mul_spec(c)),
{
    assert forall|z: int| #![auto] a.mul_spec(c).has(z) implies b.mul_spec(c).has(z) by {
        if !a.empty && !c.empty {
            lemma_refines_nonempty(a, b);
            lemma_mul_hull_mono(a, b, c, z);
        }
    };
}

pub proof fn lemma_mul_hull_mono(a: IntervalZ, b: IntervalZ, c: IntervalZ, z: int)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        !a.empty,
        !b.empty,
        !c.empty,
        a.refines(b),
        a.mul_spec(c).has(z),
    ensures
        b.mul_spec(c).has(z),
{
    lemma_refines_endpoints(a, b);
    let ra = a.mul_spec(c);
    let rb = b.mul_spec(c);
    lemma_mul_corner_covered(a, b, c, a.lo, c.lo);
    lemma_mul_corner_covered(a, b, c, a.lo, c.hi);
    lemma_mul_corner_covered(a, b, c, a.hi, c.lo);
    lemma_mul_corner_covered(a, b, c, a.hi, c.hi);
    assert(bound_le(rb.lo, ra.lo));
    assert(bound_le(ra.hi, rb.hi));
    lemma_bound_le_int_weaken(rb.lo, ra.lo, z);
    lemma_int_le_bound_weaken(z, ra.hi, rb.hi);
}

pub proof fn lemma_endpoint_value(a: IntervalZ, end: Bound)
    requires
        a.wf(),
        !a.empty,
        end == a.lo || end == a.hi,
    ensures
        is_fin_bound(end) ==> a.has(fin_view(end)),
{
    if is_fin_bound(end) {
        match end {
            Bound::Fin(n) => {
                assert(a.has(n.view()));
            },
            _ => {},
        }
    }
}

pub proof fn lemma_mul_corner_covered(a: IntervalZ, b: IntervalZ, c: IntervalZ, u: Bound, v: Bound)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        !a.empty,
        !b.empty,
        !c.empty,
        a.refines(b),
        u == a.lo || u == a.hi,
        v == c.lo || v == c.hi,
    ensures
        match ext_mul_spec(u, v) {
            Bound::NegInf => b.mul_spec(c).lo == Bound::NegInf,
            Bound::PosInf => b.mul_spec(c).hi == Bound::PosInf,
            Bound::Fin(n) => b.mul_spec(c).has(n.view()),
        },
{
    lemma_refines_endpoints(a, b);
    lemma_endpoint_value(a, u);
    lemma_endpoint_value(c, v);
    let rb = b.mul_spec(c);
    match (u, v) {
        (Bound::Fin(x), Bound::Fin(y)) => {
            assert(a.has(x.view()));
            assert(b.has(x.view()));
            assert(c.has(y.view()));
            lemma_mul_by_signs(b, c, x.view(), y.view());
            assert(IBig::from_int(x.view() * y.view()).view() == x.view() * y.view());
        },
        (Bound::Fin(x), Bound::PosInf) | (Bound::PosInf, Bound::Fin(x)) => {
            if x.view() == 0 {
                assert(a.has(0) || c.has(0));
                lemma_zero_in_mul(b, c);
            } else if x.view() < 0 {
                lemma_inf_mul_propagates(a, b, c, u, v);
                assert(rb.lo == Bound::NegInf);
            } else {
                lemma_inf_mul_propagates(a, b, c, u, v);
                assert(rb.hi == Bound::PosInf);
            }
        },
        (Bound::Fin(x), Bound::NegInf) | (Bound::NegInf, Bound::Fin(x)) => {
            if x.view() == 0 {
                assert(a.has(0) || c.has(0));
                lemma_zero_in_mul(b, c);
            } else if x.view() > 0 {
                lemma_inf_mul_propagates(a, b, c, u, v);
                assert(rb.lo == Bound::NegInf);
            } else {
                lemma_inf_mul_propagates(a, b, c, u, v);
                assert(rb.hi == Bound::PosInf);
            }
        },
        (Bound::NegInf, Bound::PosInf) | (Bound::PosInf, Bound::NegInf) => {
            lemma_inf_mul_propagates(a, b, c, u, v);
            assert(rb.lo == Bound::NegInf);
        },
        (Bound::PosInf, Bound::PosInf) | (Bound::NegInf, Bound::NegInf) => {
            lemma_inf_mul_propagates(a, b, c, u, v);
            assert(rb.hi == Bound::PosInf);
        },
    }
}

pub proof fn lemma_zero_in_mul(b: IntervalZ, c: IntervalZ)
    requires
        b.wf(),
        c.wf(),
        !b.empty,
        !c.empty,
        b.has(0) || c.has(0),
    ensures
        b.mul_spec(c).has(0),
{
    if b.has(0) {
        let y = lemma_witness(c);
        vstd::arithmetic::mul::lemma_mul_basics(y);
        lemma_mul_by_signs(b, c, 0, y);
        assert(0 * y == 0);
    } else {
        let x = lemma_witness(b);
        vstd::arithmetic::mul::lemma_mul_basics(x);
        lemma_mul_by_signs(b, c, x, 0);
        assert(x * 0 == 0);
    }
}

pub proof fn lemma_neg_inf_lo(b: IntervalZ, c: IntervalZ)
    requires
        b.wf(),
        c.wf(),
        !b.empty,
        !c.empty,
        ext_mul_spec(b.lo, c.lo) == Bound::NegInf || ext_mul_spec(b.lo, c.hi) == Bound::NegInf
            || ext_mul_spec(b.hi, c.lo) == Bound::NegInf || ext_mul_spec(b.hi, c.hi)
            == Bound::NegInf,
    ensures
        b.mul_spec(c).lo == Bound::NegInf,
{
    let lo = bound_min(
        bound_min(ext_mul_spec(b.lo, c.lo), ext_mul_spec(b.lo, c.hi)),
        bound_min(ext_mul_spec(b.hi, c.lo), ext_mul_spec(b.hi, c.hi)),
    );
    assert(lo == Bound::NegInf);
    assert(b.mul_spec(c).lo == Bound::NegInf);
}

pub proof fn lemma_pos_inf_hi(b: IntervalZ, c: IntervalZ)
    requires
        b.wf(),
        c.wf(),
        !b.empty,
        !c.empty,
        ext_mul_spec(b.lo, c.lo) == Bound::PosInf || ext_mul_spec(b.lo, c.hi) == Bound::PosInf
            || ext_mul_spec(b.hi, c.lo) == Bound::PosInf || ext_mul_spec(b.hi, c.hi)
            == Bound::PosInf,
    ensures
        b.mul_spec(c).hi == Bound::PosInf,
{
    let hi = bound_max(
        bound_max(ext_mul_spec(b.lo, c.lo), ext_mul_spec(b.lo, c.hi)),
        bound_max(ext_mul_spec(b.hi, c.lo), ext_mul_spec(b.hi, c.hi)),
    );
    assert(hi == Bound::PosInf);
    assert(b.mul_spec(c).hi == Bound::PosInf);
}

pub proof fn lemma_inf_mul_propagates(
    a: IntervalZ,
    b: IntervalZ,
    c: IntervalZ,
    u: Bound,
    v: Bound,
)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        !a.empty,
        !b.empty,
        !c.empty,
        a.refines(b),
        u == a.lo || u == a.hi,
        v == c.lo || v == c.hi,
        ext_mul_spec(u, v) == Bound::NegInf || ext_mul_spec(u, v) == Bound::PosInf,
    ensures
        ext_mul_spec(u, v) == Bound::NegInf ==> b.mul_spec(c).lo == Bound::NegInf,
        ext_mul_spec(u, v) == Bound::PosInf ==> b.mul_spec(c).hi == Bound::PosInf,
{
    lemma_refines_endpoints(a, b);
    if ext_mul_spec(u, v) == Bound::NegInf {
        if u == Bound::NegInf {
            assert(b.lo == Bound::NegInf);
            assert(ext_mul_spec(b.lo, v) == Bound::NegInf);
        } else if v == Bound::NegInf {
            if u == a.hi || bound_le(Bound::Fin(IBig::from_int(0)), b.hi) {
                assert(ext_mul_spec(b.hi, v) == Bound::NegInf || ext_mul_spec(b.lo, v)
                    == Bound::NegInf);
            }
        }
        lemma_neg_inf_lo(b, c);
    } else {
        if u == Bound::PosInf {
            assert(b.hi == Bound::PosInf);
            assert(ext_mul_spec(b.hi, v) == Bound::PosInf);
        }
        lemma_pos_inf_hi(b, c);
    }
}

pub proof fn div_monotone(a: IntervalZ, b: IntervalZ, c: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        c.wf(),
        a.refines(b),
    ensures
        a.div_spec(c).0.refines(b.div_spec(c).0),
{
    assert forall|z: int| #![auto] a.div_spec(c).0.has(z) implies b.div_spec(c).0.has(z) by {
        if !a.empty && !c.empty && !is_zero_singleton(c) {
            lemma_refines_nonempty(a, b);
            if c.has(0) {
                let dn = c.meet_spec(neg_unit_ray());
                let dp = c.meet_spec(pos_unit_ray());
                assert(IBig::from_int(0).view() == 0);
                assert(!neg_unit_ray().has(0));
                assert(!pos_unit_ray().has(0));
                meet_has_iff(c, neg_unit_ray(), 0);
                meet_has_iff(c, pos_unit_ray(), 0);
                lemma_div_one_mono(a, b, dn);
                lemma_div_one_mono(a, b, dp);
                let an = a.div_one_spec(dn);
                let ap = a.div_one_spec(dp);
                let bn = b.div_one_spec(dn);
                let bp = b.div_one_spec(dp);
                lemma_div_one_wf(a, dn);
                lemma_div_one_wf(a, dp);
                lemma_div_one_wf(b, dn);
                lemma_div_one_wf(b, dp);
                join_monotone(an, bn, ap);
                join_comm(bn, ap);
                lemma_eq_abs_refines(bn.join_spec(ap), ap.join_spec(bn));
                lemma_refines_trans(an.join_spec(ap), bn.join_spec(ap), ap.join_spec(bn));
                join_monotone(ap, bp, bn);
                join_comm(bp, bn);
                lemma_eq_abs_refines(bp.join_spec(bn), bn.join_spec(bp));
                lemma_refines_trans(ap.join_spec(bn), bp.join_spec(bn), bn.join_spec(bp));
                lemma_refines_trans(an.join_spec(ap), ap.join_spec(bn), bn.join_spec(bp));
            } else {
                lemma_div_one_mono(a, b, c);
            }
        }
    };
}

pub proof fn lemma_refines_trans(a: IntervalZ, b: IntervalZ, c: IntervalZ)
    requires
        a.refines(b),
        b.refines(c),
    ensures
        a.refines(c),
{
}

pub proof fn lemma_eq_abs_refines(a: IntervalZ, b: IntervalZ)
    requires
        a.eq_abs(b),
    ensures
        a.refines(b),
        b.refines(a),
{
    assert forall|z: int| #![auto] a.has(z) implies b.has(z) by {
        lemma_eq_abs_has(a, b, z);
    };
    assert forall|z: int| #![auto] b.has(z) implies a.has(z) by {
        lemma_eq_abs_has(a, b, z);
    };
}

pub proof fn lemma_div_zero_quot(d: IntervalZ, x: int) -> (y: int)
    requires
        d.wf(),
        !d.empty,
        !d.has(0),
        x >= 0,
        d.hi == Bound::PosInf || d.lo == Bound::NegInf,
    ensures
        d.has(y),
        y != 0,
        x / y == 0,
{
    if d.hi == Bound::PosInf {
        let n = fin_view(d.lo);
        let y = if n > x { n } else { x + 1 };
        assert(n >= 1);
        assert(y >= 1 && y > x && d.has(y));
        vstd::arithmetic::div_mod::lemma_basic_div(x, y);
        y
    } else {
        let m = fin_view(d.hi);
        let y = if m < -(x + 1) { m } else { -(x + 1) };
        assert(y <= -1 && d.has(y));
        lemma_euclid_neg_div(x, -y);
        vstd::arithmetic::div_mod::lemma_basic_div(x, -y);
        assert(x / y == -(x / (-y)));
        assert(x / (-y) == 0);
        y
    }
}

pub proof fn lemma_div_corner_covered(a: IntervalZ, b: IntervalZ, d: IntervalZ, u: Bound, v: Bound)
    requires
        a.wf(),
        b.wf(),
        d.wf(),
        !a.empty,
        !b.empty,
        !d.empty,
        !d.has(0),
        a.refines(b),
        u == a.lo || u == a.hi,
        v == d.lo || v == d.hi,
    ensures
        match ext_div_spec(u, v) {
            Some(Bound::NegInf) => b.div_one_spec(d).lo == Bound::NegInf,
            Some(Bound::PosInf) => b.div_one_spec(d).hi == Bound::PosInf,
            Some(Bound::Fin(n)) => b.div_one_spec(d).has(n.view()),
            None => b.div_one_spec(d) == IntervalZ::top_spec(),
        },
{
    lemma_refines_endpoints(a, b);
    lemma_ext_div_some(u, v);
    match (u, v) {
        (Bound::Fin(x), Bound::Fin(den)) => {
            assert(a.has(x.view()));
            assert(b.has(x.view()));
            assert(d.has(den.view()));
            assert(den.view() != 0);
            lemma_div_concrete_in_hull(b, d, x.view(), den.view());
            assert(IBig::from_int(x.view() / den.view()).view() == x.view() / den.view());
        },
        (Bound::Fin(x), Bound::PosInf) | (Bound::Fin(x), Bound::NegInf) => {
            if x.view() >= 0 {
                let y = lemma_div_zero_quot(d, x.view());
                assert(b.has(x.view()));
                lemma_div_concrete_in_hull(b, d, x.view(), y);
                assert(x.view() / y == 0);
                assert(IBig::from_int(0).view() == 0);
            } else if v == Bound::PosInf {
                let anchor = fin_view(d.lo);
                assert(anchor >= 1 && d.has(anchor));
                assert(b.has(x.view()));
                lemma_div_concrete_in_hull(b, d, x.view(), anchor);
                vstd::arithmetic::div_mod::lemma_div_is_ordered(x.view(), -1, anchor);
                assert((-1) / anchor == -1) by (nonlinear_arith)
                    requires
                        anchor >= 1,
                ;
                assert(x.view() / anchor <= -1);
                assert(b.div_one_spec(d).has(x.view() / anchor));
                assert(int_le_bound(0, b.div_one_spec(d).hi) || b.div_one_spec(d).hi == Bound::PosInf);
                assert(b.div_one_spec(d).has(0));
            } else {
                let anchor = fin_view(d.hi);
                assert(anchor <= -1 && d.has(anchor));
                assert(b.has(x.view()));
                lemma_div_concrete_in_hull(b, d, x.view(), anchor);
                lemma_euclid_neg_div(x.view(), -anchor);
                assert(b.div_one_spec(d).has(0));
            }
        },
        (Bound::NegInf, _) => {
            assert(b.lo == Bound::NegInf);
            assert(ext_div_spec(b.lo, v) == ext_div_spec(u, v));
        },
        (Bound::PosInf, _) => {
            assert(b.hi == Bound::PosInf);
            assert(ext_div_spec(b.hi, v) == ext_div_spec(u, v));
        },
    }
}

pub proof fn lemma_div_hull_mono(a: IntervalZ, b: IntervalZ, d: IntervalZ, z: int)
    requires
        a.wf(),
        b.wf(),
        d.wf(),
        !a.empty,
        !b.empty,
        !d.empty,
        !d.has(0),
        a.refines(b),
        a.div_one_spec(d).has(z),
    ensures
        b.div_one_spec(d).has(z),
{
    lemma_refines_endpoints(a, b);
    let ra = a.div_one_spec(d);
    let rb = b.div_one_spec(d);
    lemma_div_corner_covered(a, b, d, a.lo, d.lo);
    lemma_div_corner_covered(a, b, d, a.lo, d.hi);
    lemma_div_corner_covered(a, b, d, a.hi, d.lo);
    lemma_div_corner_covered(a, b, d, a.hi, d.hi);
    assert(bound_le(rb.lo, ra.lo));
    assert(bound_le(ra.hi, rb.hi));
    lemma_bound_le_int_weaken(rb.lo, ra.lo, z);
    lemma_int_le_bound_weaken(z, ra.hi, rb.hi);
}

pub proof fn lemma_div_one_mono(a: IntervalZ, b: IntervalZ, d: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        d.wf(),
        a.refines(b),
        !d.has(0),
    ensures
        a.div_one_spec(d).refines(b.div_one_spec(d)),
{
    if !a.empty && !d.empty {
        lemma_refines_nonempty(a, b);
        assert forall|z: int| #![auto] a.div_one_spec(d).has(z) implies b.div_one_spec(d).has(z)
            by {
            lemma_div_hull_mono(a, b, d, z);
        };
    }
}

pub proof fn meet_chain_sound(cur: IntervalZ, facts: Seq<IntervalZ>, fuel: nat)
    requires
        cur.wf(),
        forall|i: int| 0 <= i < facts.len() ==> (#[trigger] facts[i]).wf(),
    ensures
        meet_chain(cur, facts, fuel).wf(),
        meet_chain(cur, facts, fuel).refines(cur),
        fuel == 0 ==> meet_chain(cur, facts, fuel) == cur,
    decreases facts.len(),
{
    if facts.len() == 0 || fuel == 0 {
    } else {
        let next = cur.meet_spec(facts[0]);
        if next.eq_abs(cur) {
            meet_chain_sound(cur, facts.skip(1), fuel);
        } else {
            meet_chain_sound(next, facts.skip(1), (fuel - 1) as nat);
        }
    }
}

} // verus!

impl Clone for Bound {
    fn clone(&self) -> Self {
        match self {
            Bound::NegInf => Bound::NegInf,
            Bound::PosInf => Bound::PosInf,
            Bound::Fin(n) => Bound::Fin(n.clone()),
        }
    }
}

impl PartialEq for Bound {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Bound::NegInf, Bound::NegInf) => true,
            (Bound::PosInf, Bound::PosInf) => true,
            (Bound::Fin(x), Bound::Fin(y)) => x == y,
            _ => false,
        }
    }
}

impl Eq for Bound {}

impl core::fmt::Debug for Bound {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Bound::NegInf => write!(f, "NegInf"),
            Bound::PosInf => write!(f, "PosInf"),
            Bound::Fin(n) => write!(f, "Fin({n:?})"),
        }
    }
}

impl Clone for IntervalZ {
    fn clone(&self) -> Self {
        IntervalZ { empty: self.empty, lo: self.lo.clone(), hi: self.hi.clone() }
    }
}

impl PartialEq for IntervalZ {
    fn eq(&self, other: &Self) -> bool {
        self.empty == other.empty && self.lo == other.lo && self.hi == other.hi
    }
}

impl Eq for IntervalZ {}

impl core::fmt::Debug for IntervalZ {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.empty {
            write!(f, "bottom")
        } else {
            write!(f, "[{:?}, {:?}]", self.lo, self.hi)
        }
    }
}

impl Clone for IntervalR {
    fn clone(&self) -> Self {
        IntervalR {
            empty: self.empty,
            lo: self.lo.clone(),
            hi: self.hi.clone(),
            lo_closed: self.lo_closed,
            hi_closed: self.hi_closed,
        }
    }
}

impl core::fmt::Debug for IntervalR {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.empty {
            write!(f, "bottom")
        } else {
            let l = if self.lo_closed { "[" } else { "(" };
            let h = if self.hi_closed { "]" } else { ")" };
            write!(f, "{l}{:?}, {:?}{h}", self.lo, self.hi)
        }
    }
}
