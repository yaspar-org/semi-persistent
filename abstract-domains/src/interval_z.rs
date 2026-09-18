// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(unused_imports, unused_variables)]
//! IntervalZ: closed intervals over unbounded integers, with explicit infinities.
//!
//! This is Task 1 §3.2 of the lattice-semantics practicum:
//!
//! ```text
//! Bound     = NegInf | Fin(i64) | PosInf
//! IntervalZ = { empty, lo: Bound, hi: Bound }
//! values    = every integer z with lo <= z <= hi   (empty has none)
//! ```
//!
//! Finite endpoints are stored as `i64` (an executable stand-in for IBig).
//! Membership and every containment contract are stated over mathematical
//! `int`, so arithmetic is the unbounded integer ring: nothing wraps. When a
//! finite-endpoint sum or product falls outside `i64`, the implementation
//! widens that endpoint to the matching infinity, or to `top` if a lower
//! bound would otherwise become `PosInf` (which would look empty and be
//! unsound). Stopping at `top` is always a sound over-approximation.
//!
//! Also proved: lattice laws of §3.5, monotone transfers, widen, narrow,
//! and the per-class refinement budget of §4.5.

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Bounds
// ---------------------------------------------------------------------------

/// Three-way bound: -∞, a finite integer, or +∞.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Bound {
    NegInf,
    Fin(i64),
    PosInf,
}

/// `a` is less-or-equal `b` in the extended integers.
pub open spec fn bound_le(a: Bound, b: Bound) -> bool {
    match (a, b) {
        (Bound::NegInf, _) => true,
        (_, Bound::PosInf) => true,
        (Bound::PosInf, Bound::NegInf) => false,
        (Bound::PosInf, Bound::Fin(_)) => false,
        (Bound::Fin(_), Bound::NegInf) => false,
        (Bound::Fin(x), Bound::Fin(y)) => x <= y,
    }
}

pub open spec fn bound_eq(a: Bound, b: Bound) -> bool {
    match (a, b) {
        (Bound::NegInf, Bound::NegInf) => true,
        (Bound::PosInf, Bound::PosInf) => true,
        (Bound::Fin(x), Bound::Fin(y)) => x == y,
        _ => false,
    }
}

pub open spec fn bound_lt(a: Bound, b: Bound) -> bool {
    bound_le(a, b) && !bound_eq(a, b)
}

pub open spec fn bound_min(a: Bound, b: Bound) -> Bound {
    if bound_le(a, b) {
        a
    } else {
        b
    }
}

pub open spec fn bound_max(a: Bound, b: Bound) -> Bound {
    if bound_le(a, b) {
        b
    } else {
        a
    }
}

/// Lower-bound comparison: `b <= z` in the extended integers.
pub open spec fn bound_le_int(b: Bound, z: int) -> bool {
    match b {
        Bound::NegInf => true,
        Bound::Fin(n) => n as int <= z,
        Bound::PosInf => false,
    }
}

/// Upper-bound comparison: `z <= b` in the extended integers.
pub open spec fn int_le_bound(z: int, b: Bound) -> bool {
    match b {
        Bound::PosInf => true,
        Bound::Fin(n) => z <= n as int,
        Bound::NegInf => false,
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

pub proof fn bound_le_antisym(a: Bound, b: Bound)
    requires
        bound_le(a, b),
        bound_le(b, a),
    ensures
        a == b,
{
}

pub proof fn bound_le_trans(a: Bound, b: Bound, c: Bound)
    requires
        bound_le(a, b),
        bound_le(b, c),
    ensures
        bound_le(a, c),
{
}

pub proof fn bound_min_comm(a: Bound, b: Bound)
    ensures
        bound_min(a, b) == bound_min(b, a),
{
}

pub proof fn bound_max_comm(a: Bound, b: Bound)
    ensures
        bound_max(a, b) == bound_max(b, a),
{
}

pub proof fn bound_min_idem(a: Bound)
    ensures
        bound_min(a, a) == a,
{
}

pub proof fn bound_max_idem(a: Bound)
    ensures
        bound_max(a, a) == a,
{
}

pub proof fn bound_min_assoc(a: Bound, b: Bound, c: Bound)
    ensures
        bound_min(bound_min(a, b), c) == bound_min(a, bound_min(b, c)),
{
}

pub proof fn bound_max_assoc(a: Bound, b: Bound, c: Bound)
    ensures
        bound_max(bound_max(a, b), c) == bound_max(a, bound_max(b, c)),
{
}

/// Mathematical `i64::MIN` / `i64::MAX` as `int`. Parenthesised so the
/// verifier does not parse `MIN as` as a single token.
pub open spec fn spec_i64_min() -> int {
    (i64::MIN) as int
}

pub open spec fn spec_i64_max() -> int {
    (i64::MAX) as int
}

pub open spec fn in_i64(n: int) -> bool {
    spec_i64_min() <= n && n <= spec_i64_max()
}

/// Finite sum. Matches `i64::checked_add`: overflow widens to ±∞.
pub open spec fn fin_add_spec(a: i64, b: i64) -> Bound {
    match a.checked_add(b) {
        Some(s) => Bound::Fin(s),
        None => if a >= 0 {
            Bound::PosInf
        } else {
            Bound::NegInf
        },
    }
}

/// Finite product. Matches `i64::checked_mul`: overflow widens to ±∞.
pub open spec fn fin_mul_spec(a: i64, b: i64) -> Bound {
    match a.checked_mul(b) {
        Some(p) => Bound::Fin(p),
        None => if (a >= 0) == (b >= 0) {
            Bound::PosInf
        } else {
            Bound::NegInf
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
        (Bound::Fin(x), Bound::Fin(y)) => fin_add_spec(x, y),
    }
}

pub open spec fn neg_bound_spec(a: Bound) -> Bound {
    match a {
        Bound::NegInf => Bound::PosInf,
        Bound::PosInf => Bound::NegInf,
        Bound::Fin(n) =>
            if n == i64::MIN {
                Bound::PosInf
            } else {
                Bound::Fin((-(n as int)) as i64)
            },
    }
}

impl Bound {
    pub fn le(&self, other: Bound) -> (r: bool)
        ensures
            r == bound_le(*self, other),
    {
        match (*self, other) {
            (Bound::NegInf, _) => true,
            (_, Bound::PosInf) => true,
            (Bound::PosInf, Bound::NegInf) => false,
            (Bound::PosInf, Bound::Fin(_)) => false,
            (Bound::Fin(_), Bound::NegInf) => false,
            (Bound::Fin(x), Bound::Fin(y)) => x <= y,
        }
    }

    pub fn eq_bound(self, other: Bound) -> (r: bool)
        ensures
            r == bound_eq(self, other),
    {
        match (self, other) {
            (Bound::NegInf, Bound::NegInf) => true,
            (Bound::PosInf, Bound::PosInf) => true,
            (Bound::Fin(x), Bound::Fin(y)) => x == y,
            _ => false,
        }
    }

    pub fn lt(self, other: Bound) -> (r: bool)
        ensures
            r == bound_lt(self, other),
    {
        self.le(other) && !self.eq_bound(other)
    }

    pub fn min(self, other: Bound) -> (r: Bound)
        ensures
            r == bound_min(self, other),
    {
        if self.le(other) {
            self
        } else {
            other
        }
    }

    pub fn max(self, other: Bound) -> (r: Bound)
        ensures
            r == bound_max(self, other),
    {
        if self.le(other) {
            other
        } else {
            self
        }
    }

    pub fn add(self, other: Bound) -> (r: Bound)
        ensures
            r == add_bound_spec(self, other),
    {
        match (self, other) {
            (Bound::NegInf, Bound::PosInf) => Bound::NegInf,
            (Bound::PosInf, Bound::NegInf) => Bound::PosInf,
            (Bound::NegInf, _) => Bound::NegInf,
            (_, Bound::NegInf) => Bound::NegInf,
            (Bound::PosInf, _) => Bound::PosInf,
            (_, Bound::PosInf) => Bound::PosInf,
            (Bound::Fin(x), Bound::Fin(y)) => Bound::fin_add(x, y),
        }
    }

    pub fn neg(self) -> (r: Bound)
        ensures
            r == neg_bound_spec(self),
    {
        match self {
            Bound::NegInf => Bound::PosInf,
            Bound::PosInf => Bound::NegInf,
            Bound::Fin(n) => {
                if n == i64::MIN {
                    Bound::PosInf
                } else {
                    Bound::Fin(-n)
                }
            },
        }
    }

    pub fn fin_add(a: i64, b: i64) -> (r: Bound)
        ensures
            r == fin_add_spec(a, b),
    {
        match a.checked_add(b) {
            Some(s) => Bound::Fin(s),
            None => {
                if a >= 0 {
                    Bound::PosInf
                } else {
                    Bound::NegInf
                }
            },
        }
    }

    pub fn fin_mul(a: i64, b: i64) -> (r: Bound)
        ensures
            r == fin_mul_spec(a, b),
    {
        match a.checked_mul(b) {
            Some(p) => Bound::Fin(p),
            None => {
                if (a >= 0) == (b >= 0) {
                    Bound::PosInf
                } else {
                    Bound::NegInf
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Alarm lattice (concretization, not severity)
// ---------------------------------------------------------------------------

/// Outcomes of a possibly-failing operation. Meaning is the set of concrete
/// boolean error flags the alarm stands for:
/// `NoError = {false}`, `DefiniteError = {true}`, `MaybeError = {false,true}`.
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
        Alarm::DefiniteError.join_spec(Alarm::NoError) == Alarm::MaybeError,
{
}

// ---------------------------------------------------------------------------
// IntervalZ
// ---------------------------------------------------------------------------

/// Closed interval over the unbounded integers, plus an explicit bottom.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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

    pub open spec fn has(self, z: int) -> bool {
        !self.empty && bound_le_int(self.lo, z) && int_le_bound(z, self.hi)
    }

    pub open spec fn refines(self, other: IntervalZ) -> bool {
        forall|z: int| #![auto] self.has(z) ==> other.has(z)
    }

    pub open spec fn eq_abs(self, other: IntervalZ) -> bool {
        (self.empty && other.empty) || (!self.empty && !other.empty && self.lo == other.lo
            && self.hi == other.hi)
    }

    pub open spec fn bottom_spec() -> IntervalZ {
        IntervalZ { empty: true, lo: Bound::Fin(0i64), hi: Bound::Fin(0i64) }
    }

    pub open spec fn top_spec() -> IntervalZ {
        IntervalZ { empty: false, lo: Bound::NegInf, hi: Bound::PosInf }
    }

    pub fn bottom() -> (r: IntervalZ)
        ensures
            r.wf(),
            r == IntervalZ::bottom_spec(),
            forall|z: int| #![auto] !r.has(z),
    {
        IntervalZ { empty: true, lo: Bound::Fin(0i64), hi: Bound::Fin(0i64) }
    }

    pub fn top() -> (r: IntervalZ)
        ensures
            r.wf(),
            r == IntervalZ::top_spec(),
            forall|z: int| #![auto] r.has(z),
    {
        IntervalZ { empty: false, lo: Bound::NegInf, hi: Bound::PosInf }
    }

    pub fn constant(n: i64) -> (r: IntervalZ)
        ensures
            r.wf(),
            !r.empty,
            r.has(n as int),
            r.lo == Bound::Fin(n) && r.hi == Bound::Fin(n),
    {
        IntervalZ { empty: false, lo: Bound::Fin(n), hi: Bound::Fin(n) }
    }

    /// Well-formed range constructor. `lo > hi` becomes bottom.
    pub fn range(lo: Bound, hi: Bound) -> (r: IntervalZ)
        ensures
            r.wf(),
            !bound_le(lo, hi) || lo == Bound::PosInf || hi == Bound::NegInf ==> r.empty,
            bound_le(lo, hi) && lo != Bound::PosInf && hi != Bound::NegInf ==> !r.empty && r.lo
                == lo && r.hi == hi,
    {
        if lo.le(hi) {
            match (lo, hi) {
                (Bound::PosInf, _) => IntervalZ::bottom(),
                (_, Bound::NegInf) => IntervalZ::bottom(),
                _ => IntervalZ { empty: false, lo, hi },
            }
        } else {
            IntervalZ::bottom()
        }
    }

    pub fn contains(&self, x: i64) -> (r: bool)
        ensures
            r == self.has(x as int),
    {
        if self.empty {
            false
        } else {
            bound_le_int_exec(self.lo, x) && int_le_bound_exec(x, self.hi)
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
            let lo = self.lo.max(t.lo);
            let hi = self.hi.min(t.hi);
            let r = if !lo.le(hi) {
                IntervalZ::bottom()
            } else {
                match (lo, hi) {
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
            *t
        } else if t.empty {
            *self
        } else {
            let lo = self.lo.min(t.lo);
            let hi = self.hi.max(t.hi);
            IntervalZ { empty: false, lo, hi }
        }
    }

    // ----- arithmetic -----

    pub open spec fn add_spec(self, t: IntervalZ) -> IntervalZ {
        if self.empty || t.empty {
            IntervalZ::bottom_spec()
        } else {
            let lo = add_bound_spec(self.lo, t.lo);
            let hi = add_bound_spec(self.hi, t.hi);
            if lo == Bound::PosInf || hi == Bound::NegInf {
                IntervalZ::top_spec()
            } else if !bound_le(lo, hi) {
                IntervalZ::bottom_spec()
            } else {
                IntervalZ { empty: false, lo, hi }
            }
        }
    }

    pub open spec fn neg_spec(self) -> IntervalZ {
        if self.empty {
            IntervalZ::bottom_spec()
        } else {
            let lo = neg_bound_spec(self.hi);
            let hi = neg_bound_spec(self.lo);
            if lo == Bound::PosInf || hi == Bound::NegInf {
                IntervalZ::top_spec()
            } else if !bound_le(lo, hi) {
                IntervalZ::bottom_spec()
            } else {
                IntervalZ { empty: false, lo, hi }
            }
        }
    }

    pub open spec fn sub_spec(self, t: IntervalZ) -> IntervalZ {
        self.add_spec(t.neg_spec())
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
            proof {
                assert forall|x: int, y: int| #![auto] self.has(x) && t.has(y) implies
                    IntervalZ::bottom_spec().has(x + y) by {
                    assert(!self.has(x) || !t.has(y));
                };
            }
            IntervalZ::bottom()
        } else {
            let lo = self.lo.add(t.lo);
            let hi = self.hi.add(t.hi);
            let r = match (lo, hi) {
                (Bound::PosInf, _) => IntervalZ::top(),
                (_, Bound::NegInf) => IntervalZ::top(),
                _ => IntervalZ::range(lo, hi),
            };
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
            let lo = self.hi.neg();
            let hi = self.lo.neg();
            let r = match (lo, hi) {
                (Bound::PosInf, _) => IntervalZ::top(),
                (_, Bound::NegInf) => IntervalZ::top(),
                _ => IntervalZ::range(lo, hi),
            };
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

    pub open spec fn is_finite(self) -> bool {
        !self.empty && matches_fin(self.lo) && matches_fin(self.hi)
    }

    pub open spec fn mul_spec(self, t: IntervalZ) -> IntervalZ {
        if self.empty || t.empty {
            IntervalZ::bottom_spec()
        } else if is_zero_singleton(self) || is_zero_singleton(t) {
            IntervalZ { empty: false, lo: Bound::Fin(0i64), hi: Bound::Fin(0i64) }
        } else {
            IntervalZ::top_spec()
        }
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
        } else if self.is_zero() || t.is_zero() {
            proof {
                lemma_mul_zero_contains(*self, *t);
            }
            IntervalZ::constant(0i64)
        } else {
            proof {
                assert forall|x: int, y: int| #![auto] self.has(x) && t.has(y) implies
                    IntervalZ::top_spec().has(x * y) by {};
            }
            IntervalZ::top()
        }
    }

    pub fn finite(&self) -> (r: bool)
        ensures
            r == self.is_finite(),
    {
        !self.empty && is_fin(self.lo) && is_fin(self.hi)
    }

    pub fn is_zero(&self) -> (r: bool)
        ensures
            r == is_zero_singleton(*self),
    {
        match (self.empty, self.lo, self.hi) {
            (false, Bound::Fin(x), Bound::Fin(y)) => x == 0i64 && y == 0i64,
            _ => false,
        }
    }

    // ----- widen / narrow -----

    pub open spec fn widen_spec(self, t: IntervalZ) -> IntervalZ {
        if self.empty {
            t
        } else if t.empty {
            self
        } else {
            let lo = if bound_lt(t.lo, self.lo) {
                Bound::NegInf
            } else {
                self.lo
            };
            let hi = if bound_lt(self.hi, t.hi) {
                Bound::PosInf
            } else {
                self.hi
            };
            IntervalZ { empty: false, lo, hi }
        }
    }

    pub open spec fn narrow_spec(self, t: IntervalZ) -> IntervalZ {
        if self.empty || t.empty {
            IntervalZ::bottom_spec()
        } else {
            let lo = if self.lo == Bound::NegInf {
                t.lo
            } else {
                self.lo
            };
            let hi = if self.hi == Bound::PosInf {
                t.hi
            } else {
                self.hi
            };
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
            *t
        } else if t.empty {
            *self
        } else {
            let lo = if t.lo.lt(self.lo) {
                Bound::NegInf
            } else {
                self.lo
            };
            let hi = if self.hi.lt(t.hi) {
                Bound::PosInf
            } else {
                self.hi
            };
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
    {
        if self.empty || t.empty {
            IntervalZ::bottom()
        } else {
            let lo = match self.lo {
                Bound::NegInf => t.lo,
                _ => self.lo,
            };
            let hi = match self.hi {
                Bound::PosInf => t.hi,
                _ => self.hi,
            };
            if !lo.le(hi) {
                IntervalZ::bottom()
            } else {
                match (lo, hi) {
                    (Bound::PosInf, _) => IntervalZ::bottom(),
                    (_, Bound::NegInf) => IntervalZ::bottom(),
                    _ => IntervalZ { empty: false, lo, hi },
                }
            }
        }
    }

    /// §4.5 refinement budget: meeting `fact` into `self`. Budget 0 keeps
    /// `self` (sound: a looser value still over-approximates). A positive
    /// budget takes the meet, which is always a refinement.
    pub open spec fn refine_spec(self, fact: IntervalZ, budget: nat) -> IntervalZ {
        if budget == 0 {
            self
        } else {
            self.meet_spec(fact)
        }
    }

    pub fn refine(&self, fact: &IntervalZ, budget: u8) -> (r: IntervalZ)
        requires
            self.wf(),
            fact.wf(),
        ensures
            r.wf(),
            r.eq_abs(self.refine_spec(*fact, budget as nat)),
            r.refines(*self),
            budget == 0 ==> r.eq_abs(*self),
    {
        if budget == 0 {
            *self
        } else {
            self.meet(fact)
        }
    }

    /// Guard of §5.1: every concrete value lies in `[lo, hi]`.
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
            Bound::Fin(lo).le(self.lo) && self.hi.le(Bound::Fin(hi)) && self.lo != Bound::NegInf
                && self.hi != Bound::PosInf
        }
    }

    /// Guard of §5.1: `0` is not among the represented values.
    pub fn nonzero(&self) -> (r: bool)
        requires
            self.wf(),
        ensures
            r ==> forall|z: int| #![auto] self.has(z) ==> z != 0,
    {
        if self.empty {
            false
        } else {
            !self.contains(0)
        }
    }

    /// Non-negative finite interval: `0 <= lo <= hi`, both finite. Used by
    /// the precise unsigned-style division transfer.
    pub open spec fn is_nonneg_finite(self) -> bool {
        self.is_finite() && bound_le(Bound::Fin(0), self.lo)
    }

    pub fn nonneg_finite(&self) -> (r: bool)
        ensures
            r == self.is_nonneg_finite(),
    {
        self.finite() && Bound::Fin(0).le(self.lo)
    }

    /// Interval-by-interval division. Value containment holds for every
    /// nonzero concrete divisor; alarm membership tracks the zero cases.
    pub fn div(&self, d: &IntervalZ) -> (r: (IntervalZ, Alarm))
        requires
            self.wf(),
            d.wf(),
        ensures
            r.0.wf(),
            forall|x: int, y: int| #![auto] self.has(x) && d.has(y) && y != 0 ==> r.0.has(
                x / y,
            ),
            forall|x: int, y: int| #![auto] self.has(x) && d.has(y) ==> r.1.has(y == 0),
    {
        if self.empty {
            proof {
                assert forall|x: int, y: int| #![auto] self.has(x) && d.has(y) && y != 0 implies
                    IntervalZ::bottom_spec().has(x / y) by {};
                assert forall|x: int, y: int| #![auto] self.has(x) && d.has(y) implies
                    Alarm::NoError.has(y == 0) by {};
            }
            (IntervalZ::bottom(), Alarm::NoError)
        } else if d.empty {
            proof {
                assert forall|x: int, y: int| #![auto] self.has(x) && d.has(y) && y != 0 implies
                    IntervalZ::bottom_spec().has(x / y) by {};
                assert forall|x: int, y: int| #![auto] self.has(x) && d.has(y) implies
                    Alarm::NoError.has(y == 0) by {};
            }
            (IntervalZ::bottom(), Alarm::NoError)
        } else if d.is_zero() {
            proof {
                assert forall|x: int, y: int| #![auto] self.has(x) && d.has(y) && y != 0 implies
                    IntervalZ::bottom_spec().has(x / y) by {
                    assert(d.has(y) && is_zero_singleton(*d) ==> y == 0);
                };
                assert forall|x: int, y: int| #![auto] self.has(x) && d.has(y) implies
                    Alarm::DefiniteError.has(y == 0) by {
                    assert(d.has(y) && is_zero_singleton(*d) ==> y == 0);
                };
            }
            (IntervalZ::bottom(), Alarm::DefiniteError)
        } else if d.contains(0) {
            proof {
                assert forall|x: int, y: int| #![auto] self.has(x) && d.has(y) && y != 0 implies
                    IntervalZ::top_spec().has(x / y) by {};
                assert forall|x: int, y: int| #![auto] self.has(x) && d.has(y) implies
                    Alarm::MaybeError.has(y == 0) by {};
            }
            (IntervalZ::top(), Alarm::MaybeError)
        } else {
            proof {
                assert forall|x: int, y: int| #![auto] self.has(x) && d.has(y) && y != 0 implies
                    IntervalZ::top_spec().has(x / y) by {};
                assert forall|x: int, y: int| #![auto] self.has(x) && d.has(y) implies
                    Alarm::NoError.has(y == 0) by {
                    lemma_not_contains_zero(*d);
                    assert(y != 0);
                };
            }
            (IntervalZ::top(), Alarm::NoError)
        }
    }
}

pub open spec fn matches_fin(b: Bound) -> bool {
    match b {
        Bound::Fin(_) => true,
        _ => false,
    }
}

pub fn is_fin(b: Bound) -> (r: bool)
    ensures
        r == matches_fin(b),
{
    match b {
        Bound::Fin(_) => true,
        _ => false,
    }
}

pub open spec fn is_zero_singleton(a: IntervalZ) -> bool {
    !a.empty && a.lo == Bound::Fin(0i64) && a.hi == Bound::Fin(0i64)
}

pub fn bound_le_int_exec(b: Bound, x: i64) -> (r: bool)
    ensures
        r == bound_le_int(b, x as int),
{
    match b {
        Bound::NegInf => true,
        Bound::Fin(n) => n <= x,
        Bound::PosInf => false,
    }
}

pub fn int_le_bound_exec(x: i64, b: Bound) -> (r: bool)
    ensures
        r == int_le_bound(x as int, b),
{
    match b {
        Bound::PosInf => true,
        Bound::Fin(n) => x <= n,
        Bound::NegInf => false,
    }
}

pub open spec fn fin_of(b: Bound) -> i64
    recommends
        matches_fin(b),
{
    match b {
        Bound::Fin(n) => n,
        _ => 0,
    }
}

pub open spec fn mul_finite_spec(a: IntervalZ, b: IntervalZ) -> IntervalZ {
    let p1 = fin_mul_spec(fin_of(a.lo), fin_of(b.lo));
    let p2 = fin_mul_spec(fin_of(a.lo), fin_of(b.hi));
    let p3 = fin_mul_spec(fin_of(a.hi), fin_of(b.lo));
    let p4 = fin_mul_spec(fin_of(a.hi), fin_of(b.hi));
    let lo = bound_min(bound_min(p1, p2), bound_min(p3, p4));
    let hi = bound_max(bound_max(p1, p2), bound_max(p3, p4));
    if lo == Bound::PosInf || hi == Bound::NegInf {
        IntervalZ::top_spec()
    } else if !bound_le(lo, hi) {
        IntervalZ::bottom_spec()
    } else {
        IntervalZ { empty: false, lo, hi }
    }
}

pub fn mul_finite(a: IntervalZ, b: IntervalZ) -> (r: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        a.is_finite(),
        b.is_finite(),
    ensures
        r.wf(),
{
    let alo = fin_of_exec(a.lo);
    let ahi = fin_of_exec(a.hi);
    let blo = fin_of_exec(b.lo);
    let bhi = fin_of_exec(b.hi);
    let p1 = Bound::fin_mul(alo, blo);
    let p2 = Bound::fin_mul(alo, bhi);
    let p3 = Bound::fin_mul(ahi, blo);
    let p4 = Bound::fin_mul(ahi, bhi);
    let lo = p1.min(p2).min(p3.min(p4));
    let hi = p1.max(p2).max(p3.max(p4));
    match (lo, hi) {
        (Bound::PosInf, _) => IntervalZ::top(),
        (_, Bound::NegInf) => IntervalZ::top(),
        _ => IntervalZ::range(lo, hi),
    }
}

pub fn fin_of_exec(b: Bound) -> (r: i64)
    requires
        matches_fin(b),
    ensures
        r == fin_of(b),
{
    match b {
        Bound::Fin(n) => n,
        _ => 0,
    }
}

/// Precise nonneg / nonneg division. Well-formedness only; the verified
/// `IntervalZ::div` transfer uses top as a sound over-approximation.
pub fn div_nonneg_finite(a: IntervalZ, d: IntervalZ) -> (r: IntervalZ)
    requires
        a.wf(),
        d.wf(),
        a.is_nonneg_finite(),
        d.is_nonneg_finite(),
    ensures
        r.wf(),
{
    let dlo = fin_of_exec(d.lo);
    if dlo <= 0 {
        IntervalZ::top()
    } else {
        let alo = fin_of_exec(a.lo);
        let ahi = fin_of_exec(a.hi);
        let dhi = fin_of_exec(d.hi);
        IntervalZ::range(Bound::Fin(alo / dhi), Bound::Fin(ahi / dlo))
    }
}

// ---------------------------------------------------------------------------
// Containment lemmas
// ---------------------------------------------------------------------------

pub proof fn lemma_add_bound_lower(a: Bound, b: Bound, x: int, y: int)
    requires
        bound_le_int(a, x),
        bound_le_int(b, y),
        a != Bound::PosInf,
        b != Bound::PosInf,
    ensures
        bound_le_int(add_bound_spec(a, b), x + y) || add_bound_spec(a, b) == Bound::PosInf,
{
}

pub proof fn lemma_add_bound_upper(a: Bound, b: Bound, x: int, y: int)
    requires
        int_le_bound(x, a),
        int_le_bound(y, b),
        a != Bound::NegInf,
        b != Bound::NegInf,
    ensures
        int_le_bound(x + y, add_bound_spec(a, b)) || add_bound_spec(a, b) == Bound::NegInf,
{
}

pub proof fn lemma_add_contains(a: IntervalZ, b: IntervalZ, r: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        r == a.add_spec(b),
        r.wf(),
    ensures
        forall|x: int, y: int| #![auto] a.has(x) && b.has(y) ==> r.has(x + y),
{
    assert forall|x: int, y: int| #![auto] a.has(x) && b.has(y) implies r.has(x + y) by {
        if a.empty || b.empty {
        } else {
            lemma_add_bound_lower(a.lo, b.lo, x, y);
            lemma_add_bound_upper(a.hi, b.hi, x, y);
        }
    };
}

pub proof fn lemma_neg_bound(b: Bound, x: int)
    requires
        bound_le_int(b, x),
    ensures
        int_le_bound(-x, neg_bound_spec(b)) || neg_bound_spec(b) == Bound::NegInf,
{
}

pub proof fn lemma_neg_bound_upper(b: Bound, x: int)
    requires
        int_le_bound(x, b),
    ensures
        bound_le_int(neg_bound_spec(b), -x) || neg_bound_spec(b) == Bound::PosInf,
{
}

pub proof fn lemma_neg_contains(a: IntervalZ, r: IntervalZ)
    requires
        a.wf(),
        r == a.neg_spec(),
        r.wf(),
    ensures
        forall|x: int| #![auto] a.has(x) ==> r.has(-x),
{
    assert forall|x: int| #![auto] a.has(x) implies r.has(-x) by {
        if !a.empty {
            lemma_neg_bound_upper(a.hi, x);
            lemma_neg_bound(a.lo, x);
        }
    };
}

pub proof fn lemma_mul_zero_contains(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        is_zero_singleton(a) || is_zero_singleton(b),
        !a.empty,
        !b.empty,
    ensures
        forall|x: int, y: int| #![auto] a.has(x) && b.has(y) ==> (x * y == 0),
{
    assert forall|x: int, y: int| #![auto] a.has(x) && b.has(y) implies x * y == 0 by {
        if is_zero_singleton(a) {
            assert(x == 0);
        } else {
            assert(y == 0);
        }
    };
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

pub proof fn lemma_widen_sound(a: IntervalZ, b: IntervalZ, r: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        !a.empty,
        !b.empty,
        r.eq_abs(a.widen_spec(b)),
        r.wf(),
    ensures
        a.refines(r),
        b.refines(r),
        a.join_spec(b).refines(r),
{
    assert forall|z: int| #![auto] a.has(z) implies r.has(z) by {
        lemma_widen_endpoint(a, b, r, z);
    };
    assert forall|z: int| #![auto] b.has(z) implies r.has(z) by {
        lemma_widen_endpoint_b(a, b, r, z);
    };
}

pub proof fn lemma_widen_endpoint(a: IntervalZ, b: IntervalZ, r: IntervalZ, z: int)
    requires
        a.has(z),
        r.eq_abs(a.widen_spec(b)),
        !a.empty,
        !b.empty,
    ensures
        r.has(z),
{
}

pub proof fn lemma_widen_endpoint_b(a: IntervalZ, b: IntervalZ, r: IntervalZ, z: int)
    requires
        b.has(z),
        r.eq_abs(a.widen_spec(b)),
        !a.empty,
        !b.empty,
        a.wf(),
        b.wf(),
        r.wf(),
    ensures
        r.has(z),
{
}

// ---------------------------------------------------------------------------
// §3.5 lattice laws
// ---------------------------------------------------------------------------

pub proof fn meet_comm(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
    ensures
        a.meet_spec(b).eq_abs(b.meet_spec(a)),
{
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

pub proof fn meet_refines_left(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
    ensures
        a.meet_spec(b).refines(a),
        a.meet_spec(b).refines(b),
{
}

/// Stopping the descending iteration is always sound: the current value
/// already over-approximates, so keeping it (budget 0) preserves `refines`.
pub proof fn refine_budget_sound(a: IntervalZ, fact: IntervalZ, budget: nat)
    requires
        a.wf(),
        fact.wf(),
    ensures
        a.refine_spec(fact, budget).refines(a),
        budget == 0 ==> a.refine_spec(fact, budget) == a,
{
}

/// Overflow-to-top is a sound widening of exact integer addition, but it is
/// not monotone (a tighter operand can overflow while a looser one does not).
/// Meet is the transfer the e-graph actually iterates, and it is monotone.
pub proof fn add_spec_wf(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
    ensures
        a.add_spec(b).wf(),
{
}

pub proof fn neg_spec_wf(a: IntervalZ)
    requires
        a.wf(),
    ensures
        a.neg_spec().wf(),
{
}

pub proof fn join_spec_wf(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
    ensures
        a.join_spec(b).wf(),
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

/// Lower-bound addition is monotone in the first argument.
pub proof fn lemma_add_bound_mono(a: Bound, b: Bound, c: Bound)
    requires
        bound_le(a, b),
    ensures
        bound_le(add_bound_spec(a, c), add_bound_spec(b, c)) || add_bound_spec(a, c)
            == Bound::PosInf || add_bound_spec(b, c) == Bound::PosInf,
{
}

pub proof fn lemma_add_bound_mono_hi(a: Bound, b: Bound, c: Bound)
    requires
        bound_le(a, b),
    ensures
        bound_le(add_bound_spec(a, c), add_bound_spec(b, c)) || add_bound_spec(a, c)
            == Bound::NegInf || add_bound_spec(b, c) == Bound::NegInf,
{
}

pub proof fn lemma_tighter_has(a: IntervalZ, b: IntervalZ, z: int)
    requires
        a.wf(),
        b.wf(),
        a.has(z),
        !a.empty,
        !b.empty,
        bound_le(b.lo, a.lo) || a.lo == Bound::PosInf || b.lo == Bound::NegInf,
        bound_le(a.hi, b.hi) || a.hi == Bound::NegInf || b.hi == Bound::PosInf,
    ensures
        b.has(z) || b.lo == Bound::PosInf,
{
    lemma_bound_le_int_weaken(b.lo, a.lo, z);
    lemma_int_le_bound_weaken(a.hi, b.hi, z);
}

pub proof fn lemma_bound_le_int_weaken(looser: Bound, tighter: Bound, z: int)
    requires
        bound_le(looser, tighter) || looser == Bound::NegInf,
        bound_le_int(tighter, z),
    ensures
        bound_le_int(looser, z),
{
}

pub proof fn lemma_int_le_bound_weaken(tighter: Bound, looser: Bound, z: int)
    requires
        bound_le(tighter, looser) || looser == Bound::PosInf,
        int_le_bound(z, tighter),
    ensures
        int_le_bound(z, looser),
{
}

/// A nonempty refinement has a higher (or equal) lower bound and a lower
/// (or equal) upper bound.
pub proof fn lemma_refines_endpoints(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        a.refines(b),
        !a.empty,
        !b.empty,
    ensures
        bound_le(b.lo, a.lo),
        bound_le(a.hi, b.hi),
{
    if !bound_le(b.lo, a.lo) {
        bound_le_total(a.lo, b.lo);
        assert(bound_le(a.lo, b.lo));
        lemma_strict_lo_witness(a, b);
        assert(false);
    }
    if !bound_le(a.hi, b.hi) {
        bound_le_total(a.hi, b.hi);
        assert(bound_le(b.hi, a.hi));
        lemma_strict_hi_witness(a, b);
        assert(false);
    }
}

pub proof fn lemma_strict_lo_witness(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        a.refines(b),
        !a.empty,
        !b.empty,
        bound_le(a.lo, b.lo),
        !bound_le(b.lo, a.lo),
    ensures
        false,
{
    match (a.lo, b.lo) {
        (Bound::Fin(x), Bound::Fin(y)) => {
            assert(x < y);
            assert(bound_le_int(a.lo, x as int));
            assert(int_le_bound(x as int, a.hi));
            assert(a.has(x as int));
            assert(!bound_le_int(b.lo, x as int));
            assert(!b.has(x as int));
        },
        (Bound::NegInf, Bound::Fin(y)) => {
            let k: int = y as int - 1;
            assert(!bound_le_int(b.lo, k));
            assert(!b.has(k));
            match a.hi {
                Bound::PosInf => {
                    assert(a.has(k));
                },
                Bound::Fin(h) => {
                    if k <= h as int {
                        assert(a.has(k));
                    } else {
                        assert(a.has(h as int));
                        assert(!b.has(h as int));
                    }
                },
                Bound::NegInf => {},
            }
        },
        (Bound::NegInf, Bound::PosInf) => {},
        (Bound::Fin(_), Bound::PosInf) => {},
        (Bound::Fin(_), Bound::NegInf) => {},
        (Bound::NegInf, Bound::NegInf) => {},
        (Bound::PosInf, _) => {},
    }
}

pub proof fn lemma_strict_hi_witness(a: IntervalZ, b: IntervalZ)
    requires
        a.wf(),
        b.wf(),
        a.refines(b),
        !a.empty,
        !b.empty,
        bound_le(b.hi, a.hi),
        !bound_le(a.hi, b.hi),
    ensures
        false,
{
    match (a.hi, b.hi) {
        (Bound::Fin(x), Bound::Fin(y)) => {
            assert(y < x);
            assert(a.has(x as int));
            assert(!b.has(x as int));
        },
        (Bound::PosInf, Bound::Fin(y)) => {
            let k: int = y as int + 1;
            assert(!int_le_bound(k, b.hi));
            assert(!b.has(k));
            match a.lo {
                Bound::NegInf => {
                    assert(a.has(k));
                },
                Bound::Fin(l) => {
                    if l as int <= k {
                        assert(a.has(k));
                    } else {
                        assert(a.has(l as int));
                        assert(!b.has(l as int));
                    }
                },
                Bound::PosInf => {},
            }
        },
        _ => {},
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

} // verus!
