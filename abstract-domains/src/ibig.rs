// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Executable unbounded integer (`IBig`), the engine's bignum literal group.
//!
//! The payload is `num_bigint::BigInt`. Verus cannot see inside that crate, so
//! the struct is `external_body` and the spec view is mathematical `int`.
//! Arithmetic is the unbounded ring: nothing wraps.
//!
//! `div_euclid` is Euclidean division with a nonnegative remainder, matching
//! Verus `int` `/` and Rust `div_euclid` (not truncating `/`).
//!
//! Trust: `from_int` / `view` are a bijection (two broadcast axioms), and each
//! `external_body` ensures clause.

use num_bigint::{BigInt, Sign};
use vstd::prelude::*;

/// Euclidean quotient: `a = b * q + r` with `0 <= r < |b|`.
fn euclid_quot(a: &BigInt, b: &BigInt) -> BigInt {
    let q = a / b;
    let r = a % b;
    if r.sign() == Sign::Minus {
        if b.sign() == Sign::Minus { q + 1 } else { q - 1 }
    } else {
        q
    }
}

verus! {

/// Unbounded integer. Spec view is `int`; exec payload is `BigInt`.
#[verifier::external_body]
pub struct IBig {
    inner: BigInt,
}

impl IBig {
    /// Spec constructor: the unique `IBig` whose view is `n`.
    pub uninterp spec fn from_int(n: int) -> IBig;

    /// Mathematical value of this integer.
    pub uninterp spec fn view(&self) -> int;

    #[verifier::external_body]
    pub fn from_i64(n: i64) -> (r: IBig)
        ensures
            r.view() == n as int,
            r == IBig::from_int(n as int),
    {
        IBig { inner: BigInt::from(n) }
    }

    #[verifier::external_body]
    pub fn clone_ibig(&self) -> (r: IBig)
        ensures
            r == *self,
            r.view() == self.view(),
    {
        IBig { inner: self.inner.clone() }
    }

    #[verifier::external_body]
    pub fn zero() -> (r: IBig)
        ensures
            r.view() == 0,
            r == IBig::from_int(0),
    {
        IBig { inner: BigInt::from(0) }
    }

    #[verifier::external_body]
    pub fn add(&self, rhs: &IBig) -> (r: IBig)
        ensures
            r.view() == self.view() + rhs.view(),
            r == IBig::from_int(self.view() + rhs.view()),
    {
        IBig { inner: &self.inner + &rhs.inner }
    }

    #[verifier::external_body]
    pub fn mul(&self, rhs: &IBig) -> (r: IBig)
        ensures
            r.view() == self.view() * rhs.view(),
            r == IBig::from_int(self.view() * rhs.view()),
    {
        IBig { inner: &self.inner * &rhs.inner }
    }

    #[verifier::external_body]
    pub fn neg(&self) -> (r: IBig)
        ensures
            r.view() == -self.view(),
            r == IBig::from_int(-self.view()),
    {
        IBig { inner: -&self.inner }
    }

    /// Euclidean quotient. Spec is Verus `int` `/`, not truncating division.
    #[verifier::external_body]
    pub fn div_euclid(&self, rhs: &IBig) -> (r: IBig)
        requires
            rhs.view() != 0,
        ensures
            r.view() == self.view() / rhs.view(),
            r == IBig::from_int(self.view() / rhs.view()),
    {
        IBig { inner: euclid_quot(&self.inner, &rhs.inner) }
    }

    #[verifier::external_body]
    pub fn le(&self, rhs: &IBig) -> (r: bool)
        ensures
            r == (self.view() <= rhs.view()),
    {
        self.inner <= rhs.inner
    }

    #[verifier::external_body]
    pub fn lt(&self, rhs: &IBig) -> (r: bool)
        ensures
            r == (self.view() < rhs.view()),
    {
        self.inner < rhs.inner
    }

    #[verifier::external_body]
    pub fn eq_int(&self, rhs: &IBig) -> (r: bool)
        ensures
            r == (self.view() == rhs.view()),
    {
        self.inner == rhs.inner
    }

    #[verifier::external_body]
    pub fn is_zero(&self) -> (r: bool)
        ensures
            r == (self.view() == 0),
    {
        self.inner.sign() == Sign::NoSign
    }

    #[verifier::external_body]
    pub fn is_neg(&self) -> (r: bool)
        ensures
            r == (self.view() < 0),
    {
        self.inner.sign() == Sign::Minus
    }

    #[verifier::external_body]
    pub fn is_pos(&self) -> (r: bool)
        ensures
            r == (self.view() > 0),
    {
        self.inner.sign() == Sign::Plus
    }
}

/// `from_int` really returns an integer whose view is `n`.
pub broadcast axiom fn axiom_ibig_from_int_view(n: int)
    ensures
        #[trigger] IBig::from_int(n).view() == n,
;

/// Every executable `IBig` is the `from_int` of its view (canonical).
pub broadcast axiom fn axiom_ibig_view_surj(a: IBig)
    ensures
        a == #[trigger] IBig::from_int(a.view()),
;

pub broadcast group group_ibig_axioms {
    axiom_ibig_from_int_view,
    axiom_ibig_view_surj,
}

} // verus!

impl Clone for IBig {
    fn clone(&self) -> Self {
        IBig { inner: self.inner.clone() }
    }
}

impl PartialEq for IBig {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl Eq for IBig {}

impl core::fmt::Debug for IBig {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.inner)
    }
}
