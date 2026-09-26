// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Unbounded integers for unbounded domains: a thin trusted wrapper over
//! `num_bigint::BigInt`.
//!
//! TRUST BOUNDARY. Every `external_body` function below is trusted to meet its
//! contract, and `axiom_view_injective` is an axiom. The ledger is in
//! doc/domain-traits.md §Trust. Machine-integer domains never use this type.
use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub struct IBig {
    inner: num_bigint::BigInt,
}

impl IBig {
    /// The mathematical integer.
    pub uninterp spec fn view(&self) -> int;

    /// TRUSTED. `BigInt` keeps a normalized sign-magnitude form (no leading
    /// zero limbs, zero has sign `NoSign`), and `view` is the only spec
    /// observer of an `IBig`, so equal integers are equal spec values.
    pub axiom fn axiom_view_injective(a: &IBig, b: &IBig)
        ensures
            a.view() == b.view() ==> *a == *b,
    ;

    #[verifier::external_body]
    pub fn from_i64(v: i64) -> (r: IBig)
        ensures
            r.view() == v as int,
    {
        IBig { inner: num_bigint::BigInt::from(v) }
    }

    /// `Some` exactly when the value fits in an `i64`.
    #[verifier::external_body]
    pub fn to_i64(&self) -> (r: Option<i64>)
        ensures
            match r {
                Some(v) => v as int == self.view(),
                None => self.view() < i64::MIN || self.view() > i64::MAX,
            },
    {
        num_traits::ToPrimitive::to_i64(&self.inner)
    }

    #[verifier::external_body]
    pub fn dup(&self) -> (r: IBig)
        ensures
            r.view() == self.view(),
    {
        IBig { inner: self.inner.clone() }
    }

    #[verifier::external_body]
    pub fn le(&self, o: &IBig) -> (b: bool)
        ensures
            b == (self.view() <= o.view()),
    {
        self.inner <= o.inner
    }

    #[verifier::external_body]
    pub fn is_zero(&self) -> (b: bool)
        ensures
            b == (self.view() == 0),
    {
        num_traits::Zero::is_zero(&self.inner)
    }

    #[verifier::external_body]
    pub fn add(&self, o: &IBig) -> (r: IBig)
        ensures
            r.view() == self.view() + o.view(),
    {
        IBig { inner: &self.inner + &o.inner }
    }

    #[verifier::external_body]
    pub fn neg(&self) -> (r: IBig)
        ensures
            r.view() == -self.view(),
    {
        IBig { inner: -&self.inner }
    }
}

} // verus!
