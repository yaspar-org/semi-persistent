// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Forward transfer functions, indexed by a concrete semantics.
//!
//! `Arith<S>` and `DivRem<S>` state soundness against `S`'s operators: every
//! concrete result of operands drawn from the arguments' concretizations is in
//! the concretization of the abstract result. A domain implements a transfer
//! trait once per semantics it supports (for example both `DivRem<Unsigned<W>>`
//! and `DivRem<Signed<W>>` on one `Interval<W>`).
use crate::lattice::*;
use crate::semantics::*;
use vstd::prelude::*;

verus! {

pub trait Arith<S: Semantics>: Domain<C = S::V> {
    fn add(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|x: S::V, y: S::V|
                self.gamma(x) && o.gamma(y) ==> #[trigger] r.gamma(S::add(x, y)),
    ;

    fn sub(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|x: S::V, y: S::V|
                self.gamma(x) && o.gamma(y) ==> #[trigger] r.gamma(S::sub(x, y)),
    ;

    fn neg(&self) -> (r: Self)
        requires
            self.wf(),
        ensures
            r.wf(),
            forall|x: S::V| self.gamma(x) ==> #[trigger] r.gamma(S::neg(x)),
    ;
}

/// Whether a division may divide by zero.
pub enum DivZero {
    /// No divisor in the concretization is zero.
    Never,
    /// Some divisor may be zero.
    Maybe,
    /// Every divisor is zero; the quotient is `Bot`.
    Always,
}

pub trait DivRem<S: Semantics>: Domain<C = S::V> {
    fn contains_zero(&self) -> (b: bool)
        requires
            self.wf(),
        ensures
            b == self.gamma(S::zero()),
    ;

    /// The quotient over the nonzero divisors, and the division-by-zero flag.
    fn div(&self, d: &Self) -> (r: (BotOr<Self>, DivZero))
        requires
            self.wf(),
            d.wf(),
        ensures
            r.0.wf(),
            forall|x: S::V, y: S::V|
                self.gamma(x) && d.gamma(y) && !S::is_zero(y) ==> #[trigger] r.0.gamma(S::div(x, y)),
            r.1 is Never ==> !d.gamma(S::zero()),
            r.1 is Always ==> forall|y: S::V| #[trigger] d.gamma(y) ==> S::is_zero(y),
            (r.0 is Bot) <==> (r.1 is Always),
    ;

    /// The remainder over the nonzero divisors, and the division-by-zero flag.
    fn rem(&self, d: &Self) -> (r: (BotOr<Self>, DivZero))
        requires
            self.wf(),
            d.wf(),
        ensures
            r.0.wf(),
            forall|x: S::V, y: S::V|
                self.gamma(x) && d.gamma(y) && !S::is_zero(y) ==> #[trigger] r.0.gamma(S::rem(x, y)),
            r.1 is Never ==> !d.gamma(S::zero()),
            r.1 is Always ==> forall|y: S::V| #[trigger] d.gamma(y) ==> S::is_zero(y),
            (r.0 is Bot) <==> (r.1 is Always),
    ;
}

} // verus!
