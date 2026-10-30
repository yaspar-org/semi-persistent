// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Forward transfer functions, indexed by a concrete semantics.
//!
//! `Arith<S>`, `Mul<S>` and `DivRem<S>` state soundness against `S`'s operators: every
//! concrete result of operands drawn from the arguments' concretizations is in
//! the concretization of the abstract result. A domain implements a transfer
//! trait once per semantics it supports (for example both `DivRem<Unsigned<W>>`
//! and `DivRem<Signed<W>>` on one `Interval<W>`).
//!
//! `Compare<S>` answers comparisons with a `Bool4` and refines operands from a
//! known comparison result. Its signature is shared by every sort; change it
//! only after review (doc/reduced-product.md, "Coordination").
use crate::bool4::*;
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

pub trait Mul<S: Semantics>: Domain<C = S::V> {
    fn mul(&self, o: &Self) -> (r: Self)
        requires
            self.wf(),
            o.wf(),
        ensures
            r.wf(),
            forall|x: S::V, y: S::V|
                self.gamma(x) && o.gamma(y) ==> #[trigger] r.gamma(S::mul(x, y)),
    ;
}

// TODO(abs-domain-registry): add backward transfers for Arith, Mul and DivRem (refine operands from a result value, never growing them); none exist, see abstract-domains/doc/future/registry-task.md §4
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

// TODO(abs-domain-registry): add the Bitwise, Shift<S> and Cast traits (doc/domain-traits.md §5); the registry's bv operators name them, see abstract-domains/doc/future/registry-task.md §4
/// Comparisons. Forward: the possible truth values of `x op y`. Backward
/// (`assume_*`): both operands refined by `(x op y) == t`, keeping every pair
/// that satisfies it and never growing an operand.
pub trait Compare<S: Semantics>: Domain<C = S::V> {
    /// `x < y`.
    fn lt(&self, o: &Self) -> (r: Bool4)
        requires
            self.wf(),
            o.wf(),
        ensures
            forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) ==> r.gamma(S::lt(x, y)),
    ;

    /// `x <= y`.
    fn le(&self, o: &Self) -> (r: Bool4)
        requires
            self.wf(),
            o.wf(),
        ensures
            forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) ==> r.gamma(S::le(x, y)),
    ;

    /// `x == y`.
    fn eq(&self, o: &Self) -> (r: Bool4)
        requires
            self.wf(),
            o.wf(),
        ensures
            forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) ==> r.gamma(x == y),
    ;

    /// Refines by `(x < y) == t`.
    fn assume_lt(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>))
        requires
            self.wf(),
            o.wf(),
        ensures
            r.0.wf(),
            r.1.wf(),
            forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) && S::lt(x, y) == t ==> r.0.gamma(x) && r.1.gamma(y),
            forall|x: S::V| #[trigger] r.0.gamma(x) ==> self.gamma(x),
            forall|y: S::V| #[trigger] r.1.gamma(y) ==> o.gamma(y),
    ;

    /// Refines by `(x <= y) == t`.
    fn assume_le(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>))
        requires
            self.wf(),
            o.wf(),
        ensures
            r.0.wf(),
            r.1.wf(),
            forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) && S::le(x, y) == t ==> r.0.gamma(x) && r.1.gamma(y),
            forall|x: S::V| #[trigger] r.0.gamma(x) ==> self.gamma(x),
            forall|y: S::V| #[trigger] r.1.gamma(y) ==> o.gamma(y),
    ;

    /// Refines by `(x == y) == t`.
    fn assume_eq(&self, o: &Self, t: bool) -> (r: (BotOr<Self>, BotOr<Self>))
        requires
            self.wf(),
            o.wf(),
        ensures
            r.0.wf(),
            r.1.wf(),
            forall|x: S::V, y: S::V|
                #![trigger self.gamma(x), o.gamma(y)]
                self.gamma(x) && o.gamma(y) && (x == y) == t ==> r.0.gamma(x) && r.1.gamma(y),
            forall|x: S::V| #[trigger] r.0.gamma(x) ==> self.gamma(x),
            forall|y: S::V| #[trigger] r.1.gamma(y) ==> o.gamma(y),
    ;
}

} // verus!
