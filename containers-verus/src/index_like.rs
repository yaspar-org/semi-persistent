// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `IndexLike`: the bijection-to-`[0, max_nat)` contract.
//!
//! Every index type provides a spec function `as_nat: Self -> nat` together
//! with a bound `max_nat` and proofs that:
//!   - `as_nat` is injective
//!   - `as_nat(self) < max_nat()`
//!   - `try_from_usize` is the inverse of `as_usize` on `[0, max_nat)`
//!   - `min_spec()` projects to 0; `max_spec()` is the largest representable.
//!
//! Production-side parity:
//!   - `MIN`/`MAX` constants exposed via spec + exec method pairs.
//!   - Total ordering via `lt_spec`/`le_spec`. Exec comparison is provided
//!     for primitives via `as_usize` round-trip.
//!
//! The diff log stores `(T, I)` pairs; `IndexLike` keeps the index narrow so
//! diff entries stay compact.

use vstd::prelude::*;

verus! {

/// Bijection between an exec index type and `nat`.
pub trait IndexLike: Sized + Copy {
    // -- ghost projections ---------------------------------------------------

    /// Ghost projection to a natural number. Injective and bounded.
    spec fn as_nat(self) -> nat;

    /// Upper bound for `as_nat`. Concrete value depends on the bit width
    /// (e.g., `0x1_0000_0000` for `u32`, `0x8000_0000` for a 31-bit DenseId).
    spec fn max_nat() -> nat;

    /// Ghost zero (`I::MIN` in production).
    spec fn min_spec() -> Self;

    /// Ghost max (`I::MAX` in production). `min_spec()` projects to 0;
    /// `max_spec()` projects to `max_nat() - 1`.
    spec fn max_spec() -> Self;

    /// Total ordering on the projected nats. Implementors get this for free
    /// once `as_nat` is defined; we expose it as a spec so callers don't have
    /// to reach for `as_nat` everywhere.
    open spec fn lt_spec(self, other: Self) -> bool {
        self.as_nat() < other.as_nat()
    }

    open spec fn le_spec(self, other: Self) -> bool {
        self.as_nat() <= other.as_nat()
    }

    // -- proof obligations ---------------------------------------------------

    /// Every value of `Self` projects to a nat strictly below `max_nat()`.
    ///
    /// `tracked self`: a type whose bound is a `#[verifier::type_invariant]`
    /// (e.g. `DenseId31`, MSB-clear ⟹ `< 2^31`) needs `use_type_invariant` to
    /// discharge this, which requires a tracked/exec receiver. Primitive impls,
    /// whose bound is structural, ignore the receiver and keep an empty body.
    proof fn lemma_as_nat_bounded(tracked self)
        ensures self.as_nat() < Self::max_nat();

    /// `as_nat` is injective: distinct values project to distinct nats.
    proof fn lemma_as_nat_injective(a: Self, b: Self)
        requires a.as_nat() == b.as_nat()
        ensures a == b;

    /// `min_spec()` projects to 0.
    proof fn lemma_min_as_nat()
        ensures Self::min_spec().as_nat() == 0;

    /// `max_nat()` is positive (there is at least one representable index).
    /// A receiver-free companion to `lemma_as_nat_bounded`: callers that only
    /// need `0 < max_nat()` (e.g. to show an empty store is `wf`) use this
    /// rather than instantiating the bound at a value, which `lemma_as_nat_
    /// bounded`'s `tracked self` no longer permits on a spec-built `min_spec()`.
    proof fn lemma_max_nat_positive()
        ensures 0 < Self::max_nat();

    /// `max_spec()` projects to `max_nat() - 1` (the maximum representable).
    proof fn lemma_max_as_nat()
        ensures Self::max_spec().as_nat() == (Self::max_nat() - 1) as nat;

    // -- exec API ------------------------------------------------------------

    /// Exec: zero / minimum value.
    fn min() -> (r: Self)
        ensures r == Self::min_spec();

    /// Exec: maximum value.
    fn max() -> (r: Self)
        ensures r == Self::max_spec();

    /// Exec: project to `usize`. Equal to `as_nat()` viewed as `usize`.
    fn as_usize(self) -> (r: usize)
        ensures r as nat == self.as_nat();

    /// Exec: try to construct from a `usize`. Succeeds iff `n < max_nat()`.
    fn try_from_usize(n: usize) -> (r: Option<Self>)
        ensures
            r is Some ==> r->Some_0.as_nat() == n as nat,
            r is Some <==> (n as nat) < Self::max_nat();

    /// Exec: less-than. Implemented via `as_usize` round-trip on primitives.
    fn lt(self, other: Self) -> (r: bool)
        ensures r == self.lt_spec(other);

    /// Exec: less-than-or-equal.
    fn le(self, other: Self) -> (r: bool)
        ensures r == self.le_spec(other);
}

// ---------------------------------------------------------------------------
// Concrete impls for primitive integers.
//
// Bodies that involve `try_into` or wrapping casts are `external_body`; the
// arithmetic isn't always discharged through std's conversion machinery.
// All such casts are guarded so the contract holds on the host architecture
// (see u64 below). 32-bit hosts running a 64-bit index would observe a
// narrowing cast in `as_usize`; we forbid that by feature-gating.
// ---------------------------------------------------------------------------

impl IndexLike for u8 {
    open spec fn as_nat(self) -> nat { self as nat }
    open spec fn max_nat() -> nat { 0x100 }
    open spec fn min_spec() -> Self { 0u8 }
    open spec fn max_spec() -> Self { u8::MAX }

    proof fn lemma_as_nat_bounded(tracked self) {}
    proof fn lemma_as_nat_injective(a: Self, b: Self) {}
    proof fn lemma_min_as_nat() {}
    proof fn lemma_max_nat_positive() {}
    proof fn lemma_max_as_nat() {}

    fn min() -> Self { 0u8 }
    fn max() -> Self { u8::MAX }

    #[verifier::external_body]
    fn as_usize(self) -> usize { self as usize }

    #[verifier::external_body]
    fn try_from_usize(n: usize) -> Option<Self> {
        if n <= u8::MAX as usize { Some(n as u8) } else { None }
    }

    fn lt(self, other: Self) -> bool { self < other }
    fn le(self, other: Self) -> bool { self <= other }
}

impl IndexLike for u16 {
    open spec fn as_nat(self) -> nat { self as nat }
    open spec fn max_nat() -> nat { 0x10000 }
    open spec fn min_spec() -> Self { 0u16 }
    open spec fn max_spec() -> Self { u16::MAX }

    proof fn lemma_as_nat_bounded(tracked self) {}
    proof fn lemma_as_nat_injective(a: Self, b: Self) {}
    proof fn lemma_min_as_nat() {}
    proof fn lemma_max_nat_positive() {}
    proof fn lemma_max_as_nat() {}

    fn min() -> Self { 0u16 }
    fn max() -> Self { u16::MAX }

    #[verifier::external_body]
    fn as_usize(self) -> usize { self as usize }

    #[verifier::external_body]
    fn try_from_usize(n: usize) -> Option<Self> {
        if n <= u16::MAX as usize { Some(n as u16) } else { None }
    }

    fn lt(self, other: Self) -> bool { self < other }
    fn le(self, other: Self) -> bool { self <= other }
}

impl IndexLike for u32 {
    open spec fn as_nat(self) -> nat { self as nat }
    open spec fn max_nat() -> nat { 0x1_0000_0000 }
    open spec fn min_spec() -> Self { 0u32 }
    open spec fn max_spec() -> Self { u32::MAX }

    proof fn lemma_as_nat_bounded(tracked self) {}
    proof fn lemma_as_nat_injective(a: Self, b: Self) {}
    proof fn lemma_min_as_nat() {}
    proof fn lemma_max_nat_positive() {}
    proof fn lemma_max_as_nat() {}

    fn min() -> Self { 0u32 }
    fn max() -> Self { u32::MAX }

    #[verifier::external_body]
    fn as_usize(self) -> usize { self as usize }

    #[verifier::external_body]
    fn try_from_usize(n: usize) -> Option<Self> {
        if (n as u64) <= u32::MAX as u64 { Some(n as u32) } else { None }
    }

    fn lt(self, other: Self) -> bool { self < other }
    fn le(self, other: Self) -> bool { self <= other }
}

// `u64` as an IndexLike requires a 64-bit host: `as_usize` would narrow on
// 32-bit. Production has the same implicit assumption (the e-graph runs on
// 64-bit machines). We make it explicit here.
#[cfg(target_pointer_width = "64")]
impl IndexLike for u64 {
    open spec fn as_nat(self) -> nat { self as nat }
    open spec fn max_nat() -> nat { 0x1_0000_0000_0000_0000 }
    open spec fn min_spec() -> Self { 0u64 }
    open spec fn max_spec() -> Self { u64::MAX }

    proof fn lemma_as_nat_bounded(tracked self) {}
    proof fn lemma_as_nat_injective(a: Self, b: Self) {}
    proof fn lemma_min_as_nat() {}
    proof fn lemma_max_nat_positive() {}
    proof fn lemma_max_as_nat() {}

    fn min() -> Self { 0u64 }
    fn max() -> Self { u64::MAX }

    #[verifier::external_body]
    fn as_usize(self) -> usize { self as usize }

    #[verifier::external_body]
    fn try_from_usize(n: usize) -> Option<Self> { Some(n as u64) }

    fn lt(self, other: Self) -> bool { self < other }
    fn le(self, other: Self) -> bool { self <= other }
}

impl IndexLike for usize {
    open spec fn as_nat(self) -> nat { self as nat }
    open spec fn max_nat() -> nat { usize::MAX as nat + 1 }
    open spec fn min_spec() -> Self { 0usize }
    open spec fn max_spec() -> Self { usize::MAX }

    proof fn lemma_as_nat_bounded(tracked self) {}
    proof fn lemma_as_nat_injective(a: Self, b: Self) {}
    proof fn lemma_min_as_nat() {}
    proof fn lemma_max_nat_positive() {}
    proof fn lemma_max_as_nat() {}

    fn min() -> Self { 0usize }
    fn max() -> Self { usize::MAX }

    fn as_usize(self) -> usize { self }
    fn try_from_usize(n: usize) -> Option<Self> { Some(n) }

    fn lt(self, other: Self) -> bool { self < other }
    fn le(self, other: Self) -> bool { self <= other }
}

} // verus!
