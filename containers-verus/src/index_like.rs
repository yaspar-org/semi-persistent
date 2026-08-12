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

// `usize::MAX == u64::MAX` on a 64-bit host. Discharges the `u64 <-> usize`
// casts in the `u64` impl (both are the identity on values when the widths
// match). Relies on the crate-wide `global size_of usize == 8` pin (declared
// once, in bplus_layout.rs; verified against the build `--target`). The whole
// `u64`/`usize` index machinery is already `#[cfg(target_pointer_width = "64")]`,
// so this adds no assumption beyond the existing gate.
/// Mirrors `bplus_layout::lemma_usize_is_u64_wide`.
pub proof fn lemma_u64_usize_64bit()
    ensures usize::MAX as nat == u64::MAX as nat,
{
    vstd::layout::unsigned_int_max_values();
    assert(usize::BITS == 64);
}

/// Bijection between an exec index type and `nat`.
///
/// prod-parity: `Ord + Hash + Debug` match production's `IndexLike`
/// (`containers/src/dense_id.rs:69`, `IndexLike: Copy + Ord + Hash + Debug`).
/// The consumer relies on this transitively — e.g. `EGraphConfig::G: DenseId`
/// (which has `IndexLike` as a supertrait) is then `Debug`/`Ord`/`Hash` without
/// the config restating those bounds, and the caches' `#[derive(Debug)]` and
/// hash-map keying resolve.
pub trait IndexLike: Sized + Copy + core::cmp::Ord + core::hash::Hash + core::fmt::Debug {
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

    /// The index range fits in a `usize`: every representable index is `<= usize::MAX`.
    ///
    /// Implied by `as_usize` (whose return is a `usize` equal to `as_nat()`), but only
    /// *at a value* and only in exec code. Generic proof code needs it as a fact about
    /// the type, without a witness and without a runtime call — which is why this is a
    /// trait obligation rather than something derived at each use.
    ///
    /// What needs it: any `usize` counter whose range is bounded by an `I`-indexed
    /// collection. `ListIter::pos` walks a list whose length is bounded by the node
    /// arena, which is bounded by `N::Index::max_nat()`; `pos + 1` is overflow-free only
    /// once that chain reaches `usize`. Before `ListHead::len` followed the id family,
    /// that last step came free from the count being a literal `u32` (and Verus knows
    /// `usize::MAX >= u32::MAX`). A width-parametric count has no such accident, so the
    /// fact has to be stated — and stating it here means every index type is *checked*
    /// against it rather than assumed to satisfy it.
    ///
    /// Every impl discharges it from the crate-wide `global size_of usize == 8` pin via
    /// `lemma_u64_usize_64bit`; `usize`/`DenseUsize` have it by definition. An index type
    /// wider than a pointer could not implement it, which is the intended outcome —
    /// `as_usize` would narrow.
    proof fn lemma_max_nat_fits_usize()
        ensures Self::max_nat() <= usize::MAX as nat + 1;

    /// `max_spec()` projects to `max_nat() - 1` (the maximum representable).
    proof fn lemma_max_as_nat()
        ensures Self::max_spec().as_nat() == (Self::max_nat() - 1) as nat;

    /// The order `lt_spec`/`le_spec` is exactly the `as_nat` order. Trivially
    /// true from the `open` default bodies at a concrete type, but Verus does
    /// not unfold a default-bodied trait spec method through a generic type
    /// parameter, so generic code (e.g. binary search over `Self`) needs this
    /// lemma to reason about the order via `as_nat` (where transitivity and
    /// totality come for free on `nat`).
    proof fn lemma_order_is_as_nat(a: Self, b: Self)
        ensures
            a.lt_spec(b) == (a.as_nat() < b.as_nat()),
            a.le_spec(b) == (a.as_nat() <= b.as_nat());

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
// Checked index arithmetic.
//
// Production's `IndexLike` carries these as default-bodied trait methods
// (`containers/src/dense_id.rs`). Here they are free functions over `I: IndexLike`
// instead, for one reason: every postcondition below is *derived* from the contract the
// trait already states — `as_usize` is exact, `try_from_usize` is its inverse on
// `[0, max_nat)`, `max_spec()` projects to `max_nat() - 1` — so no impl has to restate
// or re-prove anything, and adding an index type stays as cheap as it is today.
//
// Every operation is bounded by `I::max_nat()`, not by the machine word. An index type
// may be narrower than the word carrying it (`DenseId31` lives in a `u32`, MSB reserved
// for the inline capture flag), so a sum landing in that gap has no index even though the
// word addition did not overflow. Returning it would hand back a value whose MSB reads as
// a tag — the arithmetic equivalent of `try_from_usize` narrowing before it checks.
//
// The guards are written against `I::max().as_usize()` rather than against `usize::MAX`.
// That is what makes them exact: it is the largest *index*, and getting it through
// `as_usize` also establishes `max_nat() - 1 <= usize::MAX` in passing, which is what
// licenses the `usize` intermediates below without a new proof obligation on the trait.
// ---------------------------------------------------------------------------

/// `a + b` as an index of `I`, or `None` if the sum is not representable.
pub fn checked_add<I: IndexLike>(a: I, b: I) -> (r: Option<I>)
    ensures
        r is Some ==> r->Some_0.as_nat() == a.as_nat() + b.as_nat(),
        r is Some <==> a.as_nat() + b.as_nat() < I::max_nat(),
{
    let mx = <I as IndexLike>::max().as_usize();
    let x = a.as_usize();
    let y = b.as_usize();
    proof {
        // x <= mx and y <= mx, so `mx - x` cannot underflow and, in the taken
        // branch, `x + y <= mx` cannot overflow the `usize` either.
        a.lemma_as_nat_bounded();
        b.lemma_as_nat_bounded();
        I::lemma_max_as_nat();
    }
    if y > mx - x {
        None
    } else {
        I::try_from_usize(x + y)
    }
}

/// `a - b` as an index of `I`, or `None` if `b > a`. There are no negative indices, so
/// this is the only way to subtract one.
pub fn checked_sub<I: IndexLike>(a: I, b: I) -> (r: Option<I>)
    ensures
        r is Some ==> r->Some_0.as_nat() + b.as_nat() == a.as_nat(),
        r is Some <==> b.as_nat() <= a.as_nat(),
{
    let x = a.as_usize();
    let y = b.as_usize();
    proof {
        // The difference is at most `a.as_nat()`, which is already in range, so
        // the non-`None` branch always succeeds.
        a.lemma_as_nat_bounded();
    }
    if x < y {
        None
    } else {
        I::try_from_usize(x - y)
    }
}

/// `a * b` as an index of `I`, or `None` if the product is not representable.
///
/// For strides into a flattened pool (`base + k * stride`), where the product is the term
/// that leaves the range first: it is bounded by neither factor's width, so a guard
/// written against the factors — however careful — does not constrain it.
///
/// Computed in `u128` rather than guarded by a division. Two `usize` factors cannot
/// overflow a `u128`, so the product is exact before it is compared, and the comparison is
/// against the largest *index* rather than against `usize::MAX`.
pub fn checked_mul<I: IndexLike>(a: I, b: I) -> (r: Option<I>)
    ensures
        r is Some ==> r->Some_0.as_nat() == a.as_nat() * b.as_nat(),
        r is Some <==> a.as_nat() * b.as_nat() < I::max_nat(),
{
    let mx = <I as IndexLike>::max().as_usize();
    let x = a.as_usize();
    let y = b.as_usize();
    proof {
        a.lemma_as_nat_bounded();
        b.lemma_as_nat_bounded();
        I::lemma_max_as_nat();
        lemma_u64_usize_64bit();
        // Both factors are below 2^64, so the product is below 2^128: the widened
        // multiply cannot itself overflow, which is the whole point of doing it.
        assert((x as u128) * (y as u128) <= u128::MAX) by (nonlinear_arith)
            requires x <= u64::MAX, y <= u64::MAX;
    }
    let p: u128 = (x as u128) * (y as u128);
    if p > mx as u128 {
        None
    } else {
        I::try_from_usize(p as usize)
    }
}

/// `a + 1`, or `None` at the maximum index.
///
/// The common case by a wide margin — a cursor, a length, a fresh position — and the one
/// worth having separately: a bump needs no second value of `I` to be constructed first.
pub fn checked_incr<I: IndexLike>(a: I) -> (r: Option<I>)
    ensures
        r is Some ==> r->Some_0.as_nat() == a.as_nat() + 1,
        r is Some <==> a.as_nat() + 1 < I::max_nat(),
{
    let mx = <I as IndexLike>::max().as_usize();
    let x = a.as_usize();
    proof {
        a.lemma_as_nat_bounded();
        I::lemma_max_as_nat();
    }
    if x >= mx {
        None
    } else {
        I::try_from_usize(x + 1)
    }
}

/// `a - 1`, or `None` at index 0.
pub fn checked_decr<I: IndexLike>(a: I) -> (r: Option<I>)
    ensures
        r is Some ==> r->Some_0.as_nat() + 1 == a.as_nat(),
        r is Some <==> 0 < a.as_nat(),
{
    let x = a.as_usize();
    proof {
        a.lemma_as_nat_bounded();
    }
    if x == 0 {
        None
    } else {
        I::try_from_usize(x - 1)
    }
}

/// `a + n` where `n` is a `usize` count, or `None` if the sum is not representable in `I`.
///
/// The boundary between a `std` collection's `len()` and a narrow stored index: the count
/// arrives unbounded by `I` and must not be assumed to fit.
pub fn checked_add_usize<I: IndexLike>(a: I, n: usize) -> (r: Option<I>)
    ensures
        r is Some ==> r->Some_0.as_nat() == a.as_nat() + (n as nat),
        r is Some <==> a.as_nat() + (n as nat) < I::max_nat(),
{
    let mx = <I as IndexLike>::max().as_usize();
    let x = a.as_usize();
    proof {
        a.lemma_as_nat_bounded();
        I::lemma_max_as_nat();
    }
    if n > mx - x {
        None
    } else {
        I::try_from_usize(x + n)
    }
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
    proof fn lemma_order_is_as_nat(a: Self, b: Self) {
        // Explicit unfold of the `open` default order bodies; stated (not
        // auto-unfolded) for stability under crate-wide spec pruning.
        assert(a.lt_spec(b) == (a.as_nat() < b.as_nat()));
        assert(a.le_spec(b) == (a.as_nat() <= b.as_nat()));
    }

    // 0x100 <= usize::MAX + 1 once `usize` is known to be 64 bits wide.
    proof fn lemma_max_nat_fits_usize() { lemma_u64_usize_64bit(); }

    fn min() -> Self { 0u8 }
    fn max() -> Self { u8::MAX }

    fn as_usize(self) -> usize { self as usize }

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
    proof fn lemma_order_is_as_nat(a: Self, b: Self) {
        // Explicit unfold of the `open` default order bodies; stated (not
        // auto-unfolded) for stability under crate-wide spec pruning.
        assert(a.lt_spec(b) == (a.as_nat() < b.as_nat()));
        assert(a.le_spec(b) == (a.as_nat() <= b.as_nat()));
    }

    proof fn lemma_max_nat_fits_usize() { lemma_u64_usize_64bit(); }

    fn min() -> Self { 0u16 }
    fn max() -> Self { u16::MAX }

        fn as_usize(self) -> usize { self as usize }

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
    proof fn lemma_order_is_as_nat(a: Self, b: Self) {
        // Explicit unfold of the `open` default order bodies; stated (not
        // auto-unfolded) for stability under crate-wide spec pruning.
        assert(a.lt_spec(b) == (a.as_nat() < b.as_nat()));
        assert(a.le_spec(b) == (a.as_nat() <= b.as_nat()));
    }

    proof fn lemma_max_nat_fits_usize() { lemma_u64_usize_64bit(); }

    fn min() -> Self { 0u32 }
    fn max() -> Self { u32::MAX }

        fn as_usize(self) -> usize { self as usize }

        fn try_from_usize(n: usize) -> Option<Self> {
        // Compared in `usize`, like u8/u16 above and production's
        // `n.try_into().ok()`, rather than through a `u64` round-trip.
        // Codegen-identical (LLVM canonicalizes both to the same high-word
        // test); this is just the form that matches its siblings.
        if n <= u32::MAX as usize { Some(n as u32) } else { None }
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
    proof fn lemma_order_is_as_nat(a: Self, b: Self) {
        // Explicit unfold of the `open` default order bodies; stated (not
        // auto-unfolded) for stability under crate-wide spec pruning.
        assert(a.lt_spec(b) == (a.as_nat() < b.as_nat()));
        assert(a.le_spec(b) == (a.as_nat() <= b.as_nat()));
    }

    // The tight case: `max_nat()` IS `usize::MAX + 1` here, so this is exactly the
    // 64-bit-host assumption the `cfg` gate above already makes explicit.
    proof fn lemma_max_nat_fits_usize() { lemma_u64_usize_64bit(); }

    fn min() -> Self { 0u64 }
    fn max() -> Self { u64::MAX }

    // 64-bit host (this impl is `#[cfg(target_pointer_width = "64")]`): `usize`
    // and `u64` are the same width, so both casts are the identity on values.
    // The `global size_of usize == 8` fact (below) discharges them — no longer
    // external_body. `lemma_u64_usize_64bit` packages `usize::MAX == u64::MAX`.
    fn as_usize(self) -> usize {
        proof { lemma_u64_usize_64bit(); }
        self as usize
    }

    fn try_from_usize(n: usize) -> Option<Self> {
        proof { lemma_u64_usize_64bit(); }
        Some(n as u64)
    }

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
    proof fn lemma_order_is_as_nat(a: Self, b: Self) {
        // Explicitly unfold the `open` default bodies (`lt_spec(b) == as_nat() <
        // as_nat()`, likewise `le_spec`). Stated rather than left to auto-unfold
        // so the proof is stable under crate-wide spec pruning.
        assert(a.lt_spec(b) == (a.as_nat() < b.as_nat()));
        assert(a.le_spec(b) == (a.as_nat() <= b.as_nat()));
    }

    // `max_nat()` is defined as `usize::MAX + 1`; the obligation is that definition.
    proof fn lemma_max_nat_fits_usize() {}

    fn min() -> Self { 0usize }
    fn max() -> Self { usize::MAX }

    fn as_usize(self) -> usize { self }
    fn try_from_usize(n: usize) -> Option<Self> { Some(n) }

    fn lt(self, other: Self) -> bool { self < other }
    fn le(self, other: Self) -> bool { self <= other }
}

} // verus!
