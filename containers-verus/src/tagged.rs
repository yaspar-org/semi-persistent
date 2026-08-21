// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Tagged`: the bit-stealing contract.
//!
//! A `Tagged` impl provides an injective encoding `(T, bool) -> Repr` so a
//! capture flag can be packed alongside the value. Three ghost spec items
//! describe the encoding:
//!
//!   - `value_of(r) -> Self`         — the clean value embedded in `r`
//!   - `tag_of(r) -> bool`           — the tag bit embedded in `r`
//!   - `repr_wf(r) -> bool`          — niche predicate: which reprs are in
//!                                     the image of the encoding.
//!
//! The niche obligation: a bit-stealing impl (e.g. `DenseId<31>` over `u32`)
//! reuses an unused bit of `Repr`'s state space to carry the tag. `repr_wf`
//! describes which reprs are reachable from `into_repr` / `set_tag` /
//! `clear_tag`. Concrete impls discharge:
//!
//!   - `into_repr(t)`  has  `value_of(_) == t && tag_of(_) == false`
//!     (and the result is implicitly `repr_wf` — see contract).
//!   - `set_tag` / `clear_tag` flip `tag_of`, preserve `value_of`,
//!     and preserve `repr_wf`.
//!   - Extensionality: two `repr_wf` reprs with the same `(value_of, tag_of)`
//!     are equal. This is the niche-injectivity property — without it the
//!     encoding wastes state.
//!
//! For the `BoolTagged<T>` fallback every `Repr` is `repr_wf`, so the niche
//! obligations collapse. Bit-stealing impls (lands later) must discharge
//! all of them explicitly.

use vstd::prelude::*;

verus! {

/// Bit-stealing contract for values that can carry a tag bit alongside them.
///
/// prod-parity: `Default` matches production's `Tagged: Copy + Default`
/// (`containers/src/tagged.rs:25`). The consumer relies on it transitively —
/// `DenseId::Index: Tagged` then gives `Index: Default`, which
/// `EClassEntry::default` and `SparseSet::restore`/`Vec::restore`'s
/// resize-refill need. Every `Tagged` type is already `Default` (the id types,
/// `Pair`, primitives).
pub trait Tagged: Sized + Copy + core::default::Default {
    type Repr: Sized + Copy;

    // -- ghost projections ---------------------------------------------------

    /// The clean value embedded in `r`. Survives `set_tag`/`clear_tag`.
    spec fn value_of(r: Self::Repr) -> Self;

    /// The tag bit embedded in `r`.
    spec fn tag_of(r: Self::Repr) -> bool;

    /// Niche predicate: `r` is in the image of the encoding. Bit-stealing
    /// impls use this to exclude reprs whose stolen bit is in an inconsistent
    /// state. Fallback impls (`BoolTagged<T>`) make this `true` everywhere.
    spec fn repr_wf(r: Self::Repr) -> bool;

    // -- niche-injectivity axiom (proof obligation) --------------------------

    /// Extensionality: two well-formed reprs with the same `(value_of, tag_of)`
    /// are equal. This is the bijection axiom — implementors discharge it.
    proof fn lemma_repr_extensional(r1: Self::Repr, r2: Self::Repr)
        requires
            Self::repr_wf(r1),
            Self::repr_wf(r2),
            Self::value_of(r1) == Self::value_of(r2),
            Self::tag_of(r1) == Self::tag_of(r2),
        ensures r1 == r2;

    // -- exec API ------------------------------------------------------------

    /// Encode a clean value with `tag = false`. Result is well-formed.
    fn into_repr(self) -> (r: Self::Repr)
        ensures
            Self::repr_wf(r),
            Self::value_of(r) == self,
            Self::tag_of(r) == false;

    /// Decode a `Repr` to its clean value, stripping the tag.
    fn from_repr(r: &Self::Repr) -> (v: Self)
        requires Self::repr_wf(*r),
        ensures v == Self::value_of(*r);

    /// Read the tag bit.
    fn tag(r: &Self::Repr) -> (b: bool)
        requires Self::repr_wf(*r),
        ensures b == Self::tag_of(*r);

    /// Set the tag bit. Value, well-formedness preserved.
    fn set_tag(r: &mut Self::Repr)
        requires Self::repr_wf(*old(r)),
        ensures
            Self::repr_wf(*final(r)),
            Self::value_of(*final(r)) == Self::value_of(*old(r)),
            Self::tag_of(*final(r)) == true;

    /// Clear the tag bit. Value, well-formedness preserved.
    fn clear_tag(r: &mut Self::Repr)
        requires Self::repr_wf(*old(r)),
        ensures
            Self::repr_wf(*final(r)),
            Self::value_of(*final(r)) == Self::value_of(*old(r)),
            Self::tag_of(*final(r)) == false;
}

// ---------------------------------------------------------------------------
// `BoolTagged<T>` — the canonical `(bool, T)` repr as a named struct.
//
// Verus's trait-conflict checker doesn't like tuple-typed associated types
// here, so we use a named struct. Layout-wise this is exactly `(bool, T)`.
// ---------------------------------------------------------------------------

#[derive(Copy)]
pub struct BoolTagged<T: Copy> {
    pub tagged: bool,
    pub value: T,
}

// Hand-written `Clone` (a plain copy); the autoderived `Clone` on a generic
// struct emits a "clone is not a copy" warning under Verus otherwise.
impl<T: Copy> Clone for BoolTagged<T> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

// ---------------------------------------------------------------------------
// Primitive integer impls — `BoolTagged<$T>` repr.
//
// Every `BoolTagged` is well-formed (no niche stolen), so the niche obligations
// collapse to `true` and extensionality follows from the struct layout.
// ---------------------------------------------------------------------------

impl Tagged for u8 {
    type Repr = BoolTagged<u8>;
    open spec fn value_of(r: Self::Repr) -> Self { r.value }
    open spec fn tag_of(r: Self::Repr) -> bool { r.tagged }
    open spec fn repr_wf(_r: Self::Repr) -> bool { true }
    proof fn lemma_repr_extensional(_r1: Self::Repr, _r2: Self::Repr) {}
    fn into_repr(self) -> Self::Repr { BoolTagged { tagged: false, value: self } }
    fn from_repr(r: &Self::Repr) -> Self { r.value }
    fn tag(r: &Self::Repr) -> bool { r.tagged }
    fn set_tag(r: &mut Self::Repr) { r.tagged = true; }
    fn clear_tag(r: &mut Self::Repr) { r.tagged = false; }
}

impl Tagged for u16 {
    type Repr = BoolTagged<u16>;
    open spec fn value_of(r: Self::Repr) -> Self { r.value }
    open spec fn tag_of(r: Self::Repr) -> bool { r.tagged }
    open spec fn repr_wf(_r: Self::Repr) -> bool { true }
    proof fn lemma_repr_extensional(_r1: Self::Repr, _r2: Self::Repr) {}
    fn into_repr(self) -> Self::Repr { BoolTagged { tagged: false, value: self } }
    fn from_repr(r: &Self::Repr) -> Self { r.value }
    fn tag(r: &Self::Repr) -> bool { r.tagged }
    fn set_tag(r: &mut Self::Repr) { r.tagged = true; }
    fn clear_tag(r: &mut Self::Repr) { r.tagged = false; }
}

impl Tagged for u32 {
    type Repr = BoolTagged<u32>;
    open spec fn value_of(r: Self::Repr) -> Self { r.value }
    open spec fn tag_of(r: Self::Repr) -> bool { r.tagged }
    open spec fn repr_wf(_r: Self::Repr) -> bool { true }
    proof fn lemma_repr_extensional(_r1: Self::Repr, _r2: Self::Repr) {}
    fn into_repr(self) -> Self::Repr { BoolTagged { tagged: false, value: self } }
    fn from_repr(r: &Self::Repr) -> Self { r.value }
    fn tag(r: &Self::Repr) -> bool { r.tagged }
    fn set_tag(r: &mut Self::Repr) { r.tagged = true; }
    fn clear_tag(r: &mut Self::Repr) { r.tagged = false; }
}

impl Tagged for u64 {
    type Repr = BoolTagged<u64>;
    open spec fn value_of(r: Self::Repr) -> Self { r.value }
    open spec fn tag_of(r: Self::Repr) -> bool { r.tagged }
    open spec fn repr_wf(_r: Self::Repr) -> bool { true }
    proof fn lemma_repr_extensional(_r1: Self::Repr, _r2: Self::Repr) {}
    fn into_repr(self) -> Self::Repr { BoolTagged { tagged: false, value: self } }
    fn from_repr(r: &Self::Repr) -> Self { r.value }
    fn tag(r: &Self::Repr) -> bool { r.tagged }
    fn set_tag(r: &mut Self::Repr) { r.tagged = true; }
    fn clear_tag(r: &mut Self::Repr) { r.tagged = false; }
}

impl Tagged for usize {
    type Repr = BoolTagged<usize>;
    open spec fn value_of(r: Self::Repr) -> Self { r.value }
    open spec fn tag_of(r: Self::Repr) -> bool { r.tagged }
    open spec fn repr_wf(_r: Self::Repr) -> bool { true }
    proof fn lemma_repr_extensional(_r1: Self::Repr, _r2: Self::Repr) {}
    fn into_repr(self) -> Self::Repr { BoolTagged { tagged: false, value: self } }
    fn from_repr(r: &Self::Repr) -> Self { r.value }
    fn tag(r: &Self::Repr) -> bool { r.tagged }
    fn set_tag(r: &mut Self::Repr) { r.tagged = true; }
    fn clear_tag(r: &mut Self::Repr) { r.tagged = false; }
}

// prod-parity: a named `Tagged` pair. Production impls `Tagged` for the tuple
// `(A, B)` (`containers/src/tagged.rs:157`), but Verus's Trait-Conflict-Checker
// rejects a `Tagged` (which is `: Copy`) impl on a tuple type — the same
// limitation that forced `BoolTagged` to be a named struct rather than
// `(bool, T)`. So the crate exposes this named `Pair<A, B>` instead, and the
// consumer aliases its pair types to it (e.g. `MSetChild<G> = Pair<G,
// Multiplicity>`). The tag lives entirely in `A`'s repr; `B` rides untagged.
#[derive(Copy)]
pub struct Pair<A, B> {
    pub a: A,
    pub b: B,
}

impl<A: Copy, B: Copy> Clone for Pair<A, B> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// Repr for `Pair<A, B>`: `A`'s repr carries the tag, `B` rides along.
#[derive(Copy)]
pub struct PairRepr<AR, B> {
    pub a: AR,
    pub b: B,
}

impl<AR: Copy, B: Copy> Clone for PairRepr<AR, B> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

impl<A: Tagged, B: Copy + core::default::Default> Tagged for Pair<A, B> {
    type Repr = PairRepr<A::Repr, B>;

    open spec fn value_of(r: Self::Repr) -> Self { Pair { a: A::value_of(r.a), b: r.b } }
    open spec fn tag_of(r: Self::Repr) -> bool { A::tag_of(r.a) }
    open spec fn repr_wf(r: Self::Repr) -> bool { A::repr_wf(r.a) }

    proof fn lemma_repr_extensional(r1: Self::Repr, r2: Self::Repr) {
        // A's extensionality forces r1.a == r2.a; equal `value_of` forces
        // r1.b == r2.b (the `b` field is exposed directly in `value_of`).
        A::lemma_repr_extensional(r1.a, r2.a);
    }

    fn into_repr(self) -> (r: Self::Repr) {
        PairRepr { a: self.a.into_repr(), b: self.b }
    }
    fn from_repr(r: &Self::Repr) -> (v: Self) {
        Pair { a: A::from_repr(&r.a), b: r.b }
    }
    fn tag(r: &Self::Repr) -> (b: bool) {
        A::tag(&r.a)
    }
    fn set_tag(r: &mut Self::Repr) {
        A::set_tag(&mut r.a);
    }
    fn clear_tag(r: &mut Self::Repr) {
        A::clear_tag(&mut r.a);
    }
}

} // verus!

// prod-parity: the consumer's cache requires `C: Clone + Copy + Hash + Eq +
// Debug` (production's tuple `(A,B)` got these structurally). Manual impls
// outside `verus!{}`, delegating to the fields — the same values production's
// tuple would compare/hash/print.
impl<A: PartialEq, B: PartialEq> PartialEq for Pair<A, B> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.a == other.a && self.b == other.b
    }
}
impl<A: Eq, B: Eq> Eq for Pair<A, B> {}
impl<A: core::default::Default, B: core::default::Default> core::default::Default for Pair<A, B> {
    #[inline(always)]
    fn default() -> Self {
        Pair {
            a: A::default(),
            b: B::default(),
        }
    }
}
impl<A: core::hash::Hash, B: core::hash::Hash> core::hash::Hash for Pair<A, B> {
    #[inline(always)]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.a.hash(state);
        self.b.hash(state);
    }
}
impl<A: core::fmt::Debug, B: core::fmt::Debug> core::fmt::Debug for Pair<A, B> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("Pair").field(&self.a).field(&self.b).finish()
    }
}

// Production-surface parity: production's BoolTagged derives Debug and has
// a `new` constructor.
impl<T: Copy> BoolTagged<T> {
    pub fn new(value: T) -> Self {
        BoolTagged {
            tagged: false,
            value,
        }
    }
}

impl<T: Copy + core::fmt::Debug> core::fmt::Debug for BoolTagged<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BoolTagged")
            .field("tagged", &self.tagged)
            .field("value", &self.value)
            .finish()
    }
}
