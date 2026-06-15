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
pub trait Tagged: Sized + Copy {
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
            Self::repr_wf(*r),
            Self::value_of(*r) == Self::value_of(*old(r)),
            Self::tag_of(*r) == true;

    /// Clear the tag bit. Value, well-formedness preserved.
    fn clear_tag(r: &mut Self::Repr)
        requires Self::repr_wf(*old(r)),
        ensures
            Self::repr_wf(*r),
            Self::value_of(*r) == Self::value_of(*old(r)),
            Self::tag_of(*r) == false;
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

} // verus!
