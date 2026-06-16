// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `Opt<T>`: niche-optional over a `Tagged` repr, and `DenseId`: an
//! id type that is a bijection with a dense `usize` range. Both are
//! prerequisites for `ListArena` (intrusive linked lists over a node arena).
//!
//! `Opt<T>` packs `Option<T>` into a single `T::Repr` using `T`'s tag bit:
//! `tag_of(repr) == true` encodes `None`, otherwise `Some(value_of(repr))`.
//! Like production, an `Opt<T>` must live inside a struct that provides its
//! own (different) capture bit — `Opt` owns the option bit, the enclosing
//! struct owns the capture bit, on separate fields, so they never collide.

use vstd::prelude::*;

use crate::index_like::IndexLike;
use crate::tagged::Tagged;

verus! {

/// A `Tagged` type that also requires `Default` (needed to mint the `None`
/// repr: take any value, set its tag). The crate's `Copy` convention applies.
pub trait OptElem: Tagged + core::default::Default {
}

/// Niche-optional over `T::Repr`. `None` is `tag_of` set; `Some(v)` is a clean
/// repr with `value_of == v`.
#[derive(Copy)]
pub struct Opt<T: Tagged> {
    pub repr: T::Repr,
}

// Hand-written `Clone` (a plain copy); the autoderived `Clone` on a generic
// struct emits a "clone is not a copy" warning under Verus otherwise.
impl<T: Tagged> Clone for Opt<T> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

impl<T: Tagged> Opt<T> {
    /// Ghost view: the optional value this repr encodes. Requires `repr_wf`.
    pub open spec fn get_spec(self) -> Option<T> {
        if T::tag_of(self.repr) {
            None
        } else {
            Some(T::value_of(self.repr))
        }
    }

    /// `Opt` is well-formed iff its repr is.
    pub open spec fn wf(self) -> bool {
        T::repr_wf(self.repr)
    }

    /// `Some(val)`: encode the value with tag clear.
    pub fn some(val: T) -> (r: Opt<T>)
        ensures r.wf(), r.get_spec() == Some(val),
    {
        Opt { repr: val.into_repr() }
    }

    /// `is_none` reads the tag.
    pub fn is_none(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.get_spec() is None),
    {
        T::tag(&self.repr)
    }

    pub fn is_some(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.get_spec() is Some),
    {
        !T::tag(&self.repr)
    }

    /// Extract the value (panics on `None` in exec via the precondition).
    pub fn get(&self) -> (v: T)
        requires self.wf(), self.get_spec() is Some,
        ensures Some(v) == self.get_spec(),
    {
        T::from_repr(&self.repr)
    }

    /// Embed into the raw repr (for storing inside a struct's Repr).
    pub fn into_raw(self) -> (r: T::Repr)
        ensures r == self.repr,
    {
        self.repr
    }

    /// Reconstruct from a raw repr.
    pub fn from_raw(r: T::Repr) -> (o: Opt<T>)
        ensures o.repr == r,
    {
        Opt { repr: r }
    }
}

impl<T: Tagged + core::default::Default> Opt<T> {
    /// `None`: take any value's repr and set its tag bit.
    pub fn none() -> (r: Opt<T>)
        ensures r.wf(), r.get_spec() is None,
    {
        let mut repr = T::default().into_repr();
        T::set_tag(&mut repr);
        Opt { repr }
    }
}

/// An id type in bijection with a dense `usize` range `[0, max)`. Used to index
/// arena vectors (list ids → heads, node ids → nodes). Modeled like
/// `IndexLike` (ghost `as_nat` + injective + bounded) plus exec `as_usize` /
/// `from_usize`.
pub trait DenseId: Sized + Copy {
    /// Natural storage word for this id (production's `DenseId::Index`: u8, u16,
    /// u32, or u64). This is the `Word` a `NodeLayout` stores keys as, and is
    /// what makes the B+tree generic over the 31-bit (`u32`) and 63-bit (`u64`)
    /// id families.
    type Index: crate::index_like::IndexLike;

    /// Ghost projection to a natural number (the dense index).
    spec fn id_nat(self) -> nat;

    /// One past the largest representable dense index (`2^31` for a 31-bit id,
    /// `usize::MAX + 1` for `DenseUsize`). `from_usize` round-trips exactly the
    /// indices below this bound; `id_nat` is always within it.
    spec fn id_bound() -> nat;

    /// Exec: serialize the id to its storage word (production's
    /// `Into<Self::Index>`, used as `key_to_word(k) = k.into()`). The word's
    /// dense index equals the id's, so ordering on words agrees with ordering
    /// on ids; this is what lets the B+tree store and compare `Index` words
    /// while reasoning about the abstract `id_nat` model.
    fn to_index(self) -> (w: Self::Index)
        ensures w.as_nat() == self.id_nat();

    /// Exec: project to `usize`.
    fn as_usize(self) -> (r: usize)
        ensures r as nat == self.id_nat();

    /// Exec: construct from a `usize`. Round-trips with `as_usize` for any
    /// representable index (`n < id_bound()`); out-of-range `n` has no
    /// guarantee (a bounded id may mask). `DenseUsize`'s bound is `usize::MAX +
    /// 1`, so it round-trips unconditionally.
    fn from_usize(n: usize) -> (r: Self)
        ensures (n as nat) < Self::id_bound() ==> r.id_nat() == n as nat;

    /// Injectivity: distinct ids project to distinct nats.
    proof fn lemma_id_injective(a: Self, b: Self)
        requires a.id_nat() == b.id_nat(),
        ensures a == b;
}

/// A concrete `DenseId` over `usize` (the dense index is the value itself).
/// Mirrors production's `define_id*!` newtypes at the model level; concrete
/// instantiation point for `ListArena`.
#[derive(Copy, Clone)]
pub struct DenseUsize {
    pub raw: usize,
}

impl DenseId for DenseUsize {
    type Index = usize;

    open spec fn id_nat(self) -> nat {
        self.raw as nat
    }

    open spec fn id_bound() -> nat {
        usize::MAX as nat + 1
    }

    fn to_index(self) -> (w: usize) {
        self.raw
    }

    fn as_usize(self) -> (r: usize) {
        self.raw
    }

    fn from_usize(n: usize) -> (r: Self) {
        DenseUsize { raw: n }
    }

    proof fn lemma_id_injective(a: Self, b: Self) {
        // id_nat is `raw as nat`, injective on usize.
    }
}

} // verus!
