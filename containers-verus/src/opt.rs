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

use crate::tagged::Tagged;
use crate::index_like::IndexLike;

verus! {

/// A `Tagged` type that also requires `Default` (needed to mint the `None`
/// repr: take any value, set its tag). The crate's `Copy` convention applies.
pub trait OptElem: Tagged + core::default::Default {
}

/// Niche-optional over `T::Repr`. `None` is `tag_of` set; `Some(v)` is a clean
/// repr with `value_of == v`.
#[derive(Copy, Clone)]
pub struct Opt<T: Tagged> {
    pub repr: T::Repr,
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
    /// Ghost projection to a natural number (the dense index).
    spec fn id_nat(self) -> nat;

    /// Exec: project to `usize`.
    fn as_usize(self) -> (r: usize)
        ensures r as nat == self.id_nat();

    /// Exec: construct from a `usize`. Inverse of `as_usize` (round-trips).
    fn from_usize(n: usize) -> (r: Self)
        ensures r.id_nat() == n as nat;

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
    open spec fn id_nat(self) -> nat {
        self.raw as nat
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
