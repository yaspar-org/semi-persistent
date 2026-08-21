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
    pub(crate) repr: T::Repr,
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
    pub open(crate) spec fn get_spec(self) -> Option<T> {
        if T::tag_of(self.repr) {
            None
        } else {
            Some(T::value_of(self.repr))
        }
    }

    /// `Opt` is well-formed iff its repr is.
    pub open(crate) spec fn wf(self) -> bool {
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
        requires self.wf(),
        ensures self.get_spec() is Some ==> Some(v) == self.get_spec(),
    {
        // Total-with-documented-panic: presence is the branch.
        if !self.is_some() {
            crate::guard::refuse("Opt::get: value is None");
        }
        T::from_repr(&self.repr)
    }

    /// The optional value (production `Opt::get` parity — production's `get`
    /// returned `Option<T>`; under the verus names `get` unwraps and this is the
    /// total, `Option`-returning form). prod-parity.
    pub fn to_option(&self) -> (r: Option<T>)
        requires self.wf(),
        ensures r == self.get_spec(),
    {
        if T::tag(&self.repr) {
            None
        } else {
            Some(T::from_repr(&self.repr))
        }
    }

    /// The embedded value, **ignoring the option bit**. `get_spec()` is
    /// `Some(value_spec())` when the tag is clear and `None` when it is set; this
    /// projection sees the value in *both* cases, which is what makes the
    /// value-preserving `set_none`/`get_unchecked` pair below meaningful.
    pub open(crate) spec fn value_spec(self) -> T {
        T::value_of(self.repr)
    }

    /// The embedded value even when the option bit says `None` — the verified
    /// counterpart of the e-graph's `EClassEntry::repr_id_unchecked`. A class that has
    /// been absorbed keeps its (now-absent) repr key in place; the merge path
    /// reads it back to look up the absorbed class's data before the key is
    /// removed from the sparse set. `Tagged::from_repr` already strips the tag,
    /// so this needs only `wf` — no `is Some` precondition, unlike `get`.
    pub fn get_unchecked(&self) -> (v: T)
        requires self.wf(),
        ensures v == self.value_spec(),
    {
        T::from_repr(&self.repr)
    }

    /// Set the option bit to `None` **in place, preserving the value** — the
    /// verified counterpart of `EClassEntry::set_absent`. `Tagged::set_tag`'s contract
    /// is exactly "flips the tag, keeps `value_of`", so the value stays readable
    /// through `get_unchecked` afterwards.
    pub fn set_none(&mut self)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).get_spec() is None,
            final(self).value_spec() == old(self).value_spec(),
    {
        T::set_tag(&mut self.repr);
    }

    /// The raw repr (spec counterpart; the field is `pub(crate)` — privacy closeout).
    pub open(crate) spec fn repr_spec(self) -> T::Repr {
        self.repr
    }

    /// Embed into the raw repr (for storing inside a struct's Repr).
    pub fn into_raw(self) -> (r: T::Repr)
        ensures r == self.repr_spec(),
    {
        self.repr
    }

    /// Reconstruct from a raw repr.
    pub fn from_raw(r: T::Repr) -> (o: Opt<T>)
        ensures o.repr_spec() == r,
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

// prod-parity: `Default for Opt<T>` is `None` — production parity
// (`containers/src/tagged.rs:67`). `Vec::restore` requires the element type to
// be `Default` (it refills reclaimed slots before overwriting), and the
// consumer stores `Opt<T>` in such a `Vec` (`classes.rs` min-pool). Verus's
// `none()` needs `T: Default` (to mint a repr), so the bound is slightly
// tighter than production's `T: Tagged`; every consumer element type is Default.
impl<T: Tagged + core::default::Default> core::default::Default for Opt<T> {
    fn default() -> (r: Opt<T>)
        ensures r.wf(), r.get_spec() is None,
    {
        Opt::none()
    }
}

/// An id type in bijection with a dense `usize` range `[0, max)`. Used to index
/// arena vectors (list ids → heads, node ids → nodes). Modeled like
/// `IndexLike` (ghost `as_nat` + injective + bounded) plus exec `as_usize` /
/// `from_usize`.
pub trait DenseId:
    Sized
    + Copy
    + crate::index_like::IndexLike
    + crate::tagged::Tagged
    + core::default::Default
    + core::cmp::PartialEq
    + core::cmp::Eq
    + core::cmp::PartialOrd
    + core::cmp::Ord
    + core::hash::Hash
    + Into<<Self as DenseId>::Index>
{
    /// Natural storage word for this id (production's `DenseId::Index`: u8, u16,
    /// u32, or u64). This is the `Word` a `NodeLayout` stores keys as, and is
    /// what makes the B+tree generic over the 31-bit (`u32`) and 63-bit (`u64`)
    /// id families.
    ///
    /// `Tagged` matches production's `DenseId` (`containers/src/dense_id.rs:21`,
    /// `type Index: IndexLike + Tagged`): the consumer's `EClassEntry`/`ClassData`
    /// store an id's word directly and steal its MSB as a niche
    /// (`egraph/src/classes.rs`), which needs `Index: Tagged`. Every `Index`
    /// (u8/u16/u32/u64/usize) already impls `Tagged` (`tagged.rs`), so the bound
    /// is discharged by the existing impls.
    type Index: crate::index_like::IndexLike + crate::tagged::Tagged;

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

    /// The `IndexLike` projection (now a supertrait) and the `DenseId`
    /// projection coincide — both name the dense index. Every concrete impl has
    /// `as_nat(self) == id_nat(self) == self@`; this law exposes that to generic
    /// code, which Verus does not unfold through a type parameter. It is what
    /// lets `as_usize` (whose `IndexLike` ensures is stated in `as_nat`) satisfy
    /// a `DenseId` postcondition stated in `id_nat`.
    proof fn lemma_as_nat_is_id_nat(self)
        ensures self.as_nat() == self.id_nat();

    /// Production's `DenseId::to_usize` spelling (`containers/src/dense_id.rs:23`).
    /// prod-parity: the consumer calls `to_usize`; verus's own code uses
    /// `as_usize`. Provided default delegates through the supertrait `as_usize`;
    /// the bridge law reconciles its `as_nat`-stated ensures with `id_nat`.
    fn to_usize(self) -> (r: usize)
        ensures r as nat == self.id_nat()
    {
        proof { self.lemma_as_nat_is_id_nat(); }
        self.as_usize()
    }

    /// Exec: construct from a `usize`. Round-trips with `as_usize` for any
    /// representable index (`n < id_bound()`); out-of-range `n` has no
    /// guarantee (a bounded id may mask). `DenseUsize`'s bound is `usize::MAX +
    /// 1`, so it round-trips unconditionally.
    fn from_usize(n: usize) -> (r: Self)
        ensures (n as nat) < Self::id_bound() ==> r.id_nat() == n as nat;

    /// Exec: range-checked construction — `Some` exactly on the representable
    /// range. The primitive `IdFactory` allocates through (production's
    /// `try_alloc` checked the WORD range, not the id range, and would panic
    /// half-way through the bit-stealing family's word range; checking
    /// `id_bound` here is the corrected contract).
    fn try_new(n: usize) -> (r: Option<Self>)
        ensures
            r is Some <==> (n as nat) < Self::id_bound(),
            r is Some ==> r->Some_0.id_nat() == n as nat;

    /// Injectivity: distinct ids project to distinct nats.
    proof fn lemma_id_injective(a: Self, b: Self)
        requires a.id_nat() == b.id_nat(),
        ensures a == b;

    /// `id_nat` is always within `id_bound` (the doc invariant on `id_bound`).
    /// What makes `from_usize(self.as_usize())` round-trip: the cursor's `key()`
    /// reads a stored word back into a `K`, and this is the precondition
    /// (`as_usize() < id_bound`) the `from_usize` round-trip needs.
    proof fn lemma_id_nat_bounded(tracked self)
        ensures self.id_nat() < Self::id_bound();

    /// The dense range fits in a `usize`. Inherent to the trait's meaning — a
    /// `DenseId` is a bijection with a dense `usize` range, and `from_usize` /
    /// `as_usize` would be ill-defined past `usize::MAX`. Every impl is a
    /// bit-stealing word type (bound `2^(w-1)`) or `DenseUsize` (bound exactly
    /// `usize::MAX + 1`), so all satisfy it.
    ///
    /// Why it must be a law and not a derived fact: code holding an `N` (rather
    /// than its `usize`) needs `id_nat() <= usize::MAX` to relate the id to a
    /// width-agnostic `Seq<usize>` model — e.g. `CircularList::next_of`, which
    /// returns the successor as `N` and must tie it to `next_seq()`, a
    /// `Seq<usize>`. The old `usize`-returning surface got the bound for free
    /// from `to_usize`'s ensures; an `N`-typed surface has no such handle.
    proof fn lemma_id_bound_fits_usize()
        ensures Self::id_bound() <= usize::MAX as nat + 1;

    /// How the value count relates to the storage word's range. A
    /// bit-stealing id (Id31/Id63) keeps one bit for the tag, so it has exactly
    /// HALF the word's values: `id_bound * 2 == Index::max_nat()`. A full-range id
    /// (DenseUsize) uses the whole word: `id_bound == Index::max_nat()`. The
    /// disjunction lets every `DenseId` honestly report which it is; the B+tree
    /// (only ever keyed by a bit-stealing id) consumes the `* 2` arm to bound the
    /// arena. `is_bit_stealing()` selects the arm so generic tree code can branch.
    spec fn is_bit_stealing() -> bool;

    /// Exec counterpart of `is_bit_stealing`: a static
    /// type property, so every impl is a literal and the check const-folds;
    /// it exists so the B+tree's total shell can refuse a non-bit-stealing
    /// key at runtime instead of carrying a `requires`.
    fn bit_stealing() -> (b: bool)
        ensures b == Self::is_bit_stealing();

    proof fn lemma_id_bound_word_relation()
        ensures
            if Self::is_bit_stealing() {
                Self::id_bound() * 2 == <Self::Index as crate::index_like::IndexLike>::max_nat()
            } else {
                Self::id_bound() == <Self::Index as crate::index_like::IndexLike>::max_nat()
            };
}

/// A concrete `DenseId` over `usize` (the dense index is the value itself).
/// Mirrors production's `define_id*!` newtypes at the model level; concrete
/// instantiation point for `ListArena`.
#[derive(Copy, Clone)]
pub struct DenseUsize {
    pub(crate) raw: usize,
}

impl DenseUsize {
    /// The raw value (spec counterpart; the field is `pub(crate)` — privacy
    /// closeout). The open trait-impl spec fn delegates here.
    pub open(crate) spec fn raw_spec(self) -> nat {
        self.raw as nat
    }
}

// prod-parity: the production-parity `DenseId` supertrait bundle needs `Tagged`
// on `DenseUsize`. It is full-range (no bit to steal), so it uses the
// `BoolTagged` fallback repr exactly like the primitive `usize` impl — the tag
// is a separate bool, `repr_wf` is vacuous.
impl crate::tagged::Tagged for DenseUsize {
    type Repr = crate::tagged::BoolTagged<DenseUsize>;
    open spec fn value_of(r: Self::Repr) -> Self { r.value }
    open spec fn tag_of(r: Self::Repr) -> bool { r.tagged }
    open spec fn repr_wf(_r: Self::Repr) -> bool { true }
    proof fn lemma_repr_extensional(_r1: Self::Repr, _r2: Self::Repr) {}
    fn into_repr(self) -> Self::Repr { crate::tagged::BoolTagged { tagged: false, value: self } }
    fn from_repr(r: &Self::Repr) -> Self { r.value }
    fn tag(r: &Self::Repr) -> bool { r.tagged }
    fn set_tag(r: &mut Self::Repr) { r.tagged = true; }
    fn clear_tag(r: &mut Self::Repr) { r.tagged = false; }
}

// prod-parity: `IndexLike` is now a supertrait of `DenseId` (matching
// production, whose `DenseId: … + IndexLike`), so `DenseUsize` — the internal
// ListArena id — must impl it. Mirrors the primitive `usize` impl
// (`index_like.rs`): full-range, `as_nat` is the raw value, no bit-stealing.
impl crate::index_like::IndexLike for DenseUsize {
    open spec fn as_nat(self) -> nat { self.raw_spec() }
    open spec fn max_nat() -> nat { usize::MAX as nat + 1 }
    // `closed`: constructs `DenseUsize` (opaque outside the crate via its
    // `pub(crate)` field), so the body must not be visible everywhere — same as
    // `DenseId31`/`DenseId63`'s `min_spec`/`max_spec`.
    closed spec fn min_spec() -> Self { DenseUsize { raw: 0 } }
    closed spec fn max_spec() -> Self { DenseUsize { raw: usize::MAX } }

    proof fn lemma_as_nat_bounded(tracked self) {}
    proof fn lemma_as_nat_injective(a: Self, b: Self) {}
    proof fn lemma_min_as_nat() {}
    proof fn lemma_max_nat_positive() {}
    proof fn lemma_max_as_nat() {}
    proof fn lemma_order_is_as_nat(a: Self, b: Self) {
        assert(a.lt_spec(b) == (a.as_nat() < b.as_nat()));
        assert(a.le_spec(b) == (a.as_nat() <= b.as_nat()));
    }
    // `max_nat()` is defined as `usize::MAX + 1` — the obligation is that definition.
    proof fn lemma_max_nat_fits_usize() {}

    fn min() -> Self { DenseUsize { raw: 0 } }
    fn max() -> Self { DenseUsize { raw: usize::MAX } }
    fn as_usize(self) -> usize { self.raw }
    fn try_from_usize(n: usize) -> Option<Self> { Some(DenseUsize { raw: n }) }
    fn lt(self, other: Self) -> bool { self.raw < other.raw }
    fn le(self, other: Self) -> bool { self.raw <= other.raw }
}

impl DenseId for DenseUsize {
    type Index = usize;

    open spec fn id_nat(self) -> nat {
        self.raw_spec()
    }

    open spec fn id_bound() -> nat {
        usize::MAX as nat + 1
    }

    fn to_index(self) -> (w: usize) {
        self.raw
    }

    // `as_usize` is inherited from the `IndexLike` supertrait (prod-parity).

    fn from_usize(n: usize) -> (r: Self) {
        DenseUsize { raw: n }
    }

    fn try_new(n: usize) -> (r: Option<Self>) {
        Some(DenseUsize { raw: n })  // full-range: every usize is representable
    }

    proof fn lemma_id_injective(a: Self, b: Self) {
        // id_nat is `raw as nat`, injective on usize.
    }

    proof fn lemma_as_nat_is_id_nat(self) {
        // Both are `self.raw_spec()`.
    }

    proof fn lemma_id_nat_bounded(tracked self) {
        // id_nat == raw as nat <= usize::MAX < usize::MAX + 1 == id_bound.
    }

    proof fn lemma_id_bound_fits_usize() {
        // Full-range: id_bound IS usize::MAX + 1 (the `<=` arm is equality).
    }

    open spec fn is_bit_stealing() -> bool { false }   // full-range id

    fn bit_stealing() -> (b: bool) { false }

    proof fn lemma_id_bound_word_relation() {
        // id_bound == usize::MAX + 1 == <usize as IndexLike>::max_nat() (the `== ` arm).
    }
}

/// Corollary of `lemma_id_bound_fits_usize` + `lemma_id_nat_bounded`, in the
/// form call sites actually want: this id's dense index is a representable
/// `usize`, so `id_nat() as usize` does not truncate. A free function rather
/// than a defaulted trait method — a `proof fn` with a body inside the trait
/// makes Verus re-check the surrounding lemmas' postconditions in every impl.
pub proof fn lemma_id_nat_fits_usize<N: DenseId>(tracked id: N)
    ensures
        id.id_nat() <= usize::MAX as nat,
        (id.id_nat() as usize) as nat == id.id_nat(),
{
    N::lemma_id_bound_fits_usize();
    id.lemma_id_nat_bounded();
}

} // verus!

// prod-parity: the production-parity `DenseId` supertrait bundle needs these
// plain-Rust impls on `DenseUsize`. It is full-range, so ordering/equality/hash
// on the raw `usize` is the dense-index order (`lemma_order_is_as_nat`), and
// `Into<usize>` is the identity on the value.
impl core::default::Default for DenseUsize {
    #[inline(always)]
    fn default() -> Self {
        DenseUsize { raw: 0 }
    }
}
impl PartialEq for DenseUsize {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}
impl Eq for DenseUsize {}
impl PartialOrd for DenseUsize {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for DenseUsize {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.raw.cmp(&other.raw)
    }
}
impl core::hash::Hash for DenseUsize {
    #[inline(always)]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}
impl From<DenseUsize> for usize {
    #[inline(always)]
    fn from(id: DenseUsize) -> usize {
        id.raw
    }
}
// prod-parity: `IndexLike: Debug` (production parity, dense_id.rs:69).
impl core::fmt::Debug for DenseUsize {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "DenseUsize({})", self.raw)
    }
}

// Production-surface parity: production prints `Some(v)` / `None`.
impl<T> core::fmt::Debug for Opt<T>
where
    T: crate::tagged::Tagged + Copy + core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.to_option(), f)
    }
}
