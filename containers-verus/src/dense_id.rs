// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `DenseId31`: a dense id over `u32` that genuinely steals the MSB as a tag.
//!
//! This is the type that ties the two trait layers together — it is *both*
//! [`IndexLike`](crate::index_like) (so it can index a `Vec`) and
//! [`Tagged`](crate::tagged) (so the same value type can be stored in an
//! `InlineStore` with the capture flag packed inline), exactly as production's
//! `define_id31!` makes one id type serve both roles.
//!
//! Two roles for the same 32-bit word, mirroring production's `define_id31!`:
//!   - the *clean* id `DenseId31` — its MSB is always clear (a type invariant),
//!     so it names a value in `[0, 2^31)` and indexes vectors directly;
//!   - the *stored repr* `u32` — its MSB carries the capture tag.
//!
//! `into_repr` is the identity on the bits (a clean id already has its MSB
//! clear); `from_repr` masks the MSB off; `set_tag`/`clear_tag` flip it while
//! leaving the low-31 value bits — hence `value_of` — untouched.
//!
//! ### What this exercises
//!
//! Both trait layers are discharged against `DenseId31`'s *real* masking
//! encoding, not the `BoolTagged` fallback's vacuous `repr_wf := true`:
//!   - **`Tagged`**: the niche axiom `lemma_repr_extensional` is a genuine
//!     `bit_vector` theorem (equal low-31 bits and equal MSB force word
//!     equality), and `into_repr`/`set_tag`/`clear_tag` carry their
//!     value-preservation ensures through the masks.
//!   - **`IndexLike`**: `as_nat` is the identity on the clean value (so
//!     injectivity is immediate), and the `[0, 2^31)` bound — which the
//!     `BoolTagged`/primitive impls get structurally — comes from the type
//!     invariant. `lemma_as_nat_bounded` takes `tracked self`, the receiver
//!     mode that lets `use_type_invariant` read `raw < 2^31` in a proof; that
//!     single trait-signature choice is what lets one `u32`-backed type carry
//!     a tight `2^31` index bound *and* a niche, rather than splitting the two
//!     concerns across types.
//!
//! An [`InlineStore`](crate::inline_store)`<DenseId31, DenseId31>` therefore
//! both indexes by and stores these ids, with the capture flag packed into the
//! stolen bit on the stored side.

use vstd::prelude::*;

use crate::diff_store::DiffStore;
use crate::index_like::IndexLike;
use crate::inline_store::InlineStore;
use crate::opt::DenseId;
use crate::tagged::Tagged;

verus! {

/// The value mask: the low 31 bits (everything but the stolen tag bit).
pub spec const VAL_MASK: u32 = 0x7fff_ffff;
/// The stolen tag bit: the MSB.
pub spec const TAG_BIT: u32 = 0x8000_0000;
/// One past the largest clean id (`2^31`).
pub spec const DENSE31_BOUND: u32 = 0x8000_0000;

/// A clean dense id: a `u32` whose MSB is always clear, so it names a value in
/// `[0, 2^31)`. The stolen MSB is available to `Tagged` consumers.
///
/// Opaque (it carries a `#[verifier::type_invariant]`): its field is private
/// and public contracts are stated against its `View` (`self@ : nat`, the
/// dense index), not the raw field.
#[derive(Copy, Clone)]
pub struct DenseId31 {
    raw: u32,
}

impl View for DenseId31 {
    type V = nat;

    /// The dense index: the raw value (its MSB is clear by the type invariant).
    closed spec fn view(&self) -> nat {
        self.raw as nat
    }
}

impl DenseId31 {
    /// Type invariant: a *clean* id never has the stolen bit set.
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.raw < DENSE31_BOUND
    }

    /// Construct from a `u32` known to fit in 31 bits.
    pub fn new(n: u32) -> (r: DenseId31)
        requires n < DENSE31_BOUND,
        ensures r@ == n as nat,
    {
        DenseId31 { raw: n }
    }

    /// The dense index as a `usize` (for indexing arena vectors).
    pub fn index(self) -> (r: usize)
        ensures r as nat == self@,
    {
        proof { use_type_invariant(&self); }
        self.raw as usize
    }
}

/// `Default` is id 0 (its MSB is clear, so it satisfies the type invariant).
/// Needed wherever a `DenseId31` is the index type of a semi-persistent
/// container: `restore` fills reclaimed slots with `Idx::default()` before
/// overwriting them from the captures, so the index type must be `Default` —
/// production's `define_id31!` ids are `Default` for the same reason. (The
/// filler value is never observed; it is always overwritten on the live path.)
impl core::default::Default for DenseId31 {
    fn default() -> (r: DenseId31)
        ensures r@ == 0nat,
    {
        DenseId31 { raw: 0 }
    }
}

// ---------------------------------------------------------------------------
// IndexLike: `as_nat` is the identity on the clean value, so injectivity is
// immediate; the `[0, 2^31)` bound comes from the type invariant, read in the
// `tracked self` obligation via `use_type_invariant`.
// ---------------------------------------------------------------------------

impl IndexLike for DenseId31 {
    open spec fn as_nat(self) -> nat { self@ }
    open spec fn max_nat() -> nat { DENSE31_BOUND as nat }
    closed spec fn min_spec() -> Self { DenseId31 { raw: 0 } }
    closed spec fn max_spec() -> Self { DenseId31 { raw: 0x7fff_ffff } }

    proof fn lemma_as_nat_bounded(tracked self) {
        use_type_invariant(self);  // raw < 2^31 == max_nat()
    }

    proof fn lemma_as_nat_injective(a: Self, b: Self) {
        // as_nat is the identity (a@ == b@ ⟹ a.raw == b.raw ⟹ a == b).
    }

    proof fn lemma_min_as_nat() {}

    proof fn lemma_max_as_nat() {}  // max_spec().as_nat() == 0x7fff_ffff == 2^31 - 1

    proof fn lemma_max_nat_positive() {}
    proof fn lemma_order_is_as_nat(a: Self, b: Self) {}

    fn min() -> Self { DenseId31 { raw: 0 } }

    fn max() -> Self { DenseId31 { raw: 0x7fff_ffff } }

    fn as_usize(self) -> (r: usize) {
        proof { use_type_invariant(&self); }
        self.raw as usize
    }

    fn try_from_usize(n: usize) -> (r: Option<Self>) {
        if n < 0x8000_0000usize {
            Some(DenseId31 { raw: n as u32 })
        } else {
            None
        }
    }

    fn lt(self, other: Self) -> bool { self.raw < other.raw }

    fn le(self, other: Self) -> bool { self.raw <= other.raw }
}

// ---------------------------------------------------------------------------
// DenseId: the 31-bit id family (production's `define_id31!`). `Index = u32`:
// the storage word is the raw clean value, whose `as_nat` is the identity, so
// it equals `id_nat`. This is the instance that makes a B+tree over `DenseId31`
// store/compare `u32` words while reasoning about the dense `id_nat` model.
// ---------------------------------------------------------------------------

impl DenseId for DenseId31 {
    type Index = u32;

    open spec fn id_nat(self) -> nat {
        self@
    }

    open spec fn id_bound() -> nat {
        DENSE31_BOUND as nat  // 2^31
    }

    fn to_index(self) -> (w: u32) {
        proof { use_type_invariant(&self); }  // raw < 2^31, so as_nat(raw) == raw == self@
        self.raw
    }

    fn as_usize(self) -> (r: usize) {
        proof { use_type_invariant(&self); }
        self.raw as usize
    }

    fn from_usize(n: usize) -> (r: Self) {
        // Mask the stolen bit off so the type invariant (`raw < 2^31`) holds for
        // any `n`. For an in-range `n < 2^31` the mask is a no-op, so the view
        // round-trips; out-of-range `n` is wrapped and carries no guarantee.
        assert(((n as u32) & 0x7fff_ffffu32) < 0x8000_0000u32) by (bit_vector);
        assert(forall|x: u32| #![auto] x < 0x8000_0000u32 ==> (x & 0x7fff_ffffu32) == x)
            by (bit_vector);
        DenseId31 { raw: (n as u32) & 0x7fff_ffffu32 }
    }

    proof fn lemma_id_injective(a: Self, b: Self) {
        // id_nat is the View, which is `raw`; equal views force equal raws.
    }

    proof fn lemma_id_nat_bounded(tracked self) {
        use_type_invariant(&self);  // raw < 2^31 == DENSE31_BOUND == id_bound
    }

    open spec fn is_bit_stealing() -> bool { true }   // MSB stolen for the tag

    proof fn lemma_id_bound_word_relation() {
        // id_bound == 2^31 == DENSE31_BOUND; Index == u32, max_nat == 2^32.
        // 2^31 * 2 == 2^32 (the bit-stealing arm).
    }
}

// ---------------------------------------------------------------------------
// Tagged: Repr = u32 with the tag in bit 31. Every u32 is a valid stored repr
// (`repr_wf := true`), but the niche-injectivity axiom is a real bit_vector
// fact: agreeing on the low 31 bits AND the MSB forces all 32 bits equal.
// ---------------------------------------------------------------------------

impl Tagged for DenseId31 {
    type Repr = u32;

    closed spec fn value_of(r: u32) -> DenseId31 {
        DenseId31 { raw: (r & VAL_MASK) }
    }

    open spec fn tag_of(r: u32) -> bool {
        (r & TAG_BIT) != 0
    }

    open spec fn repr_wf(_r: u32) -> bool {
        true
    }

    proof fn lemma_repr_extensional(r1: u32, r2: u32) {
        // value_of agreement gives r1 & VAL_MASK == r2 & VAL_MASK (equal
        // views); tag_of agreement gives equal MSBs; together all bits agree.
        lemma_value_of_view(r1);
        lemma_value_of_view(r2);
        assert((r1 & VAL_MASK) == (r2 & VAL_MASK));
        assert(((r1 & TAG_BIT) != 0) == ((r2 & TAG_BIT) != 0));
        assert(
            (r1 & 0x7fff_ffffu32) == (r2 & 0x7fff_ffffu32)
                && (((r1 & 0x8000_0000u32) != 0) == ((r2 & 0x8000_0000u32) != 0))
                ==> r1 == r2
        ) by (bit_vector);
    }

    fn into_repr(self) -> (r: u32) {
        proof { use_type_invariant(&self); }  // raw < 2^31
        let x = self.raw;
        // MSB clear ⟹ masking is a no-op and the tag reads false.
        assert(x < 0x8000_0000u32 ==> (x & 0x7fff_ffffu32) == x && (x & 0x8000_0000u32) == 0)
            by (bit_vector);
        proof { lemma_value_of_view(self.raw); }
        self.raw
    }

    fn from_repr(r: &u32) -> (v: DenseId31) {
        // mask the stolen bit off; the result fits in 31 bits.
        assert(((*r) & 0x7fff_ffffu32) < 0x8000_0000u32) by (bit_vector);
        proof { lemma_value_of_view(*r); }
        DenseId31 { raw: *r & 0x7fff_ffffu32 }
    }

    fn tag(r: &u32) -> (b: bool) {
        (*r & 0x8000_0000u32) != 0
    }

    fn set_tag(r: &mut u32) {
        // OR in the MSB: low 31 bits (the value) unchanged, MSB set.
        assert(forall|x: u32|
            #![auto]
            ((x | 0x8000_0000u32) & 0x7fff_ffffu32) == (x & 0x7fff_ffffu32)
                && ((x | 0x8000_0000u32) & 0x8000_0000u32) != 0) by (bit_vector);
        *r = *r | 0x8000_0000u32;
    }

    fn clear_tag(r: &mut u32) {
        // AND off the MSB: low 31 bits unchanged, MSB clear.
        assert(forall|x: u32|
            #![auto]
            ((x & 0x7fff_ffffu32) & 0x7fff_ffffu32) == (x & 0x7fff_ffffu32)
                && ((x & 0x7fff_ffffu32) & 0x8000_0000u32) == 0) by (bit_vector);
        *r = *r & 0x7fff_ffffu32;
    }
}

// ===========================================================================
// DenseId63: the 64-bit analogue (production's `define_id63!`). Same MSB-steal
// encoding one width up: a clean id is a `u64` with bit 63 clear, naming a
// value in `[0, 2^63)`; the stored repr is `u64` with bit 63 carrying the tag.
// This is the second width instance, and proves the `DenseId`/`NodeLayout`
// design is genuinely generic over the 31-bit (u32) and 63-bit (u64) families.
// ===========================================================================

/// The 63-bit value mask (everything but the stolen MSB).
pub spec const VAL_MASK64: u64 = 0x7fff_ffff_ffff_ffff;
/// The stolen tag bit (bit 63).
pub spec const TAG_BIT64: u64 = 0x8000_0000_0000_0000;
/// One past the largest clean 63-bit id (`2^63`).
pub spec const DENSE63_BOUND: u64 = 0x8000_0000_0000_0000;

/// A clean dense id over `u64`: bit 63 always clear, so it names a value in
/// `[0, 2^63)`. The stolen MSB is available to `Tagged` consumers.
#[derive(Copy, Clone)]
pub struct DenseId63 {
    raw: u64,
}

impl View for DenseId63 {
    type V = nat;

    closed spec fn view(&self) -> nat {
        self.raw as nat
    }
}

impl DenseId63 {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.raw < DENSE63_BOUND
    }

    pub fn new(n: u64) -> (r: DenseId63)
        requires n < DENSE63_BOUND,
        ensures r@ == n as nat,
    {
        DenseId63 { raw: n }
    }
}

/// `Default` is id 0 (bit 63 clear, so the type invariant holds). Same rationale
/// as `DenseId31`: required for use as a semi-persistent container's index type
/// (`restore` fills with `Idx::default()`), mirroring production's `define_id63!`.
impl core::default::Default for DenseId63 {
    fn default() -> (r: DenseId63)
        ensures r@ == 0nat,
    {
        DenseId63 { raw: 0 }
    }
}

impl IndexLike for DenseId63 {
    open spec fn as_nat(self) -> nat { self@ }
    open spec fn max_nat() -> nat { DENSE63_BOUND as nat }
    closed spec fn min_spec() -> Self { DenseId63 { raw: 0 } }
    closed spec fn max_spec() -> Self { DenseId63 { raw: 0x7fff_ffff_ffff_ffff } }

    proof fn lemma_as_nat_bounded(tracked self) {
        use_type_invariant(self);  // raw < 2^63 == max_nat()
    }

    proof fn lemma_as_nat_injective(a: Self, b: Self) {
        // as_nat is the identity on raw.
    }

    proof fn lemma_min_as_nat() {}

    proof fn lemma_max_as_nat() {}

    proof fn lemma_max_nat_positive() {}
    proof fn lemma_order_is_as_nat(a: Self, b: Self) {}

    fn min() -> Self { DenseId63 { raw: 0 } }

    fn max() -> Self { DenseId63 { raw: 0x7fff_ffff_ffff_ffff } }

    fn as_usize(self) -> (r: usize) {
        // raw is u32: widening to usize is the identity on any >= 32-bit host,
        // and id_nat() == raw as nat, so the cast meets `r as nat == id_nat()`.
        self.raw as usize
    }

    fn try_from_usize(n: usize) -> (r: Option<Self>) {
        if (n as u64) < 0x8000_0000_0000_0000u64 {
            Some(DenseId63 { raw: n as u64 })
        } else {
            None
        }
    }

    fn lt(self, other: Self) -> bool { self.raw < other.raw }

    fn le(self, other: Self) -> bool { self.raw <= other.raw }
}

impl Tagged for DenseId63 {
    type Repr = u64;

    closed spec fn value_of(r: u64) -> DenseId63 {
        DenseId63 { raw: (r & VAL_MASK64) }
    }

    open spec fn tag_of(r: u64) -> bool {
        (r & TAG_BIT64) != 0
    }

    open spec fn repr_wf(_r: u64) -> bool {
        true
    }

    proof fn lemma_repr_extensional(r1: u64, r2: u64) {
        lemma_value_of_view64(r1);
        lemma_value_of_view64(r2);
        assert((r1 & VAL_MASK64) == (r2 & VAL_MASK64));
        assert(((r1 & TAG_BIT64) != 0) == ((r2 & TAG_BIT64) != 0));
        assert(
            (r1 & 0x7fff_ffff_ffff_ffffu64) == (r2 & 0x7fff_ffff_ffff_ffffu64)
                && (((r1 & 0x8000_0000_0000_0000u64) != 0) == ((r2 & 0x8000_0000_0000_0000u64) != 0))
                ==> r1 == r2
        ) by (bit_vector);
    }

    fn into_repr(self) -> (r: u64) {
        proof { use_type_invariant(&self); }  // raw < 2^63
        let x = self.raw;
        assert(x < 0x8000_0000_0000_0000u64 ==> (x & 0x7fff_ffff_ffff_ffffu64) == x
            && (x & 0x8000_0000_0000_0000u64) == 0) by (bit_vector);
        proof { lemma_value_of_view64(self.raw); }
        self.raw
    }

    fn from_repr(r: &u64) -> (v: DenseId63) {
        assert(((*r) & 0x7fff_ffff_ffff_ffffu64) < 0x8000_0000_0000_0000u64) by (bit_vector);
        proof { lemma_value_of_view64(*r); }
        DenseId63 { raw: *r & 0x7fff_ffff_ffff_ffffu64 }
    }

    fn tag(r: &u64) -> (b: bool) {
        (*r & 0x8000_0000_0000_0000u64) != 0
    }

    fn set_tag(r: &mut u64) {
        assert(forall|x: u64|
            #![auto]
            ((x | 0x8000_0000_0000_0000u64) & 0x7fff_ffff_ffff_ffffu64) == (x & 0x7fff_ffff_ffff_ffffu64)
                && ((x | 0x8000_0000_0000_0000u64) & 0x8000_0000_0000_0000u64) != 0) by (bit_vector);
        *r = *r | 0x8000_0000_0000_0000u64;
    }

    fn clear_tag(r: &mut u64) {
        assert(forall|x: u64|
            #![auto]
            ((x & 0x7fff_ffff_ffff_ffffu64) & 0x7fff_ffff_ffff_ffffu64) == (x & 0x7fff_ffff_ffff_ffffu64)
                && ((x & 0x7fff_ffff_ffff_ffffu64) & 0x8000_0000_0000_0000u64) == 0) by (bit_vector);
        *r = *r & 0x7fff_ffff_ffff_ffffu64;
    }
}

impl DenseId for DenseId63 {
    type Index = u64;

    open spec fn id_nat(self) -> nat {
        self@
    }

    open spec fn id_bound() -> nat {
        DENSE63_BOUND as nat  // 2^63
    }

    fn to_index(self) -> (w: u64) {
        proof { use_type_invariant(&self); }
        self.raw
    }

    fn as_usize(self) -> (r: usize) {
        // raw is u64: on a 64-bit host usize == u64 width, so the cast is the
        // identity on values (usize::MAX == u64::MAX). id_nat() == raw as nat.
        proof { crate::index_like::lemma_u64_usize_64bit(); }
        self.raw as usize
    }

    fn from_usize(n: usize) -> (r: Self) {
        assert(((n as u64) & 0x7fff_ffff_ffff_ffffu64) < 0x8000_0000_0000_0000u64) by (bit_vector);
        assert(forall|x: u64| #![auto] x < 0x8000_0000_0000_0000u64
            ==> (x & 0x7fff_ffff_ffff_ffffu64) == x) by (bit_vector);
        DenseId63 { raw: (n as u64) & 0x7fff_ffff_ffff_ffffu64 }
    }

    proof fn lemma_id_injective(a: Self, b: Self) {
    }

    proof fn lemma_id_nat_bounded(tracked self) {
        use_type_invariant(&self);  // raw < 2^63 == DENSE63_BOUND == id_bound
    }

    open spec fn is_bit_stealing() -> bool { true }   // MSB (bit 63) stolen for the tag

    proof fn lemma_id_bound_word_relation() {
        // id_bound == 2^63 == DENSE63_BOUND; Index == u64, max_nat == 2^64.
        // 2^63 * 2 == 2^64 (the bit-stealing arm).
    }
}

/// `DenseId63`'s `value_of`-to-view bridge (the 64-bit analogue of
/// [`lemma_value_of_view`]).
pub proof fn lemma_value_of_view64(r: u64)
    ensures <DenseId63 as Tagged>::value_of(r)@ == (r & VAL_MASK64) as nat,
{
}

/// Bridges the opaque `value_of` constructor to its view: the dense index of
/// `value_of(r)` is the masked word. Proved inside the module, where the
/// `DenseId31` constructor and `View` body are transparent.
pub proof fn lemma_value_of_view(r: u32)
    ensures <DenseId31 as Tagged>::value_of(r)@ == (r & VAL_MASK) as nat,
{
    // value_of(r) == DenseId31 { raw: r & VAL_MASK }, whose view is its raw.
}

/// End-to-end witness that `DenseId31` serves *both* trait roles at once: an
/// `InlineStore` indexed by `DenseId31` (its `IndexLike` side) and storing
/// `DenseId31` values with the capture bit packed inline (its `Tagged` side).
/// A freshly-built such store is `DiffStore`-well-formed — so the unification
/// composes through the store's `T: Tagged, I: IndexLike` bounds with one type
/// filling both, exactly as production's `define_id31!` ids do.
pub fn lemma_dense_id31_indexes_and_stores_itself() -> (s: InlineStore<DenseId31, DenseId31>)
    ensures DiffStore::<DenseId31, DenseId31, true>::wf(&s),
{
    InlineStore::<DenseId31, DenseId31>::new::<true>()
}

} // verus!
