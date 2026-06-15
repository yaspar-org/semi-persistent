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
//! encoding, not the `BoolPair` fallback's vacuous `repr_wf := true`:
//!   - **`Tagged`**: the niche axiom `lemma_repr_extensional` is a genuine
//!     `bit_vector` theorem (equal low-31 bits and equal MSB force word
//!     equality), and `into_repr`/`set_tag`/`clear_tag` carry their
//!     value-preservation ensures through the masks.
//!   - **`IndexLike`**: `as_nat` is the identity on the clean value (so
//!     injectivity is immediate), and the `[0, 2^31)` bound — which the
//!     `BoolPair`/primitive impls get structurally — comes from the type
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
