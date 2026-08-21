// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Canonical key wrappers for float and rational `SpMap` keys.
//!
//! vstd's hash-table key model requires `==` classes to be singletons up to
//! value identity (requirement (2), see `external_specs.rs`). The natural
//! foreign key types FAIL that requirement — `OrderedFloat<f64>` puts every
//! NaN bit pattern (and ±0.0) in one `==` class; `num_rational::BigRational`
//! reaches non-reduced representations via `Ratio::new_raw` and compares
//! them equal, so their `obeys_key_model` axioms would be false. These wrappers
//! restore float/rational keying
//! by making requirement (2) TRUE BY CONSTRUCTION: each constructor
//! canonicalizes, so exactly one representation per mathematical value is
//! reachable, and the derived structural `Eq`/`Hash` over that canonical
//! representation is value identity.
//!
//! - [`CanonicalF64`]: the value IS a canonicalized bit pattern (`u64`) —
//!   all NaNs collapse to the one quiet-NaN encoding, `-0.0` to `+0.0`.
//!   `==` compares the bits; two equal keys are bit-identical structs.
//!   Requirement (2) holds with NO foreign-code dependence at all.
//! - [`CanonicalRational`]: reduced numerator/denominator `BigInt` pair
//!   with a positive denominator, produced by `Ratio::new` (which reduces
//!   and normalizes sign — the only constructor). Derived `Eq`/`Hash` are
//!   structural over `BigInt`, whose structural-eq-over-normalized-digits
//!   property is the (credible) `ExBigInt` axiom. One representation per
//!   rational ⟹ requirement (2).
//!
//! The `obeys_key_model` axioms for these types live in
//! `external_specs.rs` next to the BigInt/BigUint ones; requirement-level
//! fuzz tests in `tests/compat_map.rs::literal_keys` exercise all four.
//! Intended consumers (the e-graph's `NiraLitVal::Rat` interning and the
//! model's f64 literals) convert at their boundary — a conversion bug
//! mis-keys that caller's value but can never invalidate the container's
//! verified theorems. See `doc/future/key-model-tcb.md`.
//!
//! Plain Rust, outside `verus!` — these are exec value types; Verus sees
//! them only through the opaque type registrations in `external_specs.rs`.

use num_bigint::BigInt;
use num_rational::BigRational;

/// The single canonical NaN encoding every NaN input collapses to
/// (positive quiet NaN, zero payload — the value `f64::NAN` on all Rust
/// platforms we target; pinned as a constant so canonicalization does not
/// depend on which NaN `f64::NAN` happens to be).
const CANONICAL_NAN_BITS: u64 = 0x7ff8_0000_0000_0000;

/// An `f64` under canonical-bit identity: a hash key whose `==` IS bit
/// identity of a canonicalized representation.
///
/// Canonicalization (in [`CanonicalF64::new`], the only constructor):
/// every NaN → [`CANONICAL_NAN_BITS`]; `-0.0` → `+0.0`; every other value
/// keeps its (already unique) IEEE-754 encoding. So distinct reachable
/// `CanonicalF64`s are distinct mathematical values, and `==` classes are
/// singletons — vstd key-model requirement (2) by construction.
///
/// ## Compatibility fold, not a semantic endorsement
///
/// Folding NaNs together and `-0.0` onto `+0.0` reproduces what
/// `OrderedFloat<f64>` keys do in the e-graph interner. This preserves the
/// existing key identity, but it is NOT the right float-term identity for the
/// e-graph long term: with ±0.0 in one
/// e-class, congruence + constant folding over the model's `f64::/` merges
/// `+inf` with `-inf` (`1.0/0.0` vs `1.0/-0.0`), and `f64::neg(0.0) ≡ 0.0`
/// — a model-layer unsoundness inherited from that key identity. The semantic
/// fix is [`BitsF64`] (bit-exact, no fold), with
/// any identification you actually want expressed as rewrite rules scoped
/// to specific operators. The fold is pinned by
/// compliance tests (`canonical_key_model::canonical_f64_fold_is_pinned`);
/// see `doc/future/key-model-tcb.md` §float-semantics.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct CanonicalF64 {
    bits: u64,
}

impl CanonicalF64 {
    /// Canonicalize and wrap. Total: NaNs and signed zeros are folded onto
    /// their canonical representative, everything else is injective.
    pub fn new(value: f64) -> CanonicalF64 {
        let bits = if value.is_nan() {
            CANONICAL_NAN_BITS
        } else if value == 0.0 {
            0.0f64.to_bits() // folds -0.0 onto +0.0
        } else {
            value.to_bits()
        };
        CanonicalF64 { bits }
    }

    /// The wrapped value (NaN inputs come back as the canonical quiet NaN;
    /// `-0.0` comes back as `+0.0`).
    pub fn get(self) -> f64 {
        f64::from_bits(self.bits)
    }

    /// The canonical bit pattern (the identity `Eq`/`Hash` compare).
    pub fn bits(self) -> u64 {
        self.bits
    }
}

impl core::fmt::Display for CanonicalF64 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.get())
    }
}

impl From<f64> for CanonicalF64 {
    fn from(v: f64) -> Self {
        CanonicalF64::new(v)
    }
}

/// An `f64` under RAW-bit identity: injective by construction — no fold,
/// no normalization argument, no dependence on float semantics at all.
/// Distinct NaN payloads are distinct keys; `-0.0` and `+0.0` are distinct
/// keys. The strongest possible fit for vstd key-model requirement (2)
/// (`==` is derived bit equality of the single `u64` field, so `==`
/// classes are singletons trivially), and the long-term float-literal key
/// for the e-graph: term identity = bit identity, with any semantic
/// identification (±0.0, NaN classes) expressed as per-operator rewrite
/// rules where it is visible and scoped, not in the key layer. See
/// [`CanonicalF64`]'s doc for why the compatibility wrapper exists.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct BitsF64 {
    bits: u64,
}

impl BitsF64 {
    /// Wrap the exact bit pattern. Total and injective.
    pub fn new(value: f64) -> BitsF64 {
        BitsF64 {
            bits: value.to_bits(),
        }
    }

    /// The exact value back (bit-for-bit, NaN payload preserved).
    pub fn get(self) -> f64 {
        f64::from_bits(self.bits)
    }

    /// The raw bit pattern (the identity `Eq`/`Hash` compare).
    pub fn bits(self) -> u64 {
        self.bits
    }
}

impl core::fmt::Display for BitsF64 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.get())
    }
}

impl From<f64> for BitsF64 {
    fn from(v: f64) -> Self {
        BitsF64::new(v)
    }
}

/// A rational number in canonical (reduced, positive-denominator) form:
/// the hash-key replacement for `BigRational`.
///
/// The only constructors go through [`num_rational::Ratio::new`], which
/// reduces by the gcd and normalizes the sign onto the numerator — so
/// exactly one `(numer, denom)` pair is reachable per rational value, and
/// the derived structural `Eq`/`Hash` (over `BigInt`'s normalized digit
/// representation) is value identity: vstd key-model requirement (2) by
/// construction. (`BigRational` itself fails it: `Ratio::new_raw` reaches
/// `2/4`, which its mathematical `==` conflates with `1/2`.)
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct CanonicalRational {
    numer: BigInt,
    denom: BigInt,
}

impl CanonicalRational {
    /// Canonicalize `numer/denom`. Panics if `denom` is zero (as
    /// `BigRational::new` does — rationals have no zero denominator).
    pub fn new(numer: BigInt, denom: BigInt) -> CanonicalRational {
        Self::from_rational(&BigRational::new(numer, denom))
    }

    /// Canonicalize an existing `BigRational` (reduces it if it was built
    /// via `new_raw`; already-reduced values are copied as-is).
    pub fn from_rational(r: &BigRational) -> CanonicalRational {
        let reduced = r.reduced();
        CanonicalRational {
            numer: reduced.numer().clone(),
            denom: reduced.denom().clone(),
        }
    }

    /// Back to `BigRational` (already reduced; `new` just re-checks).
    pub fn to_rational(&self) -> BigRational {
        BigRational::new(self.numer.clone(), self.denom.clone())
    }

    /// The reduced numerator (sign lives here).
    pub fn numer(&self) -> &BigInt {
        &self.numer
    }

    /// The reduced, strictly positive denominator.
    pub fn denom(&self) -> &BigInt {
        &self.denom
    }
}

impl core::fmt::Display for CanonicalRational {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}/{}", self.numer, self.denom)
    }
}

impl From<BigRational> for CanonicalRational {
    fn from(r: BigRational) -> Self {
        CanonicalRational::from_rational(&r)
    }
}

impl From<CanonicalRational> for BigRational {
    fn from(c: CanonicalRational) -> Self {
        c.to_rational()
    }
}
