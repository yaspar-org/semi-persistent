// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Assumed key-model facts for external literal types (trust ledger group D).
//!
//! `SpMap<K, V>` requires vstd's hash-table key model for its key type:
//! `obeys_key_model::<K>()` — (1) `Hash` is deterministic, (2) two keys are
//! IDENTICAL if and only if the executable `==` considers them equal, and
//! (3) `clone()` produces a result identical to its input
//! (`vstd::std_specs::hash`, stated in prose on the `uninterp` spec fn).
//! vstd ships broadcast axioms for the primitive types and `Box`es thereof;
//! any other key type must state the assumption itself.
//!
//! Requirement (2) is the sharp one: it demands that the Rust `==` equality
//! classes be SINGLETONS up to value identity — determinism of `Eq`/`Hash`
//! is NOT sufficient. A type whose `==` identifies distinct representations
//! does NOT obey the key model, no matter how deterministic it is.
//!
//! ## Types covered here (and why the assumption is credible)
//!
//! - `num_bigint::BigInt` / `num_bigint::BigUint`: `eq` is STRUCTURAL —
//!   `BigUint::eq` is `self.data == other.data` (digit-vector equality) and
//!   `BigInt::eq` is `sign == sign && data == data` — over a normalization
//!   invariant (no trailing zero limbs; `NoSign` iff zero) that every public
//!   constructor maintains and the impls `debug_assert!`. Structural
//!   equality of a canonical representation IS value identity, so
//!   requirement (2) holds as long as the normalization invariant does.
//!   `Hash` hashes the same normalized fields; `Clone` is derived
//!   (field-wise). Assumed, not proved — foreign code — but the assumption
//!   reduces to "num-bigint maintains its own documented invariant".
//!
//! ## Types deliberately NOT covered (axioms would be FALSE)
//!
//! - `ordered_float::OrderedFloat<f64>`: `eq` treats ALL NaN bit patterns as
//!   equal (`if self.0.is_nan() { other.0.is_nan() }`) — distinct,
//!   non-identical values (different payload/sign/signaling bits) in one
//!   `==` class. Violates requirement (2) outright.
//! - `num_rational::BigRational` (= `Ratio<BigInt>`): `eq` is mathematical
//!   comparison (`self.cmp(other) == Equal`), and `Ratio::new_raw` makes
//!   non-reduced values reachable, so raw `2/4 == 1/2` with non-identical
//!   representations. The crate's own `Hash` impl comment says it must
//!   "agree with `Eq` even for non-reduced ratios" — the equality classes
//!   are non-singleton by design. Violates requirement (2).
//!
//! Consumers needing float or rational keys use the crate-local canonical
//! wrappers in [`crate::canonical_keys`] — [`CanonicalF64`] (canonical-NaN /
//! zero-normalized bits) and [`CanonicalRational`] (reduced, positive-
//! denominator pair) — whose constructors make requirement (2) hold by
//! construction. Their axioms are below, with the credibility argument per
//! type. `doc/future/key-model-tcb.md` records the further endgame
//! (verified index) that would remove even these.
//!
//! [`CanonicalF64`]: crate::canonical_keys::CanonicalF64
//! [`CanonicalRational`]: crate::canonical_keys::CanonicalRational
//!
//! Feature-gated behind `literal-types` so the default build carries no
//! external-crate assumptions: `cargo verus verify` must pass both with and
//! without the feature (migration plan, validation matrix).
//!
//! Runtime validation: `tests/compat_map.rs::literal_keys` fuzzes the
//! key-model requirements themselves for the covered types (eq ⟹
//! byte-identical representation, hash determinism, clone
//! byte-identity) and carries regression tests DEMONSTRATING the
//! requirement-(2) violations of the excluded types, so the exclusions
//! stay justified against future crate upgrades.

use vstd::prelude::*;
// `std_specs::hash` is spec-only; vstd gates it behind `cfg(verus_keep_ghost)`
// (set by the Verus driver, not by plain cargo), so mirror the gate here —
// the whole module body is ghost anyway (axioms only).
#[cfg(verus_keep_ghost)]
use vstd::std_specs::hash::obeys_key_model;

verus! {

// -------------------------------------------------------------------------
// Type registrations. `external_type_specification` + `external_body` tells
// Verus the type exists and is opaque (no fields visible to specs) — the
// minimum needed to even NAME the type in a spec. No semantics is assumed
// here; the key-model facts below are the only axioms.
// -------------------------------------------------------------------------

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)] // registration marker; the wrapped field is never read
pub struct ExBigInt(num_bigint::BigInt);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExBigUint(num_bigint::BigUint);

/// `num_bigint::BigInt` obeys the hash-table key model: `eq` is structural
/// (`sign` + digit vector) over the crate's normalization invariant, so `==`
/// classes are singletons up to identity; `Hash` hashes the same normalized
/// fields; `Clone` is field-wise. See the module doc for the full argument.
pub broadcast axiom fn axiom_bigint_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<num_bigint::BigInt>(),
;

/// `num_bigint::BigUint` obeys the hash-table key model: `eq` is
/// `self.data == other.data` over the no-trailing-zero-limbs invariant.
pub broadcast axiom fn axiom_biguint_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<num_bigint::BigUint>(),
;

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExCanonicalF64(crate::canonical_keys::CanonicalF64);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExCanonicalRational(crate::canonical_keys::CanonicalRational);

#[verifier::external_type_specification]
#[verifier::external_body]
#[allow(dead_code)]
pub struct ExBitsF64(crate::canonical_keys::BitsF64);

/// `CanonicalF64` obeys the hash-table key model. The strongest axiom of
/// the group: the type is a crate-local `struct { bits: u64 }` whose only
/// constructor canonicalizes (all NaNs → one encoding, -0.0 → +0.0), and
/// `Eq`/`Hash` are DERIVED over the single `u64` field — so `==` is
/// literally bit identity of the struct. No foreign code is involved in
/// its equality at all; the axiom is trusted only because
/// `obeys_key_model` is `uninterp` (no proof can conclude it for ANY
/// type, including this one).
pub broadcast axiom fn axiom_canonical_f64_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<crate::canonical_keys::CanonicalF64>(),
;

/// `CanonicalRational` obeys the hash-table key model: constructors
/// canonicalize through `Ratio::new` (reduced, positive denominator), so
/// one representation per rational is reachable, and the derived
/// structural `Eq`/`Hash` over `BigInt` fields is value identity — the
/// same normalized-`BigInt` argument as `axiom_bigint...` above, plus the
/// crate-local canonicalization invariant. (Contrast raw `BigRational`,
/// which VIOLATES requirement (2) and gets no axiom.)
pub broadcast axiom fn axiom_canonical_rational_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<crate::canonical_keys::CanonicalRational>(),
;

/// `BitsF64` obeys the hash-table key model: raw-bit injective wrapper
/// (`struct { bits: u64 }`, constructor is `to_bits` verbatim, derived
/// `Eq`/`Hash` over the field) — `==` classes are singletons trivially,
/// with no fold and no float-semantics dependence. The long-term
/// float-literal key (see canonical_keys.rs for the CanonicalF64-vs-
/// BitsF64 migration sequencing).
pub broadcast axiom fn axiom_bits_f64_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<crate::canonical_keys::BitsF64>(),
;

/// Group D as one obligation: broadcast-use this to make `SpMap::new`'s
/// `obeys_key_model::<K>()` precondition dischargeable for the covered
/// literal key types at once.
pub broadcast group group_literal_key_axioms {
    axiom_bigint_obeys_hash_table_key_model,
    axiom_biguint_obeys_hash_table_key_model,
    axiom_canonical_f64_obeys_hash_table_key_model,
    axiom_canonical_rational_obeys_hash_table_key_model,
    axiom_bits_f64_obeys_hash_table_key_model,
}

} // verus!

// ---------------------------------------------------------------------------
// The consumer-facing forcing function (doc/future/key-model-tcb.md, Option
// B): any crate introducing a NEW SpMap key type must go through this macro.
//
// The forcing already exists structurally — `SpMap::new` carries `requires
// obeys_key_model::<K>()` and the predicate is `uninterp`, so a verified
// caller with an unblessed type CANNOT discharge it except by stating an
// axiom. This macro makes that unavoidable act reviewed, justified, and
// fuzzed instead of ad hoc:
//
//   - the axiom fn must be named with the `axiom_key_model_` prefix (the
//     macro pins it by pattern); CI can grep that every such axiom in the
//     workspace came from this macro and carries a justification;
//   - the justification string is a REQUIRED argument, embedded in the
//     generated docs;
//   - a runtime test (caller-named, same file) is generated alongside,
//     fuzzing the three vstd key-model requirements over a caller-supplied
//     deterministic generator and a caller-supplied REPRESENTATION
//     OBSERVABLE — the falsifiable projection of "identity": requirement
//     (2) demands values that compare `==` be identical, so they must agree
//     on every representation observable.
//
// The generated test cannot PROVE the axiom (nothing can — the predicate
// is uninterp, and fuzzing samples), but it falsifies the common failure
// modes: `==` classes that identify distinct representations (the exact
// bug that sank the OrderedFloat/BigRational axioms), nondeterministic
// hashing, and non-identical clones.
// ---------------------------------------------------------------------------

/// Declare (and take ownership of) the assumption that `$Key` obeys vstd's
/// hash-table key model, generating the axiom plus its requirement-level
/// fuzz test.
///
/// ```ignore
/// semi_persistent_containers_verus::declare_key_model_assumption! {
///     key = my_crate::BigDecimal;
///     axiom = axiom_key_model_bigdecimal;      // prefix enforced
///     test = key_model_fuzz_bigdecimal;
///     justification = "Eq/Hash are derived structural over the normalized \
///                      (mantissa, scale) pair; constructor normalizes";
///     generator = |raw: u64| my_crate::BigDecimal::from_seed(raw);
///     observable = |v: &my_crate::BigDecimal| format!("{v:?}");
/// }
/// ```
///
/// - `generator`: builds a value from a raw `u64` (driven by a seeded LCG;
///   failures replay from the printed seed). It SHOULD reach values through
///   diverse construction paths — the generator's coverage is the test's
///   coverage.
/// - `observable`: a projection two values agree on IFF they have the same
///   representation (byte encoding, canonical fields, or `Debug` when it
///   prints every field). Requirement (2) is falsified when `a == b` but
///   the observables differ.
#[macro_export]
macro_rules! declare_key_model_assumption {
    (
        key = $Key:ty;
        axiom = $axiom:ident;
        test = $test:ident;
        justification = $just:expr;
        generator = $gen:expr;
        observable = $obs:expr;
    ) => {
        // Compile-time prefix check: the axiom name must start with
        // `axiom_key_model_` so CI's grep convention holds. (Pattern-matched
        // here by requiring the caller to write the full name; the const
        // assertion pins the prefix.)
        const _: () = {
            let name = stringify!($axiom).as_bytes();
            let prefix = b"axiom_key_model_";
            if name.len() < prefix.len() {
                panic!(
                    "declare_key_model_assumption!: axiom name must start with axiom_key_model_"
                );
            }
            let mut i = 0;
            while i < prefix.len() {
                if name[i] != prefix[i] {
                    panic!(
                        "declare_key_model_assumption!: axiom name must start with axiom_key_model_"
                    );
                }
                i += 1;
            }
        };

        // Hidden module gives the verus!{} expansion the vstd prelude it
        // needs without polluting the invoker's namespace (the
        // define_id_impl! pattern from id_macros.rs).
        #[doc(hidden)]
        mod $axiom {
            #[allow(unused_imports)]
            use ::vstd::prelude::*;

            verus! {

            /// ASSUMED key-model fact (trust-ledger group D shape) for `
            #[doc = stringify!($Key)]
            /// `, declared via `declare_key_model_assumption!`.
            ///
            /// Justification:
            #[doc = $just]
            pub broadcast axiom fn $axiom()
                ensures
                    #[trigger] ::vstd::std_specs::hash::obeys_key_model::<$Key>(),
            ;

            } // verus!
        }
        // The axiom fn is GHOST: plain cargo builds erase it (the verus!
        // macro drops ghost items), so the re-export must be gated to the
        // Verus driver. Verified code names the axiom via this re-export;
        // cargo sees only the (empty) module.
        #[cfg(verus_keep_ghost)]
        pub use $axiom::$axiom;

        /// Generated requirement-level fuzz for the axiom of the same name.
        /// Deterministic LCG over seeds 0..8, 512 values each; failures
        /// replay exactly.
        #[test]
        fn $test() {
            use ::std::hash::{DefaultHasher, Hash, Hasher};
            fn hash_of<K: Hash>(k: &K) -> u64 {
                let mut h = DefaultHasher::new();
                k.hash(&mut h);
                h.finish()
            }
            let generate = $gen;
            let observe = $obs;
            for seed in 0u64..8 {
                let mut s: u64 = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
                let mut raw = move || {
                    s = s
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    s >> 1
                };
                let mut pool: ::std::vec::Vec<$Key> = ::std::vec::Vec::new();
                for i in 0..512usize {
                    let v: $Key = generate(raw());
                    // req (1): hash determinism across calls.
                    assert_eq!(
                        hash_of(&v),
                        hash_of(&v),
                        "seed {seed} value {i}: hash nondeterministic"
                    );
                    // req (3): clone identity (hash + observable agree).
                    let c = v.clone();
                    assert!(c == v, "seed {seed} value {i}: clone not equal");
                    assert_eq!(
                        hash_of(&c),
                        hash_of(&v),
                        "seed {seed} value {i}: clone hashes differently"
                    );
                    assert_eq!(
                        observe(&c),
                        observe(&v),
                        "seed {seed} value {i}: clone representation differs"
                    );
                    pool.push(v);
                }
                // req (2): across the pool, == iff identical representation
                // observable, and == implies equal hash.
                for a in 0..pool.len() {
                    for b in (a + 1)..pool.len() {
                        let eq = pool[a] == pool[b];
                        let same_repr = observe(&pool[a]) == observe(&pool[b]);
                        assert_eq!(
                            eq, same_repr,
                            "seed {seed} pair ({a},{b}): == disagrees with representation \
                             identity — key-model requirement (2) violated"
                        );
                        if eq {
                            assert_eq!(
                                hash_of(&pool[a]),
                                hash_of(&pool[b]),
                                "seed {seed} pair ({a},{b}): eq but hash differs"
                            );
                        }
                    }
                }
            }
        }
    };
}
