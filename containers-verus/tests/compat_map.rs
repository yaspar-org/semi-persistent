// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Ported production compatibility test: `containers/tests/map_proptest.rs`.
//!
//! Exercises Clone (String) keys, overwrite-shadow semantics, `get_by_key`,
//! and mark/restore with index rebuild. Uses the verus name `SpMap`
//! (production `Map` collides with `vstd::map::Map`). Gated on
//! `compat-composites`.
use proptest::prelude::*;
use semi_persistent_containers_verus::{MapToken, ShrinkPolicy, SpMap};

#[derive(Clone, Debug)]
enum Op {
    Insert(String, u32),
    GetByKey(String),
    Mark,
    Restore(usize),
}

fn op_strategy() -> impl Strategy<Value = Op> {
    let key = "[a-z]{1,4}";
    prop_oneof![
        50 => (key, any::<u32>()).prop_map(|(k, v)| Op::Insert(k, v)),
        30 => key.prop_map(Op::GetByKey),
        15 => Just(Op::Mark),
        10 => any::<usize>().prop_map(Op::Restore),
    ]
}

fn run_ops(ops: Vec<Op>) {
    let mut m = SpMap::<String, u32, usize, true>::new();
    let mut oracle = std::collections::HashMap::<String, u32>::new();
    let mut snapshots: Vec<(MapToken, std::collections::HashMap<String, u32>)> = Vec::new();

    for op in ops {
        match op {
            Op::Insert(key, val) => {
                m.try_insert(key.clone(), val).expect("compat: capacity");
                oracle.insert(key, val);
            }
            Op::GetByKey(key) => {
                let got = m.get_by_key(&key).copied();
                let expected = oracle.get(&key).copied();
                assert_eq!(got, expected, "get mismatch for key {key:?}");
            }
            Op::Mark => {
                if snapshots.len() >= 20 {
                    continue;
                }
                let token = m
                    .try_mark(ShrinkPolicy::Never)
                    .expect("compat: depth in bounds");
                snapshots.push((token, oracle.clone()));
            }
            Op::Restore(idx) => {
                if snapshots.is_empty() {
                    continue;
                }
                let idx = idx % snapshots.len();
                let (token, snap) = snapshots[idx].clone();
                m.try_restore(token).expect("compat: own live token");
                oracle = snap;
                snapshots.truncate(idx);
            }
        }
    }

    // Final consistency: every oracle key is in the map with the right value,
    // and the live-key count agrees.
    assert_eq!(m.len(), oracle.len(), "final live-key count mismatch");
    assert_eq!(m.is_empty(), oracle.is_empty());
    for (k, v) in &oracle {
        assert_eq!(m.get_by_key(k), Some(v), "final mismatch for key {k:?}");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    #[test]
    fn map_proptest(ops in proptest::collection::vec(op_strategy(), 1..300)) {
        run_ops(ops);
    }
}

// ---------------------------------------------------------------------------
// Literal-key tests (trust ledger group D, feature `literal-types`).
//
// Two layers:
//  1. `literal_keys` — for the types src/external_specs.rs ASSUMES obey the
//     key model (BigInt/BigUint): an SpMap-vs-HashMap oracle trace, plus
//     fuzz tests of the key-model requirements THEMSELVES (the assumed
//     facts): eq-coherence across construction paths, hash determinism,
//     clone identity, observable-representation agreement. The oracle trace
//     alone cannot detect an identity/== mismatch (both maps use the same
//     Eq/Hash), which is why the requirement-level fuzzing exists.
//  2. `key_model_violations` — regression tests DEMONSTRATING that
//     OrderedFloat<f64> and BigRational violate vstd requirement (2)
//     (identity iff ==): non-identical representations that compare equal.
//     These document why those types get NO axiom; if a future crate
//     upgrade changes the semantics, these tests fail and the exclusion
//     must be re-reviewed. Not feature-gated (dev-deps only).
// ---------------------------------------------------------------------------

#[cfg(feature = "literal-types")]
mod literal_keys {
    use num_bigint::{BigInt, BigUint, Sign};
    use semi_persistent_containers_verus::{ShrinkPolicy, SpMap};
    use std::collections::HashMap;
    use std::hash::{DefaultHasher, Hash, Hasher};

    fn hash_of<K: Hash>(k: &K) -> u64 {
        let mut h = DefaultHasher::new();
        k.hash(&mut h);
        h.finish()
    }

    /// Deterministic LCG (fixed seeds; failures replay exactly).
    struct Lcg(u64);
    impl Lcg {
        fn new(seed: u64) -> Self {
            Lcg(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1))
        }
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 1
        }
    }

    fn exercise<K: Clone + Hash + Eq + std::fmt::Debug>(keys: Vec<K>) {
        let mut m: SpMap<K, u64, usize, true> = SpMap::new();
        let mut oracle: HashMap<K, u64> = HashMap::new();

        for (i, k) in keys.iter().enumerate() {
            m.try_insert(k.clone(), i as u64).expect("compat: capacity");
            oracle.insert(k.clone(), i as u64);
        }
        let snap = oracle.clone();
        let tok = m
            .try_mark(ShrinkPolicy::Never)
            .expect("compat: depth in bounds");
        for (i, k) in keys.iter().enumerate().filter(|(i, _)| i % 2 == 0) {
            m.try_insert(k.clone(), (i as u64) + 1000)
                .expect("compat: capacity");
            oracle.insert(k.clone(), (i as u64) + 1000);
        }
        assert_eq!(m.len(), oracle.len());
        for (k, v) in &oracle {
            assert_eq!(
                m.get_by_key(k),
                Some(v),
                "post-overwrite mismatch for {k:?}"
            );
        }
        m.try_restore(tok).expect("compat: own live token");
        assert_eq!(m.len(), snap.len());
        for (k, v) in &snap {
            assert_eq!(m.get_by_key(k), Some(v), "post-restore mismatch for {k:?}");
        }
    }

    /// Random `BigInt` from random byte strings (random construction path).
    fn rand_bigint(rng: &mut Lcg) -> BigInt {
        let len = 1 + (rng.next() as usize % 24);
        let bytes: Vec<u8> = (0..len).map(|_| rng.next() as u8).collect();
        let sign = match rng.next() % 3 {
            0 => Sign::Minus,
            1 => Sign::Plus,
            _ => Sign::NoSign,
        };
        // from_bytes_be normalizes (NoSign forces zero, leading zeros drop).
        if sign == Sign::NoSign {
            BigInt::from(0)
        } else {
            BigInt::from_bytes_be(sign, &bytes)
        }
    }

    #[test]
    fn bigint_keys_oracle() {
        exercise(
            (0..64)
                .map(|i| BigInt::from(i) * BigInt::from(i64::MAX) - BigInt::from(7 * i))
                .collect(),
        );
    }

    #[test]
    fn biguint_keys_oracle() {
        exercise(
            (0u32..64)
                .map(|i| BigUint::from(i) * BigUint::from(u64::MAX) + BigUint::from(i))
                .collect(),
        );
    }

    /// Key-model requirement (1): Hash is deterministic — equal hashes across
    /// repeated calls and across clones.
    #[test]
    fn bigint_key_model_hash_determinism() {
        let mut rng = Lcg::new(0x00D3_7E12);
        for _ in 0..2_000 {
            let x = rand_bigint(&mut rng);
            let h1 = hash_of(&x);
            let h2 = hash_of(&x);
            let h3 = hash_of(&x.clone());
            assert_eq!(h1, h2, "hash nondeterministic for {x}");
            assert_eq!(h1, h3, "clone hashes differently for {x}");
        }
    }

    /// Key-model requirement (2), the sharp one: `==` classes must be
    /// singletons up to identity. For BigInt, exec eq is structural
    /// (sign + digit vector) over the normalization invariant, so the
    /// falsifiable observable is: values that compare `==` must agree on
    /// EVERY observable of the representation (sign, byte encoding, Debug),
    /// no matter how differently they were constructed. Each round builds
    /// the same mathematical value through arithmetic detours (x + r - r,
    /// x * 1, shifts up and back down, decimal round-trip) — the paths that
    /// would expose a normalization failure (trailing zero limbs / stale
    /// sign) as an eq/representation mismatch.
    #[test]
    fn bigint_key_model_eq_is_identity() {
        let mut rng = Lcg::new(0x001D_EA11);
        for round in 0..2_000 {
            let x = rand_bigint(&mut rng);
            let r = rand_bigint(&mut rng);
            let variants = [
                x.clone(),
                &x + &r - &r,
                &x * BigInt::from(1),
                (&x << 64u32) >> 64u32,
                x.to_string().parse::<BigInt>().unwrap(),
            ];
            for v in &variants {
                assert_eq!(*v, x, "round {round}: same value not eq");
                assert_eq!(
                    v.to_signed_bytes_le(),
                    x.to_signed_bytes_le(),
                    "round {round}: eq but representations differ (== class not a singleton)"
                );
                assert_eq!(v.sign(), x.sign(), "round {round}: eq but sign differs");
                assert_eq!(
                    hash_of(v),
                    hash_of(&x),
                    "round {round}: eq but hash differs"
                );
            }
        }
    }

    /// Key-model requirement (3): clone is identical to its input — same
    /// eq, same hash, same observable representation.
    #[test]
    fn bigint_key_model_clone_identity() {
        let mut rng = Lcg::new(0xC10E);
        for _ in 0..2_000 {
            let x = rand_bigint(&mut rng);
            let c = x.clone();
            assert_eq!(c, x);
            assert_eq!(c.to_signed_bytes_le(), x.to_signed_bytes_le());
            assert_eq!(hash_of(&c), hash_of(&x));
        }
    }

    /// Same three requirements for BigUint, in one sweep.
    #[test]
    fn biguint_key_model_requirements() {
        let mut rng = Lcg::new(0x00B1_6017);
        for round in 0..2_000 {
            let len = 1 + (rng.next() as usize % 24);
            let bytes: Vec<u8> = (0..len).map(|_| rng.next() as u8).collect();
            let x = BigUint::from_bytes_be(&bytes);
            let r = BigUint::from(rng.next());
            let variants = [
                x.clone(),
                &x + &r - &r,
                (&x << 64u32) >> 64u32,
                x.to_string().parse::<BigUint>().unwrap(),
            ];
            for v in &variants {
                assert_eq!(*v, x, "round {round}: same value not eq");
                assert_eq!(
                    v.to_bytes_le(),
                    x.to_bytes_le(),
                    "round {round}: eq but representations differ"
                );
                assert_eq!(
                    hash_of(v),
                    hash_of(&x),
                    "round {round}: eq but hash differs"
                );
            }
            assert_eq!(hash_of(&x), hash_of(&x), "hash nondeterministic");
        }
    }
}

/// Requirement-(2) VIOLATION regressions for the excluded types. These are
/// expected to keep passing — they assert the violation EXISTS. If a crate
/// upgrade makes one fail, the exclusion in src/external_specs.rs must be
/// re-reviewed (the type may have become axiomatizable).
mod key_model_violations {
    use num_bigint::BigInt;
    use num_rational::{BigRational, Ratio};
    use ordered_float::OrderedFloat;

    /// Two NaN bit patterns: non-identical representations, one `==` class.
    #[test]
    fn ordered_float_nan_violates_identity_iff_eq() {
        let quiet = OrderedFloat(f64::NAN);
        let payload = OrderedFloat(f64::from_bits(f64::NAN.to_bits() ^ 0x1));
        assert_ne!(
            quiet.0.to_bits(),
            payload.0.to_bits(),
            "need two distinct NaN representations"
        );
        assert_eq!(
            quiet, payload,
            "OrderedFloat: distinct NaN representations compare equal — \
             vstd requirement (2) violated; no obeys_key_model axiom possible"
        );
    }

    /// Signed zero: -0.0 and +0.0 are distinct representations, one class.
    #[test]
    fn ordered_float_signed_zero_violates_identity_iff_eq() {
        let pos = OrderedFloat(0.0f64);
        let neg = OrderedFloat(-0.0f64);
        assert_ne!(pos.0.to_bits(), neg.0.to_bits());
        assert_eq!(pos, neg, "OrderedFloat: ±0.0 compare equal");
    }

    /// `new_raw` non-reduced ratio: 2/4 == 1/2 with different fields.
    #[test]
    fn bigrational_new_raw_violates_identity_iff_eq() {
        let reduced = BigRational::new(BigInt::from(1), BigInt::from(2));
        let raw = Ratio::new_raw(BigInt::from(2), BigInt::from(4));
        assert_ne!(reduced.numer(), raw.numer(), "representations differ");
        assert_eq!(
            reduced, raw,
            "BigRational: non-reduced 2/4 equals 1/2 — vstd requirement (2) \
             violated; no obeys_key_model axiom possible"
        );
        use std::hash::{DefaultHasher, Hash, Hasher};
        let h = |r: &BigRational| {
            let mut s = DefaultHasher::new();
            r.hash(&mut s);
            s.finish()
        };
        // The crate deliberately hashes non-reduced ratios like their reduced
        // form ("needs to agree with Eq even for non-reduced ratios").
        assert_eq!(h(&reduced), h(&raw));
    }
}

// ---------------------------------------------------------------------------
// Canonical key wrappers (src/canonical_keys.rs): requirement-level proptest
// fuzz. These are the types that REPLACE the withdrawn OrderedFloat /
// BigRational axioms; requirement (2) holds by construction (constructor
// canonicalizes; Eq/Hash are derived structural), and these tests fuzz
// exactly that construction argument: however a value is built, equal
// values have identical canonical representations.
// ---------------------------------------------------------------------------
#[cfg(feature = "literal-types")]
mod canonical_key_model {
    use num_bigint::BigInt;
    use num_rational::{BigRational, Ratio};
    use proptest::prelude::*;
    use semi_persistent_containers_verus::{CanonicalF64, CanonicalRational, ShrinkPolicy, SpMap};
    use std::hash::{DefaultHasher, Hash, Hasher};

    fn hash_of<K: Hash>(k: &K) -> u64 {
        let mut h = DefaultHasher::new();
        k.hash(&mut h);
        h.finish()
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(512))]

        /// Requirement (2) for CanonicalF64: == implies identical canonical
        /// bits, across arbitrary f64s INCLUDING arbitrary NaN payloads and
        /// signed zeros (any bit pattern is a valid f64 input).
        #[test]
        fn canonical_f64_eq_is_identity(a_bits in any::<u64>(), b_bits in any::<u64>()) {
            let a = CanonicalF64::new(f64::from_bits(a_bits));
            let b = CanonicalF64::new(f64::from_bits(b_bits));
            if a == b {
                prop_assert_eq!(a.bits(), b.bits(), "eq but bits differ");
                prop_assert_eq!(hash_of(&a), hash_of(&b), "eq but hash differs");
            } else {
                prop_assert_ne!(a.bits(), b.bits(), "ne but bits identical");
            }
            // The two OrderedFloat violations are FIXED here: every NaN input
            // lands on one representation, and ±0.0 collapse.
            let c = a; // Copy — clone identity is trivial bitwise copy
            prop_assert_eq!(a, c);
        }

        /// The fold is semantic: values that std `==` would call equal (or
        /// are both NaN) canonicalize to the SAME key; values std would
        /// distinguish stay distinct keys.
        #[test]
        fn canonical_f64_respects_float_semantics(a_bits in any::<u64>(), b_bits in any::<u64>()) {
            let (fa, fb) = (f64::from_bits(a_bits), f64::from_bits(b_bits));
            let (a, b) = (CanonicalF64::new(fa), CanonicalF64::new(fb));
            let semantically_same = (fa == fb) || (fa.is_nan() && fb.is_nan());
            prop_assert_eq!(a == b, semantically_same);
        }

        /// Requirement (2) for CanonicalRational: mathematically equal
        /// inputs built through DIFFERENT paths (reduced, raw non-reduced,
        /// scaled, negated-twice) produce identical representations.
        #[test]
        fn canonical_rational_eq_is_identity(
            n in -10_000i64..10_000, d in 1i64..10_000, scale in 1i64..64,
        ) {
            let base = CanonicalRational::new(BigInt::from(n), BigInt::from(d));
            let variants = [
                CanonicalRational::new(BigInt::from(n * scale), BigInt::from(d * scale)),
                CanonicalRational::new(BigInt::from(-n), BigInt::from(-d)),
                CanonicalRational::from_rational(
                    &Ratio::new_raw(BigInt::from(n * scale), BigInt::from(d * scale))),
                CanonicalRational::from_rational(&BigRational::new(
                    BigInt::from(n), BigInt::from(d))),
                base.clone(), // requirement (3)
            ];
            for v in &variants {
                prop_assert_eq!(v, &base, "same rational not eq");
                prop_assert_eq!(v.numer(), base.numer(), "eq but numer differs");
                prop_assert_eq!(v.denom(), base.denom(), "eq but denom differs");
                prop_assert_eq!(hash_of(v), hash_of(&base), "eq but hash differs");
            }
            // canonical form invariants
            prop_assert!(base.denom() > &BigInt::from(0), "denominator not positive");
        }

        /// Distinct rationals stay distinct (the fold is exactly by value).
        #[test]
        fn canonical_rational_injective(
            n1 in -1_000i64..1_000, d1 in 1i64..1_000,
            n2 in -1_000i64..1_000, d2 in 1i64..1_000,
        ) {
            let a = CanonicalRational::new(BigInt::from(n1), BigInt::from(d1));
            let b = CanonicalRational::new(BigInt::from(n2), BigInt::from(d2));
            // value equality iff cross-multiplication equality
            let same_value = n1 as i128 * d2 as i128 == n2 as i128 * d1 as i128;
            prop_assert_eq!(a == b, same_value);
        }
    }

    /// SpMap oracle trace over canonical keys — the interning surface the
    /// e-graph's NiraLitVal::Rat / model f64 literals are intended to use.
    /// Adversarial inputs: NaN payload variants and ±0.0 (which broke the
    /// withdrawn OrderedFloat axiom) now legitimately collapse to ONE key.
    #[test]
    fn canonical_keys_spmap_oracle() {
        let mut m: SpMap<CanonicalF64, u64, usize, true> = SpMap::new();
        let mut oracle: std::collections::HashMap<CanonicalF64, u64> =
            std::collections::HashMap::new();

        let inputs: Vec<f64> = vec![
            f64::NAN,
            f64::from_bits(f64::NAN.to_bits() ^ 0x1), // distinct payload
            f64::from_bits(f64::NAN.to_bits() | 0x8000_0000_0000_0000), // sign bit
            0.0,
            -0.0,
            1.5,
            -1.5,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::MIN_POSITIVE,
        ];
        for (i, &f) in inputs.iter().enumerate() {
            let k = CanonicalF64::new(f);
            m.try_insert(k, i as u64).expect("compat: capacity");
            oracle.insert(k, i as u64);
        }
        // The three NaN inputs are ONE key; ±0.0 are ONE key.
        assert_eq!(oracle.len(), 7, "canonicalization folds NaNs and zeros");
        assert_eq!(m.len(), oracle.len());

        let tok = m
            .try_mark(ShrinkPolicy::Never)
            .expect("compat: depth in bounds");
        m.try_insert(CanonicalF64::new(f64::NAN), 999)
            .expect("compat: capacity");
        assert_eq!(m.get_by_key(&CanonicalF64::new(-f64::NAN)), Some(&999));
        m.try_restore(tok).expect("compat: own live token");
        for (k, v) in &oracle {
            assert_eq!(m.get_by_key(k), Some(v), "post-restore mismatch");
        }

        // Rational side: raw non-reduced input interns to the same id.
        let mut r: SpMap<CanonicalRational, u64, usize, true> = SpMap::new();
        let half = CanonicalRational::new(BigInt::from(1), BigInt::from(2));
        let raw_half =
            CanonicalRational::from_rational(&Ratio::new_raw(BigInt::from(2), BigInt::from(4)));
        let id1 = r.try_insert(half, 1).expect("compat: capacity");
        let _ = id1;
        assert_eq!(r.get_by_key(&raw_half), Some(&1), "2/4 interns as 1/2");
        assert_eq!(r.len(), 1);
    }
}

/// Compatibility checks for float keys (feature `literal-types`).
///
/// `CanonicalF64` reproduces the e-graph interner's `OrderedFloat` identity.
/// These tests pin both that equivalence and the fold itself so a change cannot
/// silently alter term identity. They do not resolve semantic float identity
/// (±0.0 / NaN classes or the `1/0` versus `1/-0` model hazard);
/// `BitsF64` is the no-fold key for that purpose. See `canonical_keys.rs` and
/// `doc/future/key-model-tcb.md`.
#[cfg(feature = "literal-types")]
mod float_key_semantics {
    use ordered_float::OrderedFloat;
    use proptest::prelude::*;
    use semi_persistent_containers_verus::{BitsF64, CanonicalF64};

    /// The fold is pinned: NaN payloads and ±0.0 collapse, exactly like
    /// production's OrderedFloat keys.
    #[test]
    fn canonical_f64_fold_is_pinned() {
        let nan_variants = [
            f64::NAN,
            f64::from_bits(f64::NAN.to_bits() ^ 0x1),
            f64::from_bits(f64::NAN.to_bits() | 0x8000_0000_0000_0000),
        ];
        for v in nan_variants {
            assert_eq!(
                CanonicalF64::new(v),
                CanonicalF64::new(f64::NAN),
                "fold pin: every NaN is one key"
            );
        }
        assert_eq!(
            CanonicalF64::new(-0.0),
            CanonicalF64::new(0.0),
            "fold pin: signed zeros are one key"
        );
        // And BitsF64 does NOT fold — the semantic-fix key keeps them apart.
        assert_ne!(BitsF64::new(-0.0), BitsF64::new(0.0));
        assert_ne!(
            BitsF64::new(f64::NAN),
            BitsF64::new(f64::from_bits(f64::NAN.to_bits() ^ 0x1))
        );
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(512))]

        /// CanonicalF64 keys agree with OrderedFloat keys on EVERY pair:
        /// same equivalence relation as the production interner.
        #[test]
        fn canonical_f64_matches_ordered_float(a in any::<u64>(), b in any::<u64>()) {
            let (fa, fb) = (f64::from_bits(a), f64::from_bits(b));
            prop_assert_eq!(
                CanonicalF64::new(fa) == CanonicalF64::new(fb),
                OrderedFloat(fa) == OrderedFloat(fb),
                "CanonicalF64 must key exactly like production's OrderedFloat"
            );
        }

        /// BitsF64 requirement (2) is trivial: == iff identical bits.
        #[test]
        fn bits_f64_eq_is_bit_identity(a in any::<u64>(), b in any::<u64>()) {
            let (ka, kb) = (BitsF64::new(f64::from_bits(a)), BitsF64::new(f64::from_bits(b)));
            prop_assert_eq!(ka == kb, a == b);
            prop_assert_eq!(ka.bits(), a);
        }
    }
}
