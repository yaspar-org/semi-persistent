// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conformance of the verified `DenseSpanMap`: a reference-model differential
//! over randomized `(key, value)` streams.
//!
//! There is no production-crate twin, because `DenseSpanMap` replaces the
//! e-graph's per-round index families, which were open-coded `Vec<Vec<_>>`
//! rebuilds. The oracle is a transparent model written from the semantics rather
//! from the implementation: a `HashMap<usize, Vec<V>>` filled by walking the
//! stream and pushing each value onto its key's vector. No pool, no spans, no
//! prefix sums, no cursors. It cannot reproduce an off-by-one in the counting
//! sort because it does not count.
//!
//! Verus erases `requires`/`ensures` under `cargo test`, so this exercises the
//! executable code the proofs never run: the two-pass build, the span
//! arithmetic, and the public total shells' refusal paths.
//!
//! What is asserted, for every generated stream:
//!   - every key's slice equals the reference vector, *in stream order* (the
//!     order-preserving part of the refinement: a set comparison would miss a
//!     permuted pass 2);
//!   - keys with no entries yield an empty slice rather than being absent, and
//!     are generated on purpose (`num_keys` deliberately exceeds the key range
//!     in some cases);
//!   - `key_len` agrees with the slice length and `total` with the stream
//!     length (no invented, no dropped values, counted independently);
//!   - the slices, concatenated in key order, are exactly the stream stably
//!     sorted by key, which is the tiling and the disjointness observed from
//!     the outside: an overlap or a gap shows up as a duplicated or missing
//!     value here;
//!   - out-of-range reads take the `None` shell rather than panicking, and a
//!     stream carrying an out-of-range key is refused by `try_build`.

use proptest::prelude::*;
use semi_persistent_containers_verus as verus;
use std::collections::HashMap;
use verus::DenseSpanMap;

/// The oracle: stream order preserved per key, nothing else.
fn reference(stream: &[(usize, u32)], num_keys: usize) -> HashMap<usize, Vec<u32>> {
    let mut m: HashMap<usize, Vec<u32>> = HashMap::new();
    for k in 0..num_keys {
        m.insert(k, Vec::new());
    }
    for &(k, v) in stream {
        m.entry(k).or_default().push(v);
    }
    m
}

/// Full comparison of a built map against the oracle.
fn check_against_reference(stream: &[(usize, u32)], num_keys: usize) -> Result<(), TestCaseError> {
    let map = DenseSpanMap::<u32>::try_build(stream, num_keys)
        .expect("every generated key is below num_keys");
    let want = reference(stream, num_keys);

    prop_assert_eq!(map.len(), num_keys, "key count");
    prop_assert_eq!(map.total(), stream.len(), "pool size vs stream length");
    prop_assert_eq!(map.is_empty(), num_keys == 0, "is_empty");

    let mut concatenated: Vec<u32> = Vec::new();
    for k in 0..num_keys {
        let got = map.get(k);
        let expected = &want[&k];
        prop_assert_eq!(
            got,
            expected.as_slice(),
            "key {}: slice differs from the reference (stream {:?})",
            k,
            stream
        );
        prop_assert_eq!(map.key_len(k), expected.len(), "key {}: key_len", k);
        prop_assert_eq!(
            map.try_get(k).map(|s| s.to_vec()),
            Some(expected.clone()),
            "key {}: try_get",
            k
        );
        concatenated.extend_from_slice(got);
    }

    // Tiling observed from outside: the slices in key order reconstruct the
    // stream stably sorted by key, with no value duplicated or lost.
    let mut stably_sorted: Vec<(usize, u32)> = stream.to_vec();
    stably_sorted.sort_by_key(|&(k, _)| k);
    let expected_concat: Vec<u32> = stably_sorted.iter().map(|&(_, v)| v).collect();
    prop_assert_eq!(concatenated, expected_concat, "concatenated slices");

    // Out-of-range reads take the total shell.
    prop_assert!(map.try_get(num_keys).is_none(), "try_get past the last key");
    prop_assert!(map.try_get(usize::MAX).is_none(), "try_get at usize::MAX");
    Ok(())
}

proptest! {
    /// Randomized streams over a dense key range, with `num_keys` allowed to
    /// exceed the keys actually used so empty keys are covered.
    #[test]
    fn matches_hashmap_reference(
        num_keys in 0usize..24,
        entries in prop::collection::vec((0usize..24, any::<u32>()), 0..200),
    ) {
        // Keep only the entries whose key is in range; `num_keys` may be 0.
        let stream: Vec<(usize, u32)> =
            entries.into_iter().filter(|&(k, _)| k < num_keys).collect();
        check_against_reference(&stream, num_keys)?;
    }

    /// Skewed streams: most traffic on one key, which is the shape the e-graph's
    /// index families actually see (a hot relation plus a long tail).
    #[test]
    fn matches_hashmap_reference_skewed(
        num_keys in 1usize..16,
        entries in prop::collection::vec((0usize..3, any::<u32>()), 0..300),
    ) {
        let stream: Vec<(usize, u32)> =
            entries.into_iter().filter(|&(k, _)| k < num_keys).collect();
        check_against_reference(&stream, num_keys)?;
    }

    /// `try_build` refuses a stream carrying a key at or beyond `num_keys`
    /// instead of indexing past the count table.
    #[test]
    fn out_of_range_key_is_refused(
        num_keys in 1usize..16,
        bad_key in 16usize..64,
        prefix in prop::collection::vec((0usize..16, any::<u32>()), 0..32),
    ) {
        let mut stream: Vec<(usize, u32)> =
            prefix.into_iter().filter(|&(k, _)| k < num_keys).collect();
        stream.push((bad_key, 7));
        prop_assert!(
            DenseSpanMap::<u32>::try_build(&stream, num_keys).is_err(),
            "a key >= num_keys must be refused"
        );
    }

    /// The composite-key helper is injective on its domain, so a map keyed by it
    /// never conflates two distinct pairs.
    #[test]
    fn composite_key_is_injective(
        bcount in 1usize..64,
        a1 in 0usize..64, b1 in 0usize..64,
        a2 in 0usize..64, b2 in 0usize..64,
    ) {
        let k1 = DenseSpanMap::<u32>::composite_key(a1, b1, bcount);
        let k2 = DenseSpanMap::<u32>::composite_key(a2, b2, bcount);
        // Out-of-range `b` is rejected rather than folded into the next `a`.
        prop_assert_eq!(k1.is_some(), b1 < bcount);
        prop_assert_eq!(k2.is_some(), b2 < bcount);
        if let (Some(k1), Some(k2)) = (k1, k2) {
            prop_assert_eq!(k1 == k2, (a1, b1) == (a2, b2), "composite key collision");
        }
    }

    /// Two-dimensional use: build over composite keys and read back by pair.
    #[test]
    fn composite_key_round_trip(
        acount in 1usize..8,
        bcount in 1usize..8,
        entries in prop::collection::vec((0usize..8, 0usize..8, any::<u32>()), 0..100),
    ) {
        let num_keys = acount * bcount;
        let pairs: Vec<(usize, usize, u32)> = entries
            .into_iter()
            .filter(|&(a, b, _)| a < acount && b < bcount)
            .collect();
        let stream: Vec<(usize, u32)> = pairs
            .iter()
            .map(|&(a, b, v)| {
                (
                    DenseSpanMap::<u32>::composite_key(a, b, bcount).expect("in range"),
                    v,
                )
            })
            .collect();
        let map = DenseSpanMap::<u32>::try_build(&stream, num_keys).expect("keys in range");

        for a in 0..acount {
            for b in 0..bcount {
                let k = DenseSpanMap::<u32>::composite_key(a, b, bcount).expect("in range");
                let expected: Vec<u32> = pairs
                    .iter()
                    .filter(|&&(pa, pb, _)| pa == a && pb == b)
                    .map(|&(_, _, v)| v)
                    .collect();
                prop_assert_eq!(map.get(k), expected.as_slice(), "pair ({}, {})", a, b);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Fixed cases: the shapes a random search reaches rarely or never.
// ---------------------------------------------------------------------------

#[test]
fn empty_stream_and_zero_keys() {
    let map = DenseSpanMap::<u32>::try_build(&[], 0).expect("empty is buildable");
    assert_eq!(map.len(), 0);
    assert_eq!(map.total(), 0);
    assert!(map.is_empty());
    assert!(map.try_get(0).is_none());
}

#[test]
fn all_keys_empty() {
    let map = DenseSpanMap::<u32>::try_build(&[], 5).expect("no entries is buildable");
    assert_eq!(map.len(), 5);
    assert_eq!(map.total(), 0);
    assert!(!map.is_empty());
    for k in 0..5 {
        assert_eq!(map.get(k), &[] as &[u32], "key {k} must be an empty slice");
        assert_eq!(map.key_len(k), 0);
    }
}

#[test]
fn single_key_holds_everything() {
    let stream: Vec<(usize, u32)> = (0..64).map(|v| (3usize, v)).collect();
    let map = DenseSpanMap::<u32>::try_build(&stream, 4).expect("keys in range");
    assert_eq!(map.total(), 64);
    for k in 0..4 {
        if k == 3 {
            assert_eq!(map.key_len(k), 64);
            assert_eq!(map.get(k), (0..64).collect::<Vec<u32>>().as_slice());
        } else {
            assert_eq!(map.key_len(k), 0);
        }
    }
}

#[test]
fn duplicate_values_are_kept_not_deduplicated() {
    // A multimap, not a set: repeats survive, in stream order.
    let stream = [(0usize, 9u32), (1, 9), (0, 9), (0, 1)];
    let map = DenseSpanMap::<u32>::try_build(&stream, 2).expect("keys in range");
    assert_eq!(map.get(0), &[9, 9, 1]);
    assert_eq!(map.get(1), &[9]);
    assert_eq!(map.total(), 4);
}

#[test]
fn interleaved_keys_preserve_stream_order() {
    let stream = [
        (2usize, 20u32),
        (0, 0),
        (1, 10),
        (2, 21),
        (0, 1),
        (2, 22),
        (1, 11),
    ];
    let map = DenseSpanMap::<u32>::try_build(&stream, 3).expect("keys in range");
    assert_eq!(map.get(0), &[0, 1]);
    assert_eq!(map.get(1), &[10, 11]);
    assert_eq!(map.get(2), &[20, 21, 22]);
}

#[test]
fn u64_values_build_the_same_way() {
    // `V` is generic; the proofs are over any `Copy + Default`, and the e-graph
    // will instantiate it at node-id width.
    let stream: Vec<(usize, u64)> = vec![(1, u64::MAX), (0, 0), (1, 7)];
    let map = DenseSpanMap::<u64>::try_build(&stream, 2).expect("keys in range");
    assert_eq!(map.get(0), &[0u64]);
    assert_eq!(map.get(1), &[u64::MAX, 7]);
}

#[test]
fn out_of_range_key_in_stream_is_refused() {
    let stream = [(0usize, 1u32), (5, 2)];
    assert!(DenseSpanMap::<u32>::try_build(&stream, 2).is_err());
}

#[test]
fn composite_key_rejects_out_of_range_b_and_overflow() {
    assert_eq!(DenseSpanMap::<u32>::composite_key(2, 3, 4), Some(11));
    // b == bcount would alias (a+1, 0).
    assert_eq!(DenseSpanMap::<u32>::composite_key(2, 4, 4), None);
    // Product leaves usize.
    assert_eq!(DenseSpanMap::<u32>::composite_key(usize::MAX, 0, 2), None);
}
