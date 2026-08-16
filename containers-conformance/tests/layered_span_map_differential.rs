// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conformance of the verified `LayeredSpanMap`: a reference-model differential
//! over randomized base, delta and invalidated-key inputs.
//!
//! The oracle is the same shape as `dense_span_map_differential.rs`'s: a
//! `HashMap<usize, Vec<V>>`, here filled by the definition of the logical view
//! rather than by the container's mechanism. It walks the base stream skipping
//! entries whose key was invalidated, then walks the delta stream. No layers, no
//! spans, no binary search, no flatten threshold.
//!
//! Verus erases contracts under `cargo test`, so this exercises the executable
//! code the proofs never run: the invalidated-key binary search, the two-segment
//! `get`, the validation in `try_with_delta`, and `flatten`'s regrouping.
//!
//! What is asserted, for every generated input:
//!   - both segments of `get(k)`, concatenated, equal the reference vector, in
//!     order (an out-of-order pass would satisfy a multiset comparison);
//!   - an invalidated key contributes an empty base segment, so its logical
//!     contents are exactly its delta entries, including the case where those
//!     are empty and the key disappears entirely;
//!   - `key_len` agrees with the concatenated length;
//!   - `flatten` produces a `DenseSpanMap` with the same per-key contents,
//!     which is the theorem that makes the compaction policy sound;
//!   - cross-generation sortedness: when the caller separates the generations
//!     (every delta value above every surviving base value under that key), the
//!     concatenation is sorted, and when it does not, the test records that the
//!     concatenation is NOT claimed sorted, only each segment;
//!   - `try_with_delta` rejects an unsorted or out-of-range invalidated-key
//!     list and an out-of-range delta key.

use proptest::prelude::*;
use semi_persistent_containers_verus as verus;
use std::collections::HashMap;
use verus::{DenseSpanMap, LayeredSpanMap};

/// The oracle: the logical view, straight from its definition.
fn reference(
    base: &[(usize, u32)],
    delta: &[(usize, u32)],
    invalid: &[usize],
    num_keys: usize,
) -> HashMap<usize, Vec<u32>> {
    let mut m: HashMap<usize, Vec<u32>> = HashMap::new();
    for k in 0..num_keys {
        m.insert(k, Vec::new());
    }
    for &(k, v) in base {
        if !invalid.contains(&k) {
            m.entry(k).or_default().push(v);
        }
    }
    for &(k, v) in delta {
        m.entry(k).or_default().push(v);
    }
    m
}

/// Build a layered map and compare every key against the oracle.
fn check(
    base_stream: &[(usize, u32)],
    delta_stream: &[(usize, u32)],
    invalid: &[usize],
    num_keys: usize,
) -> Result<(), TestCaseError> {
    let base = DenseSpanMap::<u32>::try_build(base_stream, num_keys).expect("base keys in range");
    let layered = LayeredSpanMap::<u32>::try_with_delta(base, delta_stream, invalid)
        .expect("delta keys in range, invalid list ascending");
    let want = reference(base_stream, delta_stream, invalid, num_keys);

    prop_assert_eq!(layered.len(), num_keys, "key count");
    prop_assert_eq!(layered.delta_total(), delta_stream.len(), "delta size");
    prop_assert_eq!(layered.base_total(), base_stream.len(), "base size");
    prop_assert_eq!(layered.invalid_count(), invalid.len(), "invalid count");

    for k in 0..num_keys {
        let (bseg, dseg) = layered.get(k);
        let mut got = bseg.to_vec();
        got.extend_from_slice(dseg);
        let expected = &want[&k];
        prop_assert_eq!(&got, expected, "key {}: logical contents", k);
        prop_assert_eq!(layered.key_len(k), expected.len(), "key {}: key_len", k);

        // An invalidated key contributes nothing from the base.
        prop_assert_eq!(
            layered.is_invalidated(k),
            invalid.contains(&k),
            "key {}: invalidation verdict",
            k
        );
        if invalid.contains(&k) {
            prop_assert!(bseg.is_empty(), "key {}: invalidated base segment", k);
        }
        // The delta segment never depends on invalidation.
        let delta_only: Vec<u32> = delta_stream
            .iter()
            .filter(|&&(dk, _)| dk == k)
            .map(|&(_, v)| v)
            .collect();
        prop_assert_eq!(dseg, delta_only.as_slice(), "key {}: delta segment", k);
    }

    // flatten preserves every key's contents.
    let flat = layered.flatten();
    prop_assert_eq!(flat.len(), num_keys, "flatten key count");
    for k in 0..num_keys {
        prop_assert_eq!(flat.get(k), want[&k].as_slice(), "key {}: after flatten", k);
    }
    Ok(())
}

proptest! {
    /// Randomized base, delta and invalidated keys.
    #[test]
    fn matches_reference(
        num_keys in 1usize..20,
        base in prop::collection::vec((0usize..20, any::<u32>()), 0..150),
        delta in prop::collection::vec((0usize..20, any::<u32>()), 0..60),
        invalid_raw in prop::collection::vec(0usize..20, 0..10),
    ) {
        let base: Vec<(usize, u32)> = base.into_iter().filter(|&(k, _)| k < num_keys).collect();
        let delta: Vec<(usize, u32)> = delta.into_iter().filter(|&(k, _)| k < num_keys).collect();
        // `try_with_delta` requires a strictly ascending, in-range list.
        let mut invalid: Vec<usize> =
            invalid_raw.into_iter().filter(|&k| k < num_keys).collect();
        invalid.sort_unstable();
        invalid.dedup();
        check(&base, &delta, &invalid, num_keys)?;
    }

    /// The shape the consumer actually produces: ids ascending across
    /// generations, so every delta value exceeds every base value, and the
    /// concatenation of the two segments is sorted.
    #[test]
    fn cross_generation_sortedness(
        num_keys in 1usize..12,
        base_keys in prop::collection::vec(0usize..12, 0..80),
        delta_keys in prop::collection::vec(0usize..12, 0..40),
        invalid_raw in prop::collection::vec(0usize..12, 0..6),
    ) {
        // Values are assigned in ascending order across both generations, which
        // is what visiting node ids in ascending order produces.
        let mut next: u32 = 0;
        let base: Vec<(usize, u32)> = base_keys
            .into_iter()
            .filter(|&k| k < num_keys)
            .map(|k| { let v = next; next += 1; (k, v) })
            .collect();
        let delta: Vec<(usize, u32)> = delta_keys
            .into_iter()
            .filter(|&k| k < num_keys)
            .map(|k| { let v = next; next += 1; (k, v) })
            .collect();
        let mut invalid: Vec<usize> =
            invalid_raw.into_iter().filter(|&k| k < num_keys).collect();
        invalid.sort_unstable();
        invalid.dedup();

        check(&base, &delta, &invalid, num_keys)?;

        let dense = DenseSpanMap::<u32>::try_build(&base, num_keys).expect("in range");
        let layered = LayeredSpanMap::<u32>::try_with_delta(dense, &delta, &invalid)
            .expect("in range");
        for k in 0..num_keys {
            let (bseg, dseg) = layered.get(k);
            // Each segment is sorted on its own.
            prop_assert!(bseg.windows(2).all(|w| w[0] < w[1]), "base segment sorted");
            prop_assert!(dseg.windows(2).all(|w| w[0] < w[1]), "delta segment sorted");
            // Separation holds because ids ascend across generations, so the
            // concatenation is sorted: the cross-generation lemma's conclusion.
            if let (Some(&last_base), Some(&first_delta)) = (bseg.last(), dseg.first()) {
                prop_assert!(last_base < first_delta, "key {}: generations separated", k);
            }
            let mut all = bseg.to_vec();
            all.extend_from_slice(dseg);
            prop_assert!(all.windows(2).all(|w| w[0] < w[1]), "key {}: concat sorted", k);
        }
    }

    /// `flatten` is idempotent as a base: flattening and re-layering with an
    /// empty delta reproduces the same contents.
    #[test]
    fn flatten_round_trips(
        num_keys in 1usize..14,
        base in prop::collection::vec((0usize..14, any::<u32>()), 0..80),
        delta in prop::collection::vec((0usize..14, any::<u32>()), 0..40),
    ) {
        let base: Vec<(usize, u32)> = base.into_iter().filter(|&(k, _)| k < num_keys).collect();
        let delta: Vec<(usize, u32)> = delta.into_iter().filter(|&(k, _)| k < num_keys).collect();
        let d = DenseSpanMap::<u32>::try_build(&base, num_keys).expect("in range");
        let layered = LayeredSpanMap::<u32>::try_with_delta(d, &delta, &[]).expect("in range");

        let flat = layered.flatten();
        let relayered = LayeredSpanMap::<u32>::try_with_delta(flat, &[], &[]).expect("in range");
        for k in 0..num_keys {
            let (b1, d1) = layered.get(k);
            let mut before = b1.to_vec();
            before.extend_from_slice(d1);
            let (b2, d2) = relayered.get(k);
            let mut after = b2.to_vec();
            after.extend_from_slice(d2);
            prop_assert_eq!(before, after, "key {}: flatten round trip", k);
        }
    }
}

// ---------------------------------------------------------------------------
// Fixed cases
// ---------------------------------------------------------------------------

fn layered(
    base: &[(usize, u32)],
    delta: &[(usize, u32)],
    invalid: &[usize],
    num_keys: usize,
) -> LayeredSpanMap<u32> {
    let d = DenseSpanMap::<u32>::try_build(base, num_keys).expect("in range");
    LayeredSpanMap::<u32>::try_with_delta(d, delta, invalid).expect("in range")
}

fn contents(m: &LayeredSpanMap<u32>, k: usize) -> Vec<u32> {
    let (b, d) = m.get(k);
    let mut out = b.to_vec();
    out.extend_from_slice(d);
    out
}

#[test]
fn delta_appends_to_a_live_base_bucket() {
    let m = layered(&[(0, 1), (0, 2), (1, 9)], &[(0, 3)], &[], 2);
    assert_eq!(contents(&m, 0), vec![1, 2, 3]);
    assert_eq!(contents(&m, 1), vec![9]);
}

#[test]
fn invalidated_key_drops_its_base_bucket() {
    let m = layered(&[(0, 1), (0, 2), (1, 9)], &[(0, 3)], &[0], 2);
    // Key 0's base entries are gone; only the delta survives.
    assert_eq!(contents(&m, 0), vec![3]);
    assert_eq!(contents(&m, 1), vec![9]);
}

#[test]
fn invalidated_key_with_no_delta_is_empty() {
    let m = layered(&[(0, 1), (0, 2)], &[], &[0], 1);
    assert_eq!(contents(&m, 0), Vec::<u32>::new());
    assert_eq!(m.key_len(0), 0);
}

#[test]
fn empty_delta_and_no_invalidation_is_the_base() {
    let m = layered(&[(0, 1), (1, 2), (1, 3)], &[], &[], 2);
    assert_eq!(contents(&m, 0), vec![1]);
    assert_eq!(contents(&m, 1), vec![2, 3]);
}

#[test]
fn build_base_has_no_delta_and_no_invalidation() {
    let m = LayeredSpanMap::<u32>::try_build_base(&[(0, 7), (1, 8)], 2).expect("in range");
    assert_eq!(m.delta_total(), 0);
    assert_eq!(m.invalid_count(), 0);
    assert_eq!(contents(&m, 0), vec![7]);
    assert_eq!(contents(&m, 1), vec![8]);
}

#[test]
fn flatten_collapses_both_generations() {
    let m = layered(&[(0, 1), (1, 5), (0, 2)], &[(1, 6), (0, 3)], &[], 2);
    let flat = m.flatten();
    assert_eq!(flat.get(0), &[1, 2, 3]);
    assert_eq!(flat.get(1), &[5, 6]);
    assert_eq!(flat.total(), 5);
}

#[test]
fn flatten_drops_invalidated_base_entries() {
    let m = layered(&[(0, 1), (1, 5), (0, 2)], &[(0, 3)], &[0], 2);
    let flat = m.flatten();
    assert_eq!(flat.get(0), &[3]);
    assert_eq!(flat.get(1), &[5]);
    assert_eq!(flat.total(), 2);
}

#[test]
fn needs_flatten_tracks_the_quarter_threshold() {
    // base 8 values: threshold is delta + invalid > 2.
    let base: Vec<(usize, u32)> = (0..8).map(|v| (0usize, v)).collect();
    let small = layered(&base, &[(0, 100), (0, 101)], &[], 1);
    assert!(!small.needs_flatten(), "2 <= 8/4 must not trigger");
    let big = layered(&base, &[(0, 100), (0, 101), (0, 102)], &[], 1);
    assert!(big.needs_flatten(), "3 > 8/4 must trigger");
    // Invalidated keys count toward the threshold too.
    let with_invalid = layered(&base, &[(0, 100), (0, 101)], &[1], 2);
    assert!(with_invalid.needs_flatten(), "2 delta + 1 invalid > 8/4");
}

#[test]
fn invalidated_key_list_must_be_ascending_and_in_range() {
    let d = DenseSpanMap::<u32>::try_build(&[(0, 1)], 3).expect("in range");
    assert!(
        LayeredSpanMap::<u32>::try_with_delta(d, &[], &[1, 0]).is_err(),
        "descending"
    );
    let d = DenseSpanMap::<u32>::try_build(&[(0, 1)], 3).expect("in range");
    assert!(
        LayeredSpanMap::<u32>::try_with_delta(d, &[], &[0, 0]).is_err(),
        "repeated"
    );
    let d = DenseSpanMap::<u32>::try_build(&[(0, 1)], 3).expect("in range");
    assert!(
        LayeredSpanMap::<u32>::try_with_delta(d, &[], &[3]).is_err(),
        "out of range"
    );
    let d = DenseSpanMap::<u32>::try_build(&[(0, 1)], 3).expect("in range");
    assert!(
        LayeredSpanMap::<u32>::try_with_delta(d, &[(3, 1)], &[]).is_err(),
        "delta key"
    );
}

#[test]
fn invalidation_lookup_is_exact_over_a_wide_list() {
    // Exercises the binary search across every key, present and absent.
    let invalid: Vec<usize> = (0..64).filter(|k| k % 3 == 0).collect();
    let m = layered(&[], &[], &invalid, 64);
    for k in 0..64 {
        assert_eq!(m.is_invalidated(k), k % 3 == 0, "key {k}");
    }
    assert!(!m.is_invalidated(64), "past the key space");
    assert!(!m.is_invalidated(usize::MAX));
}

#[test]
fn u64_values_layer_the_same_way() {
    let d = DenseSpanMap::<u64>::try_build(&[(0, 1u64), (1, u64::MAX)], 2).expect("in range");
    let m = LayeredSpanMap::<u64>::try_with_delta(d, &[(0, 7u64)], &[1]).expect("in range");
    let (b0, d0) = m.get(0);
    assert_eq!(b0, &[1u64]);
    assert_eq!(d0, &[7u64]);
    let (b1, d1) = m.get(1);
    assert_eq!(b1, &[] as &[u64]);
    assert_eq!(d1, &[] as &[u64]);
}

// ---------------------------------------------------------------------------
// Cross-round reinstall: replace_delta and into_base
// ---------------------------------------------------------------------------

proptest! {
    /// The accumulate-and-reinstall policy, exercised the way a saturation loop
    /// drives it: build a base once, install a delta, then replace that delta
    /// with a longer accumulated stream each round. The base is never rebuilt,
    /// and after every round the contents must equal the oracle computed from
    /// the original base stream and the round's accumulated delta.
    #[test]
    fn replace_delta_matches_reference_across_rounds(
        num_keys in 1usize..14,
        base in prop::collection::vec((0usize..14, any::<u32>()), 0..90),
        rounds in prop::collection::vec(
            (
                prop::collection::vec((0usize..14, any::<u32>()), 0..25),
                prop::collection::vec(0usize..14, 0..5),
            ),
            1..6,
        ),
    ) {
        let base: Vec<(usize, u32)> = base.into_iter().filter(|&(k, _)| k < num_keys).collect();
        let d = DenseSpanMap::<u32>::try_build(&base, num_keys).expect("in range");
        let mut m = LayeredSpanMap::<u32>::try_with_delta(d, &[], &[]).expect("in range");

        // The caller accumulates the delta stream and the invalidations.
        let mut accumulated: Vec<(usize, u32)> = Vec::new();
        let mut invalid: Vec<usize> = Vec::new();

        for (round_delta, round_invalid) in rounds {
            accumulated.extend(round_delta.into_iter().filter(|&(k, _)| k < num_keys));
            invalid.extend(round_invalid.into_iter().filter(|&k| k < num_keys));
            invalid.sort_unstable();
            invalid.dedup();

            m = m.replace_delta(&accumulated, &invalid).expect("in range");

            let want = reference(&base, &accumulated, &invalid, num_keys);
            prop_assert_eq!(m.len(), num_keys);
            prop_assert_eq!(m.base_total(), base.len(), "base was rebuilt");
            prop_assert_eq!(m.delta_total(), accumulated.len(), "delta size");
            prop_assert_eq!(m.invalid_count(), invalid.len(), "invalid count");
            for k in 0..num_keys {
                prop_assert_eq!(&contents(&m, k), &want[&k], "key {}: after reinstall", k);
            }
        }
    }

    /// `into_base` yields the base generation, and what it yields is accepted by
    /// `try_with_delta`, so a caller can leave and re-enter the layered form.
    #[test]
    fn into_base_round_trips_through_try_with_delta(
        num_keys in 1usize..12,
        base in prop::collection::vec((0usize..12, any::<u32>()), 0..60),
        delta in prop::collection::vec((0usize..12, any::<u32>()), 0..30),
    ) {
        let base: Vec<(usize, u32)> = base.into_iter().filter(|&(k, _)| k < num_keys).collect();
        let delta: Vec<(usize, u32)> = delta.into_iter().filter(|&(k, _)| k < num_keys).collect();
        let d = DenseSpanMap::<u32>::try_build(&base, num_keys).expect("in range");
        let m = LayeredSpanMap::<u32>::try_with_delta(d, &delta, &[]).expect("in range");

        // into_base discards the delta and the invalidations: it is the base,
        // not the logical view.
        let recovered = m.into_base();
        prop_assert_eq!(recovered.len(), num_keys);
        prop_assert_eq!(recovered.total(), base.len(), "into_base is the base");
        let base_only = reference(&base, &[], &[], num_keys);
        for k in 0..num_keys {
            prop_assert_eq!(recovered.get(k), base_only[&k].as_slice(), "key {}", k);
        }

        // And it re-enters the layered form.
        let again = LayeredSpanMap::<u32>::try_with_delta(recovered, &delta, &[])
            .expect("into_base output is a usable base");
        for k in 0..num_keys {
            prop_assert_eq!(&contents(&again, k), &reference(&base, &delta, &[], num_keys)[&k]);
        }
    }
}

#[test]
fn replace_delta_keeps_the_base_and_swaps_the_delta() {
    let m = layered(&[(0, 1), (1, 5)], &[(0, 2)], &[], 2);
    assert_eq!(contents(&m, 0), vec![1, 2]);
    // Round two hands in the accumulated stream, not just the new entries.
    let m = m
        .replace_delta(&[(0, 2), (0, 3), (1, 6)], &[])
        .expect("in range");
    assert_eq!(contents(&m, 0), vec![1, 2, 3]);
    assert_eq!(contents(&m, 1), vec![5, 6]);
    assert_eq!(m.base_total(), 2, "base untouched");
    assert_eq!(m.delta_total(), 3);
}

#[test]
fn replace_delta_can_change_the_invalidated_set() {
    let m = layered(&[(0, 1), (1, 5)], &[(0, 2)], &[], 2);
    // Key 1 becomes invalidated in a later round; key 0 stays live.
    let m = m.replace_delta(&[(0, 2), (1, 7)], &[1]).expect("in range");
    assert_eq!(contents(&m, 0), vec![1, 2]);
    assert_eq!(contents(&m, 1), vec![7], "base entry 5 dropped");
    // And it can be un-invalidated again, because invalidation is per install.
    let m = m.replace_delta(&[(0, 2), (1, 7)], &[]).expect("in range");
    assert_eq!(contents(&m, 1), vec![5, 7]);
}

#[test]
fn replace_delta_validates_its_inputs() {
    let m = layered(&[(0, 1)], &[], &[], 2);
    let m = match m.replace_delta(&[(9, 1)], &[]) {
        Ok(_) => panic!("out-of-range delta key must be refused"),
        Err(_) => layered(&[(0, 1)], &[], &[], 2),
    };
    assert!(
        m.replace_delta(&[], &[1, 0]).is_err(),
        "descending invalid list"
    );
}

#[test]
fn into_base_discards_the_delta() {
    let m = layered(&[(0, 1)], &[(0, 2)], &[], 1);
    assert_eq!(contents(&m, 0), vec![1, 2]);
    let b = m.into_base();
    assert_eq!(
        b.get(0),
        &[1],
        "into_base is the base, not the logical view"
    );
    assert_eq!(b.total(), 1);
}

#[test]
fn flatten_then_relayer_is_the_other_restart_route() {
    // flatten folds the delta in; into_base would have dropped it.
    let m = layered(&[(0, 1)], &[(0, 2)], &[], 1);
    let folded = m.flatten();
    assert_eq!(folded.get(0), &[1, 2]);
    let m2 = LayeredSpanMap::<u32>::try_with_delta(folded, &[(0, 3)], &[]).expect("in range");
    assert_eq!(contents(&m2, 0), vec![1, 2, 3]);
}
