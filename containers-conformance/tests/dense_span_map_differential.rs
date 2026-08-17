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

// ---------------------------------------------------------------------------
// The recycled build path: generation stamps and span-table reuse
// ---------------------------------------------------------------------------
//
// `build_in` writes only the keys its stream carries and bumps a generation
// stamp; a key left by an earlier build carries an older stamp and reads as
// empty. These tests drive that against the same oracle, because the whole point
// is that reuse is not observable in the contents.

use semi_persistent_containers_verus::SpanArena;

/// Build over an arena, check against the oracle, hand the arena back.
fn build_check_recycle(
    arena: SpanArena,
    stream: &[(usize, u32)],
    num_keys: usize,
) -> Result<SpanArena, TestCaseError> {
    let map = DenseSpanMap::<u32>::try_build_in(arena, stream, num_keys)
        .unwrap_or_else(|_| panic!("keys in range"));
    let want = reference(stream, num_keys);
    prop_assert_eq!(map.len(), num_keys);
    prop_assert_eq!(map.total(), stream.len());
    for k in 0..num_keys {
        prop_assert_eq!(map.get(k), want[&k].as_slice(), "key {}", k);
        prop_assert_eq!(map.key_len(k), want[&k].len(), "key {} len", k);
    }
    Ok(map.recycle())
}

proptest! {
    /// A sequence of builds over ONE recycled arena. Every build must match the
    /// oracle for its own stream, with no trace of the previous generations:
    /// keys an earlier build occupied and this one does not must read empty.
    #[test]
    fn recycled_builds_leave_no_trace(
        num_keys in 1usize..24,
        rounds in prop::collection::vec(
            prop::collection::vec((0usize..24, any::<u32>()), 0..80),
            1..8,
        ),
    ) {
        let mut arena = SpanArena::new();
        for entries in rounds {
            let stream: Vec<(usize, u32)> =
                entries.into_iter().filter(|&(k, _)| k < num_keys).collect();
            arena = build_check_recycle(arena, &stream, num_keys)?;
        }
    }

    /// Reuse across a shrinking key space: a later build over fewer keys must
    /// not expose the wider table the arena still carries.
    #[test]
    fn recycled_builds_across_key_spaces(
        wide in 8usize..32,
        narrow in 1usize..8,
        a in prop::collection::vec((0usize..32, any::<u32>()), 0..60),
        b in prop::collection::vec((0usize..8, any::<u32>()), 0..30),
    ) {
        let sa: Vec<(usize, u32)> = a.into_iter().filter(|&(k, _)| k < wide).collect();
        let sb: Vec<(usize, u32)> = b.into_iter().filter(|&(k, _)| k < narrow).collect();
        let arena = SpanArena::new();
        let arena = build_check_recycle(arena, &sa, wide)?;
        // The table is still `wide` long; the narrow build must report `narrow`.
        prop_assert!(arena.capacity() >= wide);
        let arena = build_check_recycle(arena, &sb, narrow)?;
        // And widening again still works.
        let _ = build_check_recycle(arena, &sa, wide)?;
    }
}

#[test]
fn stale_keys_read_empty_after_rebuild() {
    // Build A occupies keys 1 and 3; build B over the same arena occupies 0 and 2.
    let arena = SpanArena::new();
    let a = DenseSpanMap::<u32>::try_build_in(arena, &[(1, 10), (3, 30), (1, 11)], 4)
        .unwrap_or_else(|_| panic!("in range"));
    assert_eq!(a.get(1), &[10, 11]);
    assert_eq!(a.get(3), &[30]);
    assert_eq!(a.get(0), &[] as &[u32]);
    let arena = a.recycle();

    let b = DenseSpanMap::<u32>::try_build_in(arena, &[(0, 100), (2, 200)], 4)
        .unwrap_or_else(|_| panic!("in range"));
    // A's keys are stale in B: their spans are still physically in the table,
    // but they carry the previous generation's stamp.
    assert_eq!(b.get(1), &[] as &[u32], "key 1 was A's, must be stale");
    assert_eq!(b.get(3), &[] as &[u32], "key 3 was A's, must be stale");
    assert_eq!(b.get(0), &[100]);
    assert_eq!(b.get(2), &[200]);
    assert_eq!(b.total(), 2);
    assert_eq!(b.key_len(1), 0);
}

#[test]
fn recycled_arena_matches_a_fresh_one() {
    // The same stream built into a used arena and into a fresh one are equal.
    let used = DenseSpanMap::<u32>::try_build_in(SpanArena::new(), &[(0, 1), (2, 2)], 3)
        .unwrap_or_else(|_| panic!("in range"))
        .recycle();
    let stream = [(1usize, 7u32), (1, 8), (2, 9)];
    let from_used =
        DenseSpanMap::<u32>::try_build_in(used, &stream, 3).unwrap_or_else(|_| panic!("in range"));
    let fresh = DenseSpanMap::<u32>::try_build(&stream, 3).expect("in range");
    for k in 0..3 {
        assert_eq!(from_used.get(k), fresh.get(k), "key {k}");
    }
    assert_eq!(from_used.total(), fresh.total());
}

#[test]
fn an_empty_stream_makes_every_key_stale() {
    let arena = SpanArena::new();
    let a = DenseSpanMap::<u32>::try_build_in(arena, &[(0, 1), (1, 2)], 2)
        .unwrap_or_else(|_| panic!("in range"));
    let arena = a.recycle();
    let b = DenseSpanMap::<u32>::try_build_in(arena, &[], 2).unwrap_or_else(|_| panic!("in range"));
    assert_eq!(b.total(), 0);
    for k in 0..2 {
        assert_eq!(b.get(k), &[] as &[u32], "key {k} must be stale");
    }
}

#[test]
fn try_build_in_returns_the_arena_on_refusal() {
    let arena = SpanArena::new();
    match DenseSpanMap::<u32>::try_build_in(arena, &[(9, 1)], 2) {
        Ok(_) => panic!("out-of-range key must be refused"),
        Err((back, _)) => {
            // The arena is handed back, so a refusal costs no allocation.
            let m = DenseSpanMap::<u32>::try_build_in(back, &[(0, 1)], 2)
                .unwrap_or_else(|_| panic!("in range"));
            assert_eq!(m.get(0), &[1]);
        }
    }
}
