// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Runtime checks for the sort-first index-major frame encoding selectable through
//! the two-stack (`CompressionMode::IndexRunsSorted`). The verified surface is the
//! CODEC CONTRACT: `compress_frame` preserves the write MULTISET for every mode
//! (proved), and `is_unique_idx` decides the sorted-vs-fallback branch. These tests
//! exercise the exec paths the proof abstracts over: the actual sort+coalesce+decode
//! round-trip, and the write-order fallback taken when a frame's indices repeat.

use proptest::prelude::*;
use std::collections::HashMap;

use semi_persistent_containers_verus as verus;
use verus::CompressionMode;
use verus::diff_compress::{compress_frame, is_unique_idx};

// The multiset of writes, as a count per (value, index) pair.
fn as_multiset(v: &[(u32, u32)]) -> HashMap<(u32, u32), usize> {
    let mut m = HashMap::new();
    for &p in v {
        *m.entry(p).or_insert(0) += 1;
    }
    m
}

fn is_unique_math(v: &[(u32, u32)]) -> bool {
    let mut seen = std::collections::HashSet::new();
    v.iter().all(|&(_, i)| seen.insert(i))
}

proptest! {
    // `is_unique_idx` matches the mathematical property `unique_idx` (each index at
    // most once). This is the runtime check the doc on `is_unique_idx` references.
    #[test]
    fn unique_idx_check(frame in prop::collection::vec((0u32..50, 0u32..20), 0..40)) {
        prop_assert_eq!(is_unique_idx::<u32, u32>(&frame), is_unique_math(&frame));
    }

    // Unique-index frames: the sorted encoder round-trips to the same multiset and
    // decodes in ascending index order (the sort actually happened).
    #[test]
    fn sorted_unique_roundtrip(pairs in prop::collection::vec((0u32..1000, 0u32..1000), 0..60)) {
        // Dedup indices to make the frame unique (first-write-wins), as a finalized
        // frame is.
        let mut seen = std::collections::HashSet::new();
        let frame: Vec<(u32, u32)> = pairs.into_iter().filter(|&(_, i)| seen.insert(i)).collect();
        prop_assume!(is_unique_math(&frame));

        let enc = compress_frame::<u32, u32>(&frame, CompressionMode::IndexRunsSorted);
        let decoded = enc.decode_exec();
        prop_assert_eq!(as_multiset(&decoded), as_multiset(&frame));
        prop_assert_eq!(decoded.len(), frame.len());
        // Sorted ascending by index.
        for w in decoded.windows(2) {
            prop_assert!(w[0].1 <= w[1].1);
        }
    }

    // Non-unique frames: `compress_frame` must NOT sort (that would shadow a write);
    // it falls back to the write-order encoder, which reproduces the exact sequence.
    #[test]
    fn sorted_nonunique_falls_back_to_exact(
        frame in prop::collection::vec((0u32..10, 0u32..5), 1..40)
    ) {
        prop_assume!(!is_unique_math(&frame)); // small index range forces collisions
        let enc = compress_frame::<u32, u32>(&frame, CompressionMode::IndexRunsSorted);
        let decoded = enc.decode_exec();
        // Fallback is write-order exact, so the full sequence (order included) matches.
        prop_assert_eq!(decoded, frame);
    }
}
