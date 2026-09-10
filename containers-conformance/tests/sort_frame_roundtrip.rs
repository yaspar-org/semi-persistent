// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conformance for the sort-first index-major codec.
//!
//! `sort_frame_by_index` is `external_body` (its algorithm is swappable behind a
//! multiset+sorted contract), and `compress_runs_sorted` builds on it plus the
//! `external_body` run decoder. The verified surface is the CODEC CONTRACT —
//! `vec::lemma_multiset_eq_overlay`: a codec that preserves the multiset of
//! writes restores identically. This test backs the trusted pieces by checking
//! that contract directly on randomized UNIQUE-INDEX frames (finalized frames
//! have one write per cell): the sort preserves the multiset and sorts, and the
//! full sort->coalesce->decode round-trip reproduces the same SET of writes.

use proptest::prelude::*;
use semi_persistent_containers_verus as verus;
use std::collections::HashMap;
use verus::diff_compress::{compress_runs_sorted, sort_frame_by_index};

// A unique-index frame: a map from index -> value, as a Vec of pairs in
// insertion order (so arrival is arbitrary, indices unique).
fn unique_frame(pairs: Vec<(u32, u32)>) -> Vec<(u32, u32)> {
    let mut m: HashMap<u32, u32> = HashMap::new();
    for (v, i) in pairs {
        m.entry(i % 128).or_insert(v); // bound indices so runs can form; first wins
    }
    m.into_iter().map(|(i, v)| (v, i)).collect()
}

fn as_set(d: &[(u32, u32)]) -> std::collections::HashSet<(u32, u32)> {
    d.iter().copied().collect()
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 2000, ..ProptestConfig::default() })]

    #[test]
    fn sort_preserves_multiset_and_orders(pairs in prop::collection::vec((any::<u32>(), any::<u32>()), 0..300)) {
        let frame = unique_frame(pairs);
        let sorted = sort_frame_by_index(&frame);
        // Same multiset of writes.
        prop_assert_eq!(as_set(&sorted), as_set(&frame));
        prop_assert_eq!(sorted.len(), frame.len());
        // Ascending by index.
        for w in sorted.windows(2) {
            prop_assert!(w[0].1 <= w[1].1);
        }
    }

    #[test]
    fn sorted_codec_roundtrips_the_write_set(pairs in prop::collection::vec((any::<u32>(), any::<u32>()), 0..300)) {
        let frame = unique_frame(pairs);
        let rf = compress_runs_sorted::<u32, u32>(&frame);
        let decoded: Vec<(u32, u32)> = rf.decode_exec_i::<u32>();
        // Round-trip preserves the write set (order irrelevant, cells unique).
        prop_assert_eq!(as_set(&decoded), as_set(&frame));
        prop_assert_eq!(decoded.len(), frame.len());
        // And the decoded frame is sorted ascending by index.
        for w in decoded.windows(2) {
            prop_assert!(w[0].1 < w[1].1);
        }
    }
}
