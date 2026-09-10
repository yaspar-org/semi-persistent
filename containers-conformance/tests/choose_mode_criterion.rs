// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Documents the per-frame scheme-selection criterion (`choose_mode`): given a
//! frame's diffs, it picks index-major, value-major, or plain by exact-size
//! costing. These cases pin the decision boundaries the criterion is built to
//! recognize; `choose_mode` is a heuristic (its output never affects
//! correctness, only size), so this asserts it makes the size-sensible call, not
//! a proof obligation.

use semi_persistent_containers_verus as verus;
use verus::CompressionMode;
use verus::diff_compress::choose_mode;

// Either index-major encoder counts as "index-major". The honest selector now
// returns IndexRunsSorted (its cost is the sorted run count, which the sorted
// encoder achieves), but the write-order IndexRuns is the same family.
fn is_runs(m: CompressionMode) -> bool {
    matches!(
        m,
        CompressionMode::IndexRuns | CompressionMode::IndexRunsSorted
    )
}
fn is_dict(m: CompressionMode) -> bool {
    matches!(m, CompressionMode::ValueDict)
}
fn is_none(m: CompressionMode) -> bool {
    matches!(m, CompressionMode::None)
}

#[test]
fn clustered_indices_pick_index_major() {
    // One contiguous run of 500 cells, each a distinct value. Index-major drops
    // the index column (1 run); value-major cannot help (all values distinct).
    let diffs: Vec<(u32, u32)> = (0..500u32)
        .map(|i| (i.wrapping_mul(2654435761), i))
        .collect();
    assert!(
        is_runs(choose_mode::<u32, u32>(&diffs)),
        "clustered indices -> IndexRuns"
    );
}

#[test]
fn repeated_values_scattered_indices_pick_value_major() {
    // Scattered indices (stride 7, so no runs), only 4 distinct values —
    // value-major's best case (D=4 << N=500). With the shipped packed codes (2 bits
    // for D<=4), dict bytes = 4*4 + ceil(500*2/8) codes + 500*4 idxs = 16+125+2000
    // = 2141 < plain 4000, so the honest selector picks ValueDict. (At the old usize
    // codes this was 6016 > plain and it wrongly picked None — the packed-codes fix
    // is exactly what lets the selector choose value-major here.)
    let diffs: Vec<(u32, u32)> = (0..500u32)
        .map(|i| ((i % 4), i.wrapping_mul(7) % 100_000))
        .collect();
    assert!(
        is_dict(choose_mode::<u32, u32>(&diffs)),
        "few distinct, scattered, narrow codes -> ValueDict (now a win)"
    );
}

#[test]
fn scattered_unique_picks_plain() {
    // Scattered indices AND all-distinct values: neither axis compresses, so the
    // criterion falls back to plain (never worse).
    let diffs: Vec<(u32, u32)> = (0..500u32)
        .map(|i| (i.wrapping_mul(2654435761), i.wrapping_mul(7) % 100_000))
        .collect();
    assert!(
        is_none(choose_mode::<u32, u32>(&diffs)),
        "scattered + unique -> None (plain)"
    );
}

#[test]
fn empty_frame_picks_none() {
    let diffs: Vec<(u32, u32)> = Vec::new();
    assert!(is_none(choose_mode::<u32, u32>(&diffs)));
}
