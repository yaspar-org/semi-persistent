// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Conformance for the verified index-major run column `RunCol` (the A2
//! encoder that drops the index column and reconstructs each index via
//! `IndexLike::checked_add`, carrying a ghost of the write pairs tied to the runs
//! by `as_nat`). Unlike `RunFrame::decode_exec_i`, `RunCol::decode_exec` is NOT
//! `external_body`: `decode_exec() == decode() == the input pairs` is proved in
//! `containers-verus` with no `IndexFromNat`, so it works for opaque id index
//! types. This test backs two things the proofs do not run under `cargo test`:
//!   - the exec round-trip: `single_run(diffs).decode_exec() == diffs` exactly,
//!   - the heap claim: the encoded `byte_len()` is below a plain `Vec<(T, I)>`
//!     (`len * (size_of::<T>() + size_of::<I>())`) for a contiguous frame,
//!     because the index column is dropped down to one `start`.

use proptest::prelude::*;
use semi_persistent_containers_verus as verus;
use verus::diff_compress::{
    ColdFrame, CompressedFrame, CompressionMode, DeltaFrame, HotFrame, RunCol,
};

/// Reference restore: apply `(value, index)` pairs to a base column in order,
/// last write wins. The oracle `restore_runs_into`'s memcpy must reproduce.
fn apply_pairs(base: &[u32], pairs: &[(u32, u32)]) -> Vec<u32> {
    let mut col = base.to_vec();
    for &(v, i) in pairs {
        col[i as usize] = v;
    }
    col
}

/// A contiguous frame: values arbitrary, indices `start, start+1, ...`.
fn contiguous(start: u32, vals: &[u32]) -> Vec<(u32, u32)> {
    vals.iter()
        .enumerate()
        .map(|(k, &v)| (v, start + k as u32))
        .collect()
}

fn plain_byte_len(n: usize) -> usize {
    n * (core::mem::size_of::<u32>() + core::mem::size_of::<u32>())
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 2000, ..ProptestConfig::default() })]

    #[test]
    fn single_run_roundtrips_and_compresses(
        start in 0u32..1_000_000u32,
        vals in prop::collection::vec(any::<u32>(), 1..300usize),
    ) {
        let diffs = contiguous(start, &vals);

        let col: RunCol<u32, u32> = RunCol::single_run(&diffs);

        // Exact round-trip: decode reproduces every (value, index) pair.
        let decoded = col.decode_exec();
        prop_assert_eq!(decoded.len(), diffs.len());
        for (got, want) in decoded.iter().zip(diffs.iter()) {
            prop_assert_eq!(got.0, want.0);
            prop_assert_eq!(got.1, want.1);
        }

        // Heap claim: index column dropped to one start ⇒ strictly below plain,
        // for any frame of two or more entries.
        if diffs.len() >= 2 {
            prop_assert!(
                col.byte_len() < plain_byte_len(diffs.len()),
                "encoded {} not below plain {} (n={})",
                col.byte_len(), plain_byte_len(diffs.len()), diffs.len(),
            );
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 2000, ..ProptestConfig::default() })]

    // General write-order coalescing: arbitrary (value, index) streams over a
    // bounded index space, so runs both coalesce (ascending contiguous captures)
    // and fall back to singletons (scattered/descending). compress must round-trip
    // exactly, and the memcpy restore must match the pair-by-pair overlay.
    #[test]
    fn compress_roundtrips_and_restore_matches_overlay(
        diffs in prop::collection::vec((any::<u32>(), 0u32..64u32), 0..200usize),
    ) {
        // (value, index) pairs for the encoder.
        let input: Vec<(u32, u32)> = diffs.clone();

        let col: RunCol<u32, u32> = RunCol::compress(&input);

        // Exact round-trip via the verified decode.
        let decoded = col.decode_exec();
        prop_assert_eq!(decoded.len(), input.len());
        for (got, want) in decoded.iter().zip(input.iter()) {
            prop_assert_eq!(got.0, want.0);
            prop_assert_eq!(got.1, want.1);
        }

        // Random access matches the whole decode at every position.
        for (i, d) in decoded.iter().enumerate() {
            prop_assert_eq!(col.decode_at(i), *d);
        }

        // memcpy restore == pair-by-pair overlay (both onto the same base column).
        let base = vec![0u32; 64];
        let mut memcpy_col = base.clone();
        // restore_runs_into was deleted with its trust marker (dead code once the
        // trait restore_to became the verified per-element replay); both paths
        // are now the same verified function.
        CompressedFrame::restore_to(&col, &mut memcpy_col);
        let overlay_col = apply_pairs(&base, &decoded);
        prop_assert_eq!(memcpy_col, overlay_col);
    }
}

/// First-write-wins dedup: keep the first pair per index, giving unique indices
/// (the per-frame invariant the sorted encoder requires).
fn dedup_first(raw: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::new();
    for &(v, i) in raw {
        if seen.insert(i) {
            out.push((v, i));
        }
    }
    out
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 2000, ..ProptestConfig::default() })]

    // Sorted index-major (A3): sort-first coalescing over unique-index frames. The
    // codec reorders, so it does NOT reproduce the capture sequence; it preserves the
    // write multiset, and with unique indices the restore is order-independent, so
    // applying the decoded (sorted) pairs to a base column equals applying the
    // originals. Decoded indices come out ascending.
    #[test]
    fn compress_sorted_restore_matches_and_sorts(
        raw in prop::collection::vec((any::<u32>(), 0u32..64u32), 0..200usize),
    ) {
        let diffs = dedup_first(&raw);

        let col: RunCol<u32, u32> = RunCol::compress_sorted(&diffs);
        let decoded = col.decode_exec();

        // Same number of writes (multiset size), and restore-equivalent to the
        // originals despite the reorder (unique indices).
        prop_assert_eq!(decoded.len(), diffs.len());
        let base = vec![0u32; 64];
        prop_assert_eq!(apply_pairs(&base, &decoded), apply_pairs(&base, &diffs));

        // Decoded indices are ascending (the sort captured all contiguity).
        for w in decoded.windows(2) {
            prop_assert!(w[0].1 <= w[1].1);
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 1000, ..ProptestConfig::default() })]

    // The per-frame-adaptive cold frame (A4 substrate): every mode decodes to a
    // sequence with the input's write multiset, restore-equivalent under unique
    // indices, and decode_at matches the whole decode at each position. Covers the
    // four integrated modes a per-frame selector chooses among.
    #[test]
    fn cold_frame_modes_roundtrip(
        raw in prop::collection::vec((any::<u32>(), 0u32..64u32), 0..150usize),
        mode_pick in 0u8..4,
    ) {
        let diffs = dedup_first(&raw);
        let mode = match mode_pick {
            0 => CompressionMode::None,
            1 => CompressionMode::ValueDict,
            2 => CompressionMode::IndexRuns,
            _ => CompressionMode::IndexRunsSorted,
        };

        let frame: ColdFrame<u32, u32> = ColdFrame::compress_mode(&diffs, mode);
        let n = frame.entry_len();
        prop_assert_eq!(n, diffs.len());

        // decode_at reconstructs each entry; collect the full decode.
        let mut decoded: Vec<(u32, u32)> = Vec::new();
        for i in 0..n {
            decoded.push(frame.decode_at(i));
        }

        // Same write multiset ⇒ same restore onto a base (unique indices).
        let base = vec![0u32; 64];
        prop_assert_eq!(apply_pairs(&base, &decoded), apply_pairs(&base, &diffs));
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 1000, ..ProptestConfig::default() })]

    // Frame trait surface: a hot (uncompressed) frame and every compressed variant
    // restore the SAME write set straight onto a live column. The Runs variant does it
    // with a sliced memcpy, Plain/Dict scattered, and HotFrame scattered; all three
    // must equal the reference application of the pairs. This is the cold-to-live and
    // hot-to-live path (no decode detour).
    #[test]
    fn frames_restore_to_live_column(
        raw in prop::collection::vec((any::<u32>(), 0u32..64u32), 0..150usize),
        mode_pick in 0u8..4,
    ) {
        let diffs = dedup_first(&raw);
        let mode = match mode_pick {
            0 => CompressionMode::None,
            1 => CompressionMode::ValueDict,
            2 => CompressionMode::IndexRuns,
            _ => CompressionMode::IndexRunsSorted,
        };
        let base = vec![7u32; 64];
        let reference = apply_pairs(&base, &diffs);

        // Hot frame: add writes one at a time, restore straight to the column.
        let mut hot: HotFrame<u32, u32> = HotFrame::new();
        for &(v, i) in diffs.iter() {
            hot.add_write(v, i);
        }
        let mut hot_col = base.clone();
        hot.restore_to(&mut hot_col);
        prop_assert_eq!(&hot_col, &reference);

        // Seal it into the chosen mode; the cold frame restores to the same column
        // (memcpy for Runs, scattered otherwise).
        let cold: ColdFrame<u32, u32, verus::value_compressor::NoValueCompression> =
            hot.compress(mode);
        let mut cold_col = base.clone();
        cold.restore_to(&mut cold_col);
        prop_assert_eq!(&cold_col, &reference);
    }
}

#[test]
fn single_run_boundaries() {
    // One entry: byte_len == start index + one value; round-trip holds.
    let d = contiguous(7, &[42]);
    let col: RunCol<u32, u32> = RunCol::single_run(&d);
    let got = col.decode_exec();
    assert_eq!(got, vec![(42u32, 7u32)]);

    // A long contiguous run near a high start still reconstructs each index.
    let vals: Vec<u32> = (0..256).map(|k| k * 3).collect();
    let d = contiguous(1_000, &vals);
    let col: RunCol<u32, u32> = RunCol::single_run(&d);
    let got = col.decode_exec();
    assert_eq!(got, d);
    assert!(col.byte_len() < plain_byte_len(d.len()));
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 1000, ..ProptestConfig::default() })]

    // Delta (value-equals-index with exceptions, F3): exact round-trip on mixed
    // frames. Positions with value == index carry no stored value; exceptions are
    // verbatim. No arithmetic exists to overflow; the boundary test below pins the
    // extremes anyway.
    #[test]
    fn delta_frame_roundtrips(
        raw in prop::collection::vec((any::<u32>(), 0u32..64u32), 0..150usize),
        selfparent_bias in 0u8..2,
    ) {
        // Bias half the runs toward the self-parented shape the encoder targets.
        let diffs: Vec<(u32, u32)> = raw
            .iter()
            .map(|&(v, i)| if selfparent_bias == 1 && v % 4 != 0 { (i, i) } else { (v, i) })
            .collect();
        let f: DeltaFrame<u32, u32> = DeltaFrame::compress(&diffs);
        let n = f.entry_len();
        prop_assert_eq!(n, diffs.len());
        for (i, d) in diffs.iter().enumerate().take(n) {
            prop_assert_eq!(f.decode_at(i), *d);
        }
    }
}

#[test]
fn delta_frame_boundaries_and_bytes() {
    // F3.2 boundary values: value == index everywhere; value == 0; index == 0;
    // value == u32::MAX at index u32::MAX-as-index... u32 index space here, use
    // the extremes representable in the test's index domain.
    let all_self: Vec<(u32, u32)> = (0..1000u32).map(|i| (i, i)).collect();
    let f: DeltaFrame<u32, u32> = DeltaFrame::compress(&all_self);
    for (i, d) in all_self.iter().enumerate() {
        assert_eq!(f.decode_at(i), *d);
    }
    let edges: Vec<(u32, u32)> = vec![
        (0, 0),               // value == index == 0
        (u32::MAX, 1),        // max value as an exception
        (0, 2),               // zero value exception
        (3, 3),               // self at small index
        (u32::MAX, u32::MAX), // value == index at the top of the domain
    ];
    let fe: DeltaFrame<u32, u32> = DeltaFrame::compress(&edges);
    for (i, d) in edges.iter().enumerate() {
        assert_eq!(fe.decode_at(i), *d);
    }

    // F3.3 measured: an all-self-parented frame's delta bytes against plain.
    let plain = all_self.len() * (4 + 4);
    let delta = f.byte_len();
    println!(
        "delta frame: {} bytes vs plain {} ({}x)",
        delta,
        plain,
        plain as f64 / delta as f64
    );
    assert!(delta < plain, "delta {delta} !< plain {plain}");
}
