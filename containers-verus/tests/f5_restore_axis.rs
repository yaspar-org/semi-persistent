// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! F5.2, the restore-time axis: per-mode restore wall on a REPRESENTATIVE
//! EqSat frame (the sweep's median big ENodeId frame: 4,530 entries, 103
//! distinct values, 173 sorted index runs), alongside each mode's real
//! encoded size. Run with:
//!
//!   cargo test --release --test f5_restore_axis -- --ignored --nocapture

use std::time::Instant;

use semi_persistent_containers_verus::diff_compress::{ColdFrame, RunCol, compress};
use semi_persistent_containers_verus::layered::LayeredFrame;
use semi_persistent_containers_verus::value_compressor::ValueDictC;

const ENTRIES: usize = 4530;
const DISTINCT: u32 = 103;
const RUNS: usize = 173;
const TARGET: usize = 60_000;
const REPS: usize = 2000;

/// The representative frame: RUNS contiguous spans whose lengths sum to
/// ENTRIES, values from a DISTINCT-symbol alphabet, span starts scattered.
fn representative_frame() -> Vec<(u32, u32)> {
    let per = ENTRIES / RUNS;
    let mut d = Vec::with_capacity(ENTRIES);
    let mut seed = 0x9e3779b97f4a7c15u64;
    for r in 0..RUNS {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let start = (seed % (TARGET as u64 - per as u64)) as u32;
        let len = if r == RUNS - 1 {
            ENTRIES - per * (RUNS - 1)
        } else {
            per
        };
        for k in 0..len as u32 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            d.push(((seed % DISTINCT as u64) as u32, start + k));
        }
    }
    // Unique indices (last-write-wins dedup, the seal-path shape).
    let mut seen = std::collections::HashSet::new();
    d.retain(|&(_, i)| seen.insert(i));
    d
}

fn time_restore<F: Fn(&mut Vec<u32>)>(label: &str, bytes: usize, f: F) {
    let mut target = vec![0u32; TARGET];
    // Warm.
    f(&mut target);
    let t = Instant::now();
    for _ in 0..REPS {
        f(&mut target);
    }
    let per = t.elapsed().as_secs_f64() * 1e6 / REPS as f64;
    println!("{label:26} {bytes:>8} B   {per:>8.1} us/restore");
}

#[test]
#[ignore = "measurement; run with --ignored --nocapture"]
fn restore_axis_on_representative_frame() {
    let diffs = representative_frame();
    println!(
        "frame: {} entries, {} distinct, {} sorted runs, target {}",
        diffs.len(),
        DISTINCT,
        RUNS,
        TARGET
    );

    let plain: ColdFrame<u32, u32> = ColdFrame::plain_copy(&diffs);
    time_restore("plain (scattered)", plain.byte_len(), |t| {
        plain.restore_to(t)
    });

    let rc = RunCol::compress_sorted(&diffs);
    let runs_frame: ColdFrame<u32, u32> = ColdFrame::Runs(rc);
    time_restore("sorted runs (memcpy)", runs_frame.byte_len(), |t| {
        runs_frame.restore_to(t)
    });

    let dict = compress(&diffs);
    let dict_frame: ColdFrame<u32, u32> = ColdFrame::Dict(dict);
    time_restore("dict (scattered decode)", dict_frame.byte_len(), |t| {
        dict_frame.restore_to(t)
    });

    let lay_sorted = LayeredFrame::<u32, u32, ValueDictC>::compress_runs_sorted(&diffs);
    time_restore("sorted runs x dict", lay_sorted.byte_len(), |t| {
        lay_sorted.restore_to(t)
    });

    let lay_plain = LayeredFrame::<u32, u32, ValueDictC>::compress_plain(&diffs);
    time_restore("plain x dict", lay_plain.byte_len(), |t| {
        lay_plain.restore_to(t)
    });
}
