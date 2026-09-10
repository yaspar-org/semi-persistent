// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Does reordering a finalized frame by index before run-coalescing pay?
//!
//! A finalized frame has unique indices (first-write-wins), so its diffs may be
//! reordered without changing the restored state. Sorting by index lets the run
//! encoder capture ALL contiguity, not just runs that happen to be consecutive in
//! capture order. This bench measures the two effects the reorder is supposed to
//! buy:
//!
//!   1. Compression: run count and compressed bytes, write-order vs sort-first,
//!      on a workload whose indices tile contiguous blocks but arrive shuffled.
//!      Also times the encode (the sort-first variant pays a sort).
//!   2. Restore: writing a frame back into a base array entry-by-entry vs
//!      run-by-run (`copy_from_slice` over each contiguous run). Longer runs mean
//!      fewer, larger contiguous writes.
//!
//! The compression numbers are a deterministic table (printed once); the encode
//! and restore costs are criterion.

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use semi_persistent_containers_verus as verus;
use verus::diff_compress::{RunFrame, compress_runs, compress_runs_writeorder};

struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

// A frame whose indices tile `blocks` contiguous ranges of length `run_len`
// (N = blocks * run_len distinct indices), but the diffs arrive SHUFFLED — the
// realistic finalized-frame shape: contiguous regions touched, but not in index
// order. Write-order coalescing sees this as mostly singletons; sorting recovers
// the `blocks` long runs.
fn shuffled_blocks(blocks: usize, run_len: usize) -> Vec<(u32, usize)> {
    let mut out: Vec<(u32, usize)> = Vec::with_capacity(blocks * run_len);
    let mut rng = XorShift(0x9E37_79B9_7F4A_7C15);
    // Gap of `run_len` between blocks, so after sorting the frame has exactly
    // `blocks` runs (not one fused run) — a realistic "contiguous regions,
    // separated by untouched cells" shape.
    let stride = run_len * 2;
    for b in 0..blocks {
        for o in 0..run_len {
            out.push(((rng.next() & 0xFFFF) as u32, b * stride + o));
        }
    }
    // Fisher-Yates shuffle (deterministic).
    for i in (1..out.len()).rev() {
        let j = (rng.next() % (i as u64 + 1)) as usize;
        out.swap(i, j);
    }
    out
}

fn sorted_by_index(mut d: Vec<(u32, usize)>) -> Vec<(u32, usize)> {
    d.sort_by_key(|&(_, i)| i);
    d
}

// Restore a run frame into a base array, entry by entry.
fn restore_entrywise(frame: &RunFrame<u32>, base: &mut [u32]) {
    for r in 0..frame.starts.len() {
        let start = frame.starts[r];
        let run = &frame.vals[r];
        for (o, &v) in run.iter().enumerate() {
            base[start + o] = v;
        }
    }
}

// Restore a run frame into a base array, one contiguous slice per run.
fn restore_runwise(frame: &RunFrame<u32>, base: &mut [u32]) {
    for r in 0..frame.starts.len() {
        let start = frame.starts[r];
        let run = &frame.vals[r];
        base[start..start + run.len()].copy_from_slice(run);
    }
}

fn run_bytes(frame: &RunFrame<u32>) -> (usize, usize) {
    let n: usize = frame.vals.iter().map(|v| v.len()).sum();
    let bytes = frame.starts.len() * std::mem::size_of::<usize>() + n * std::mem::size_of::<u32>();
    (frame.starts.len(), bytes)
}

fn report_compression() {
    use std::sync::atomic::{AtomicBool, Ordering};
    static DONE: AtomicBool = AtomicBool::new(false);
    if DONE.swap(true, Ordering::Relaxed) {
        return;
    }
    eprintln!("\n=== reorder-before-coalesce: runs and bytes (write-order vs sorted) ===");
    eprintln!(
        "  {:>8} {:>8} {:>10} {:>18} {:>18}",
        "N", "run_len", "plain_B", "writeorder(runs/B)", "sorted(runs/B)"
    );
    for &(blocks, run_len) in &[(1000usize, 4usize), (500, 16), (100, 64), (20, 256)] {
        let n = blocks * run_len;
        let diffs = shuffled_blocks(blocks, run_len);
        let wo = compress_runs_writeorder(&diffs);
        let so = compress_runs(&sorted_by_index(diffs.clone()));
        let (wr, wb) = run_bytes(&wo);
        let (sr, sb) = run_bytes(&so);
        let plain = n * std::mem::size_of::<(u32, usize)>();
        eprintln!(
            "  {:>8} {:>8} {:>10} {:>9}/{:>7} {:>9}/{:>7}",
            n, run_len, plain, wr, wb, sr, sb
        );
    }
    eprintln!("  (sorted recovers `blocks` runs; write-order sees ~N singletons after shuffle)\n");
}

fn bench_encode(c: &mut Criterion) {
    report_compression();
    let mut g = c.benchmark_group("reorder/encode");
    for &(blocks, run_len) in &[(500usize, 16usize), (100, 64)] {
        let n = blocks * run_len;
        let diffs = shuffled_blocks(blocks, run_len);
        g.bench_with_input(BenchmarkId::new("writeorder", n), &diffs, |b, d| {
            b.iter(|| black_box(compress_runs_writeorder(black_box(d))))
        });
        g.bench_with_input(BenchmarkId::new("sort_then_runs", n), &diffs, |b, d| {
            b.iter(|| {
                let s = sorted_by_index(d.clone());
                black_box(compress_runs(black_box(&s)))
            })
        });
    }
    g.finish();
}

fn bench_restore(c: &mut Criterion) {
    let mut g = c.benchmark_group("reorder/restore");
    // Sorted frames (long runs) so the run-slice path has contiguous runs to copy.
    for &(blocks, run_len) in &[(500usize, 16usize), (100, 64), (20, 256)] {
        let n = blocks * run_len;
        let frame = compress_runs(&sorted_by_index(shuffled_blocks(blocks, run_len)));
        // Indices span up to blocks*stride (stride = 2*run_len) with the gaps.
        let mut base = vec![0u32; blocks * run_len * 2 + 1];
        g.bench_with_input(BenchmarkId::new("entrywise", n), &frame, |b, f| {
            b.iter(|| restore_entrywise(black_box(f), black_box(&mut base)))
        });
        g.bench_with_input(BenchmarkId::new("runwise_slice", n), &frame, |b, f| {
            b.iter(|| restore_runwise(black_box(f), black_box(&mut base)))
        });
    }
    g.finish();
}

criterion_group!(benches, bench_encode, bench_restore);
criterion_main!(benches);
