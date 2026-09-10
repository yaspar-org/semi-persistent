// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Diff-compression benches: the cost and benefit of the two finalized-frame
//! encoders, measured on the column shapes each targets.
//!
//! - Value-major (`DictFrame`, `compress`/`decode_exec`): a union-find parent
//!   column, where a mark's stratum captures many cells whose old value was one
//!   of a few representatives. Swept over the dedup ratio `D/N` (distinct values
//!   over entries).
//! - Index-major (`RunFrame`, `compress_runs`): a batch update over contiguous
//!   index ranges, so the diffs form `R` runs of consecutive indices. Swept over
//!   `R/N` (runs over entries); a run drops its whole index column.
//!
//! Timing is criterion; the space comparison is a deterministic table printed to
//! stderr once (bytes are a function of the shape, not a measurement), because
//! whether an encoder saves space is arithmetic, not wall-clock.

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use semi_persistent_containers_verus as verus;
use verus::diff_compress::{compress, compress_runs};

// Deterministic xorshift, seeded per-workload; no rand/Date dependency (the
// harness forbids nondeterministic sources, and a fixed seed keeps the shape
// reproducible across runs).
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
    fn below(&mut self, n: u32) -> u32 {
        (self.next() % n as u64) as u32
    }
}

// A union-find-shaped stratum: `n` diffs, each a distinct scattered cell index
// (a permutation prefix) whose old value is one of `distinct` representatives.
// This is the value-major target: few distinct values, scattered indices.
fn dict_workload(n: usize, distinct: u32) -> Vec<(u32, u32)> {
    let mut rng = XorShift(0x2545F491 ^ (n as u64).wrapping_mul(0x9E37_79B9));
    // Indices: 0..n shuffled (each cell captured at most once per frame — the
    // first-write-wins bound), so the index column is a scattered permutation.
    let mut idxs: Vec<u32> = (0..n as u32).collect();
    for i in (1..idxs.len()).rev() {
        let j = rng.below((i + 1) as u32) as usize;
        idxs.swap(i, j);
    }
    idxs.into_iter()
        .map(|idx| (rng.below(distinct), idx))
        .collect()
}

// An index-major-shaped stratum: `runs` runs of consecutive indices tiling
// `0..n`, each cell's old value arbitrary. This is the run-coalescing target:
// the index column is implied by run start + offset.
fn runs_workload(n: usize, runs: usize) -> Vec<(u32, usize)> {
    let mut rng = XorShift(0x1D2C_6E43 ^ (n as u64).wrapping_mul(0x85EB_CA6B));
    let per = n / runs;
    let mut out: Vec<(u32, usize)> = Vec::with_capacity(n);
    let mut idx: usize = 0;
    for _ in 0..runs {
        for _ in 0..per {
            out.push((rng.below(1 << 20), idx));
            idx += 1;
        }
    }
    while idx < n {
        out.push((rng.below(1 << 20), idx));
        idx += 1;
    }
    out
}

fn bench_dict_encode(c: &mut Criterion) {
    report_space();
    let mut g = c.benchmark_group("diff_compress/dict_encode");
    for &n in &[1_000usize, 10_000, 100_000] {
        for &ratio in &[100u32, 10] {
            let distinct = (n as u32 / ratio).max(1);
            let diffs = dict_workload(n, distinct);
            g.bench_with_input(
                BenchmarkId::new(format!("N{n}_D{}", n as u32 / ratio), ratio),
                &diffs,
                |b, diffs| b.iter(|| black_box(compress(black_box(diffs)))),
            );
        }
    }
    g.finish();
}

fn bench_dict_decode(c: &mut Criterion) {
    let mut g = c.benchmark_group("diff_compress/dict_decode");
    for &n in &[1_000usize, 10_000, 100_000] {
        for &ratio in &[100u32, 10] {
            let distinct = (n as u32 / ratio).max(1);
            let frame = compress(&dict_workload(n, distinct));
            g.bench_with_input(
                BenchmarkId::new(format!("N{n}_D{}", n as u32 / ratio), ratio),
                &frame,
                |b, frame| b.iter(|| black_box(frame.decode_exec())),
            );
        }
    }
    g.finish();
}

fn bench_runs_encode(c: &mut Criterion) {
    let mut g = c.benchmark_group("diff_compress/runs_encode");
    for &n in &[1_000usize, 10_000, 100_000] {
        for &runs in &[n / 100, n / 10] {
            let runs = runs.max(1);
            let diffs = runs_workload(n, runs);
            g.bench_with_input(
                BenchmarkId::new(format!("N{n}_R{runs}"), runs),
                &diffs,
                |b, diffs| b.iter(|| black_box(compress_runs(black_box(diffs)))),
            );
        }
    }
    g.finish();
}

// -- space report ------------------------------------------------------------

// Bytes a plain frame occupies: one `(T, I)` per entry.
fn plain_bytes(n: usize) -> usize {
    n * std::mem::size_of::<(u32, u32)>()
}

// Bytes the value-dictionary occupies as built today (codes are `usize`), and
// as it would be with narrowed `u32` codes. `dict`: distinct values; `codes`:
// one per entry; `idxs`: one per entry (still stored explicitly — value-major
// does not drop the index column for scattered indices).
fn dict_bytes_usize_codes(n: usize, distinct: usize) -> usize {
    distinct * std::mem::size_of::<u32>()      // dict
        + n * std::mem::size_of::<usize>()     // codes (usize, as built)
        + n * std::mem::size_of::<u32>() // idxs
}
fn dict_bytes_u32_codes(n: usize, distinct: usize) -> usize {
    distinct * std::mem::size_of::<u32>()
        + n * std::mem::size_of::<u32>()       // codes narrowed to u32
        + n * std::mem::size_of::<u32>()
}

// Bytes a run frame occupies: `starts` (one usize per run) plus `vals` (one T
// per entry). The index column is gone — implied by start + offset.
fn runs_bytes(n: usize, runs: usize) -> usize {
    runs * std::mem::size_of::<usize>()        // starts
        + n * std::mem::size_of::<u32>() // vals (flattened)
}

fn report_space() {
    use std::sync::atomic::{AtomicBool, Ordering};
    static DONE: AtomicBool = AtomicBool::new(false);
    if DONE.swap(true, Ordering::Relaxed) {
        return;
    }
    eprintln!("\n=== diff-compression space (bytes; ratio vs plain, <1.0 is a win) ===");
    eprintln!("value-major (DictFrame), union-find shape:");
    eprintln!(
        "  {:>8} {:>8} {:>10} {:>14} {:>14} {:>13}",
        "N", "distinct", "plain", "dict(usize)", "dict(u32)", "runs-equiv"
    );
    for &n in &[1_000usize, 10_000, 100_000] {
        for &ratio in &[100usize, 10] {
            let distinct = (n / ratio).max(1);
            let p = plain_bytes(n);
            let du = dict_bytes_usize_codes(n, distinct);
            let d4 = dict_bytes_u32_codes(n, distinct);
            eprintln!(
                "  {:>8} {:>8} {:>10} {:>10} {:>4.2}x {:>10} {:>4.2}x {:>13}",
                n,
                distinct,
                p,
                du,
                du as f64 / p as f64,
                d4,
                d4 as f64 / p as f64,
                "-",
            );
        }
    }
    eprintln!("index-major (RunFrame), contiguous-range shape:");
    eprintln!("  {:>8} {:>8} {:>10} {:>14}", "N", "runs", "plain", "runs");
    for &n in &[1_000usize, 10_000, 100_000] {
        for &rratio in &[100usize, 10] {
            let runs = (n / rratio).max(1);
            let p = plain_bytes(n);
            let r = runs_bytes(n, runs);
            eprintln!(
                "  {:>8} {:>8} {:>10} {:>10} {:>4.2}x",
                n,
                runs,
                p,
                r,
                r as f64 / p as f64
            );
        }
    }
    eprintln!();
}

criterion_group!(
    benches,
    bench_dict_encode,
    bench_dict_decode,
    bench_runs_encode
);
criterion_main!(benches);
