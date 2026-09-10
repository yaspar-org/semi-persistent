// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Does parallelizing per-column frame compression across a composite's disjoint
//! columns pay, and above what column-work threshold? A composite (union_find,
//! sparse_set, the e-graph aggregate) is K independent columns; at mark time each
//! flushes/compresses its own frame. This benches K frames compressed sequentially
//! vs on the rayon pool (par_iter), across K (column count) and frame size, to set
//! `parallel::PAR_THRESHOLD` and decide whether the verified `_parallel` twins are
//! worth building. Rayon uses a maintained pool, so this measures work-stealing
//! dispatch, not per-mark thread creation.

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use rayon::prelude::*;
use std::hint::black_box;

use semi_persistent_containers_verus as verus;
use verus::diff_compress::compress;

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

// A union-find-shaped frame: `n` scattered writes drawn from `distinct` values
// (value-major's target, the memory-critical eq-sat column).
fn frame(n: usize, distinct: u32, seed: u64) -> Vec<(u32, u32)> {
    let mut rng = XorShift(0x9E3779B9 ^ seed);
    (0..n)
        .map(|_| {
            (
                (rng.next() as u32) % distinct,
                (rng.next() as u32) % 1_000_000,
            )
        })
        .collect()
}

// K independent columns, each with one frame of `frame_size` writes.
fn columns(k: usize, frame_size: usize) -> Vec<Vec<(u32, u32)>> {
    (0..k).map(|i| frame(frame_size, 64, i as u64)).collect()
}

fn bench_parallel_compress(c: &mut Criterion) {
    let mut g = c.benchmark_group("compress_columns");
    // K = 5 mirrors the e-graph aggregate's leaf-column count; sweep frame size to
    // find where the per-column compress work outweighs dispatch.
    for &k in &[2usize, 5, 10] {
        for &frame_size in &[64usize, 256, 1024, 4096, 16384] {
            let cols = columns(k, frame_size);
            let id = format!("k{k}_frame{frame_size}");

            g.bench_with_input(BenchmarkId::new("sequential", &id), &cols, |b, cols| {
                b.iter(|| {
                    let out: Vec<_> = cols.iter().map(compress::<u32, u32>).collect();
                    black_box(out.len())
                })
            });

            g.bench_with_input(BenchmarkId::new("rayon", &id), &cols, |b, cols| {
                b.iter(|| {
                    let out: Vec<_> = cols.par_iter().map(compress::<u32, u32>).collect();
                    black_box(out.len())
                })
            });
        }
    }
    g.finish();
}

criterion_group!(benches, bench_parallel_compress);
criterion_main!(benches);
