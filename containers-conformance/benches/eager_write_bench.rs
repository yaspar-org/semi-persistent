// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Does compressing the ACTIVE frame on-write (eager) beat pushing raw writes and
//! compressing lazily at mark? The write path is the e-graph's hottest loop, so
//! this isolates the per-write cost of three active-frame representations:
//!   - plain:  push (val, idx) onto a Vec  (current hot path, O(1) push)
//!   - eager value-major:  hashmap get-or-insert the value to a code, push code+idx
//!     (one hash per write; hot frame is dict + codes + idxs, smaller for D << N)
//!   - eager index-major write-order:  extend the current run if idx is contiguous,
//!     else start a new run (NO hashing; hot frame is runs, smaller for clustered
//!     indices)
//!
//! plus the resulting hot-frame byte size. This says whether the eager write tax is
//! worth the smaller/cache-friendlier hot frame, per workload. It does NOT measure
//! end-to-end e-graph time (a saturation bench does); it measures the write path the
//! idea trades against.

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::collections::HashMap;
use std::hint::black_box;

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

// Writes: `n` entries, values drawn from `distinct`, indices either contiguous
// (a batch update) or scattered.
fn writes(n: usize, distinct: u32, contiguous: bool) -> Vec<(u32, u32)> {
    let mut rng = XorShift(0x1234_5678);
    (0..n)
        .map(|t| {
            let v = (rng.next() as u32) % distinct;
            let i = if contiguous {
                t as u32
            } else {
                (rng.next() as u32) % 1_000_000
            };
            (v, i)
        })
        .collect()
}

// -- the three active-frame write paths --------------------------------------

fn plain(ws: &[(u32, u32)]) -> usize {
    let mut v: Vec<(u32, u32)> = Vec::with_capacity(ws.len());
    for &w in ws {
        v.push(w);
    }
    v.len() * 8 // bytes: (u32,u32) per entry
}

fn eager_value_major(ws: &[(u32, u32)]) -> usize {
    let mut dict: Vec<u32> = Vec::new();
    let mut code_of: HashMap<u32, u32> = HashMap::new();
    let mut codes: Vec<u32> = Vec::with_capacity(ws.len());
    let mut idxs: Vec<u32> = Vec::with_capacity(ws.len());
    for &(val, idx) in ws {
        let code = *code_of.entry(val).or_insert_with(|| {
            dict.push(val);
            (dict.len() - 1) as u32
        });
        codes.push(code);
        idxs.push(idx);
    }
    // Hot-frame bytes: dict (D * 4) + codes (N, packed to ceil(log2 D) bits) + idxs (N*4).
    let d = dict.len().max(1);
    let bits = (usize::BITS - (d - 1).max(1).leading_zeros()) as usize;
    dict.len() * 4 + (codes.len() * bits).div_ceil(8) + idxs.len() * 4
}

fn eager_index_runs(ws: &[(u32, u32)]) -> usize {
    // One run = (start_index, Vec<value>). Extend when idx == last + 1.
    let mut starts: Vec<u32> = Vec::new();
    let mut runs: Vec<Vec<u32>> = Vec::new();
    let mut last: Option<u32> = None;
    for &(val, idx) in ws {
        match last {
            Some(l) if idx == l + 1 => runs.last_mut().unwrap().push(val),
            _ => {
                starts.push(idx);
                runs.push(vec![val]);
            }
        }
        last = Some(idx);
    }
    // Hot-frame bytes: starts (R * 4) + values (N * 4); index column dropped.
    starts.len() * 4 + ws.len() * 4
}

fn bench_eager(c: &mut Criterion) {
    let n = 4096;
    // Three column shapes: union-find (D=4, scattered), contiguous batch (D=N, runs),
    // scattered-unique (D=N, scattered).
    let shapes: &[(&str, Vec<(u32, u32)>)] = &[
        ("union_find_D4_scattered", writes(n, 4, false)),
        ("contiguous_Dn", writes(n, n as u32, true)),
        ("scattered_unique", writes(n, n as u32, false)),
    ];
    let mut g = c.benchmark_group("active_frame_write");
    for (shape, ws) in shapes {
        g.bench_with_input(BenchmarkId::new("plain", shape), ws, |b, ws| {
            b.iter(|| black_box(plain(ws)))
        });
        g.bench_with_input(BenchmarkId::new("eager_value_major", shape), ws, |b, ws| {
            b.iter(|| black_box(eager_value_major(ws)))
        });
        g.bench_with_input(BenchmarkId::new("eager_index_runs", shape), ws, |b, ws| {
            b.iter(|| black_box(eager_index_runs(ws)))
        });
        // Report the resulting hot-frame sizes once (bytes), for the space side.
        eprintln!(
            "  [{shape}] hot bytes: plain {}, eager_value {}, eager_runs {}",
            plain(ws),
            eager_value_major(ws),
            eager_index_runs(ws)
        );
    }
    g.finish();
}

criterion_group!(benches, bench_eager);
criterion_main!(benches);
