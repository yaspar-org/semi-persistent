// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use semi_persistent_containers::{ShrinkPolicy, VecI, VecP};
use std::hint::black_box;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Fill a `VecP<u32, usize>` with `n` elements, no marks active.
fn fill_p(v: &mut VecP<u32, usize>, n: usize) {
    for i in 0..n {
        v.push((i as u32) & 0x7FFF_FFFF);
    }
}

/// Mutate `k` distinct cells in a `VecP<u32, usize>` of size `n`.
fn mutate_p(v: &mut VecP<u32, usize>, n: usize, k: usize) {
    for i in 0..k {
        v.set(i % n, (i as u32 + 999) & 0x7FFF_FFFF);
    }
}

/// Fill a `VecI<u32, usize>` with `n` elements, no marks active.
fn fill_i(v: &mut VecI<u32, usize>, n: usize) {
    for i in 0..n {
        v.push((i as u32) & 0x7FFF_FFFF);
    }
}

/// Mutate `k` distinct cells in a `VecI<u32, usize>` of size `n`.
fn mutate_i(v: &mut VecI<u32, usize>, n: usize, k: usize) {
    for i in 0..k {
        v.set(i % n, (i as u32 + 999) & 0x7FFF_FFFF);
    }
}

// ---------------------------------------------------------------------------
// mark() cost — the key differentiator
// ---------------------------------------------------------------------------

fn bench_mark(c: &mut Criterion) {
    let mut group = c.benchmark_group("mark");
    for n in [1_000, 10_000, 100_000, 1_000_000] {
        // Dirty half the cells before each mark to exercise prepare_mark.
        let k = n / 2;

        group.bench_with_input(BenchmarkId::new("bitset", n), &n, |b, &n| {
            let mut v = VecP::<u32, usize>::new();
            fill_p(&mut v, n);
            b.iter(|| {
                let t = v.mark(ShrinkPolicy::Never);
                mutate_p(&mut v, n, k);
                v.restore(t);
            });
        });

        group.bench_with_input(BenchmarkId::new("epoch", n), &n, |b, &n| {
            let mut v = VecP::<u32, usize>::new();
            fill_p(&mut v, n);
            b.iter(|| {
                let t = v.mark(ShrinkPolicy::Never);
                mutate_p(&mut v, n, k);
                v.restore(t);
            });
        });

        group.bench_with_input(BenchmarkId::new("marked", n), &n, |b, &n| {
            let mut v = VecI::<u32, usize>::new();
            fill_i(&mut v, n);
            b.iter(|| {
                let t = v.mark(ShrinkPolicy::Never);
                mutate_i(&mut v, n, k);
                v.restore(t);
            });
        });
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// set() throughput — guard check overhead
// ---------------------------------------------------------------------------

fn bench_set(c: &mut Criterion) {
    let mut group = c.benchmark_group("set");
    let n = 100_000;
    let k: usize = 1_000;

    group.bench_function("bitset", |b| {
        let mut v = VecP::<u32, usize>::new();
        fill_p(&mut v, n);
        let t = v.mark(ShrinkPolicy::Never);
        b.iter(|| {
            for i in 0..k {
                v.set(i, black_box(42));
            }
        });
        v.restore(t);
    });

    group.bench_function("epoch", |b| {
        let mut v = VecP::<u32, usize>::new();
        fill_p(&mut v, n);
        let t = v.mark(ShrinkPolicy::Never);
        b.iter(|| {
            for i in 0..k {
                v.set(i, black_box(42));
            }
        });
        v.restore(t);
    });

    group.bench_function("marked", |b| {
        let mut v = VecI::<u32, usize>::new();
        fill_i(&mut v, n);
        let t = v.mark(ShrinkPolicy::Never);
        b.iter(|| {
            for i in 0..k {
                v.set(i, black_box(42));
            }
        });
        v.restore(t);
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// get() throughput — Markable pays a mask
// ---------------------------------------------------------------------------

fn bench_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("get");
    let n = 100_000;

    group.bench_function("bitset", |b| {
        let mut v = VecP::<u32, usize>::new();
        fill_p(&mut v, n);
        b.iter(|| {
            let mut sum = 0u32;
            for i in 0..n {
                sum = sum.wrapping_add(v.get(i));
            }
            black_box(sum);
        });
    });

    group.bench_function("epoch", |b| {
        let mut v = VecP::<u32, usize>::new();
        fill_p(&mut v, n);
        b.iter(|| {
            let mut sum = 0u32;
            for i in 0..n {
                sum = sum.wrapping_add(v.get(i));
            }
            black_box(sum);
        });
    });

    group.bench_function("marked", |b| {
        let mut v = VecI::<u32, usize>::new();
        fill_i(&mut v, n);
        b.iter(|| {
            let mut sum = 0u32;
            for i in 0..n {
                sum = sum.wrapping_add(v.get(i));
            }
            black_box(sum);
        });
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// backtrack() cost — varying diff sizes
// ---------------------------------------------------------------------------

fn bench_backtrack(c: &mut Criterion) {
    let mut group = c.benchmark_group("backtrack");
    let n = 100_000;

    for k in [100, 1_000, 10_000, 50_000] {
        group.bench_with_input(BenchmarkId::new("bitset", k), &k, |b, &k| {
            let mut v = VecP::<u32, usize>::new();
            fill_p(&mut v, n);
            b.iter(|| {
                let t = v.mark(ShrinkPolicy::Never);
                mutate_p(&mut v, n, k);
                v.restore(t);
            });
        });

        group.bench_with_input(BenchmarkId::new("epoch", k), &k, |b, &k| {
            let mut v = VecP::<u32, usize>::new();
            fill_p(&mut v, n);
            b.iter(|| {
                let t = v.mark(ShrinkPolicy::Never);
                mutate_p(&mut v, n, k);
                v.restore(t);
            });
        });

        group.bench_with_input(BenchmarkId::new("marked", k), &k, |b, &k| {
            let mut v = VecI::<u32, usize>::new();
            fill_i(&mut v, n);
            b.iter(|| {
                let t = v.mark(ShrinkPolicy::Never);
                mutate_i(&mut v, n, k);
                v.restore(t);
            });
        });
    }
    group.finish();
}

// ---------------------------------------------------------------------------
// Realistic: mark → mutate K of N → mark → mutate → backtrack (nested)
// ---------------------------------------------------------------------------

fn bench_nested_mark_backtrack(c: &mut Criterion) {
    let mut group = c.benchmark_group("nested");
    let n = 100_000;
    let k = 1_000; // mutations per frame
    let depth = 10; // nesting depth

    group.bench_function("bitset", |b| {
        let mut v = VecP::<u32, usize>::new();
        fill_p(&mut v, n);
        b.iter(|| {
            let mut tokens = Vec::with_capacity(depth);
            for d in 0..depth {
                tokens.push(v.mark(ShrinkPolicy::Never));
                mutate_p(&mut v, n, k);
                // Also push some elements per frame.
                for j in 0..100 {
                    v.push(((d * 100 + j) as u32) & 0x7FFF_FFFF);
                }
            }
            // Backtrack all the way to the first mark.
            v.restore(tokens[0]);
        });
    });

    group.bench_function("epoch", |b| {
        let mut v = VecP::<u32, usize>::new();
        fill_p(&mut v, n);
        b.iter(|| {
            let mut tokens = Vec::with_capacity(depth);
            for d in 0..depth {
                tokens.push(v.mark(ShrinkPolicy::Never));
                mutate_p(&mut v, n, k);
                for j in 0..100 {
                    v.push(((d * 100 + j) as u32) & 0x7FFF_FFFF);
                }
            }
            v.restore(tokens[0]);
        });
    });

    group.bench_function("marked", |b| {
        let mut v = VecI::<u32, usize>::new();
        fill_i(&mut v, n);
        b.iter(|| {
            let mut tokens = Vec::with_capacity(depth);
            for d in 0..depth {
                tokens.push(v.mark(ShrinkPolicy::Never));
                mutate_i(&mut v, n, k);
                for j in 0..100 {
                    v.push(((d * 100 + j) as u32) & 0x7FFF_FFFF);
                }
            }
            v.restore(tokens[0]);
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_mark,
    bench_set,
    bench_get,
    bench_backtrack,
    bench_nested_mark_backtrack,
);
criterion_main!(benches);
