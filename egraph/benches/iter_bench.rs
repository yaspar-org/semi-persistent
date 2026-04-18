// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use criterion::{Criterion, criterion_group, criterion_main};
use semi_persistent_containers::{ShrinkPolicy, VecI, VecP};

fn bench_iteration(c: &mut Criterion) {
    let n = 100_000;

    // --- Bitset: has as_slice() ---
    let mut bitset = VecP::<u32, u32>::new();
    for i in 0..n {
        bitset.push(i);
    }
    let _t = bitset.mark(ShrinkPolicy::Never);

    c.bench_function("bitset/slice_iter", |b| {
        b.iter(|| {
            let slice = bitset.as_slice().unwrap();
            let mut sum = 0u64;
            for &v in slice {
                sum += v as u64;
            }
            std::hint::black_box(sum);
        })
    });

    c.bench_function("bitset/view_iter", |b| {
        b.iter(|| {
            let view = bitset.view();
            let mut sum = 0u64;
            for v in view.iter() {
                sum += v as u64;
            }
            std::hint::black_box(sum);
        })
    });

    // --- Marked: no as_slice(), view only ---
    let mut marked = VecI::<u32, u32>::new();
    for i in 0..n {
        marked.push(i);
    }
    let _t = marked.mark(ShrinkPolicy::Never);

    assert!(
        marked.as_slice().is_none(),
        "Marked should not expose slice"
    );

    c.bench_function("marked/view_iter", |b| {
        b.iter(|| {
            let view = marked.view();
            let mut sum = 0u64;
            for v in view.iter() {
                sum += v as u64;
            }
            std::hint::black_box(sum);
        })
    });
}

criterion_group!(benches, bench_iteration);
criterion_main!(benches);
