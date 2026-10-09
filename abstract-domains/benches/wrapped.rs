use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use semi_persistent_abstract_domains::interval::Interval;
use semi_persistent_abstract_domains::lattice::Domain;
use semi_persistent_abstract_domains::semantics::{Signed, Unsigned};
use semi_persistent_abstract_domains::transfer::{Arith, DivRem};
use semi_persistent_abstract_domains::wrapped::WrappedU64;

fn bench_wrapped_vs_interval(c: &mut Criterion) {
    let mut group = c.benchmark_group("Wrapped_vs_Interval_U64");

    // Non-wrapping continuous ranges
    let i1 = Interval::<u64>::new(100, 500).unwrap();
    let i2 = Interval::<u64>::new(400, 800).unwrap();
    let w1 = WrappedU64::new(100, 500);
    let w2 = WrappedU64::new(400, 800);

    // Join comparison
    group.bench_function("interval_join", |b| {
        b.iter(|| black_box(&i1).join(black_box(&i2)))
    });
    group.bench_function("wrapped_join_non_wrapping", |b| {
        b.iter(|| black_box(&w1).join(black_box(&w2)))
    });

    // Unsigned Add comparison
    group.bench_function("interval_add", |b| {
        b.iter(|| <Interval<u64> as Arith<Unsigned<u64>>>::add(black_box(&i1), black_box(&i2)))
    });
    group.bench_function("wrapped_add_non_wrapping", |b| {
        b.iter(|| <WrappedU64 as Arith<Unsigned<u64>>>::add(black_box(&w1), black_box(&w2)))
    });

    // Unsigned Division comparison
    group.bench_function("interval_udiv", |b| {
        b.iter(|| <Interval<u64> as DivRem<Unsigned<u64>>>::div(black_box(&i1), black_box(&i2)))
    });
    group.bench_function("wrapped_udiv_fast_path", |b| {
        b.iter(|| <WrappedU64 as DivRem<Unsigned<u64>>>::div(black_box(&w1), black_box(&w2)))
    });

    group.finish();
}

fn bench_wrapped_division_cases(c: &mut Criterion) {
    let mut group = c.benchmark_group("Wrapped_Division_Cases_U64");

    let small_pos_1 = WrappedU64::new(10, 50);
    let small_pos_2 = WrappedU64::new(2, 5);
    let wrapping_1 = WrappedU64::new(u64::MAX - 200, 100);
    let wrapping_2 = WrappedU64::new(u64::MAX - 50, 20);

    // Unsigned: fast-path vs wrapping loop
    group.bench_function("udiv_fast_path", |b| {
        b.iter(|| <WrappedU64 as DivRem<Unsigned<u64>>>::div(black_box(&small_pos_1), black_box(&small_pos_2)))
    });
    group.bench_function("udiv_wrapping_loop", |b| {
        b.iter(|| <WrappedU64 as DivRem<Unsigned<u64>>>::div(black_box(&wrapping_1), black_box(&wrapping_2)))
    });

    // Signed: fast-path vs wrapping 4x4 loop
    group.bench_function("sdiv_fast_path", |b| {
        b.iter(|| <WrappedU64 as DivRem<Signed<u64>>>::div(black_box(&small_pos_1), black_box(&small_pos_2)))
    });
    group.bench_function("sdiv_wrapping_loop", |b| {
        b.iter(|| <WrappedU64 as DivRem<Signed<u64>>>::div(black_box(&wrapping_1), black_box(&wrapping_2)))
    });

    group.finish();
}

criterion_group!(benches, bench_wrapped_vs_interval, bench_wrapped_division_cases);
criterion_main!(benches);