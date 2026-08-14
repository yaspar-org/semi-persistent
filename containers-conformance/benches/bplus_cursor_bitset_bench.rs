// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Production-vs-verus comparison for the three drop-in replacements the
//! retained-containers bench did not cover: the B+ tree (insert, point
//! lookup via cursor seek, bulk build), the sorted cursor's seek/step scan
//! over tree leaves, and the bit set. Same shape as
//! `retained_containers_bench.rs`: one group per workload, `prod` and
//! `verus` arms, shuffled keys so production's `last_leaf` append fast path
//! cannot fire (see `tests/bplus_search_parity.rs`).

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

prod::define_id31! { pub struct PId / StoredPId, "p"; }
verus::define_id31! { pub struct VId / StoredVId, "v"; }

type ProdTree =
    prod::bplus::BPlusTreeSet<PId, prod::bplus::Layout256, prod::bplus::BinarySearch, false>;
type VerusTree = verus::bplus::BPlusTreeSet<
    VId,
    verus::bplus_layout::Layout256,
    verus::bplus_search::BinarySearch,
    false,
>;
type ProdTreeBr =
    prod::bplus::BPlusTreeSet<PId, prod::bplus::Layout256, prod::bplus::Branchless, false>;
type VerusTreeBr = verus::bplus::BPlusTreeSet<
    VId,
    verus::bplus_layout::Layout256,
    verus::bplus_search::Branchless,
    false,
>;

const N: u32 = 1 << 14;

fn shuffled(n: u32) -> Vec<u32> {
    let mut v: Vec<u32> = (0..n).collect();
    let mut st = 0x2545_F491_4F6C_DD1Du64;
    for i in (1..v.len()).rev() {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        let j = (st >> 33) as usize % (i + 1);
        v.swap(i, j);
    }
    v
}

fn bench_bplus_insert(c: &mut Criterion) {
    let keys = shuffled(N);
    let mut g = c.benchmark_group("bplus/insert_shuffled");
    g.bench_function("prod", |b| {
        b.iter_batched(
            ProdTree::new,
            |mut t| {
                for &k in &keys {
                    t.insert(PId::new(k));
                }
                black_box(t.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.bench_function("verus", |b| {
        b.iter_batched(
            VerusTree::new,
            |mut t| {
                for &k in &keys {
                    t.try_insert(VId::new(k)).expect("bench: within capacity");
                }
                black_box(t.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.finish();
}

fn bench_bplus_seek(c: &mut Criterion) {
    let keys = shuffled(N);
    let mut pt = ProdTree::new();
    let mut vt = VerusTree::new();
    for &k in &keys {
        pt.insert(PId::new(k));
        vt.try_insert(VId::new(k)).expect("bench: within capacity");
    }
    let probes = shuffled(N);
    let mut g = c.benchmark_group("bplus/cursor_seek");
    g.bench_function("prod", |b| {
        b.iter(|| {
            let mut hits = 0u32;
            for &k in &probes {
                let mut c = pt.cursor();
                c.seek(PId::new(k));
                if c.key() == Some(PId::new(k)) {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });
    g.bench_function("verus", |b| {
        b.iter(|| {
            let mut hits = 0u32;
            for &k in &probes {
                let mut c = vt.cursor();
                c.seek(VId::new(k));
                if c.key() == Some(VId::new(k)) {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });
    g.finish();
}

fn bench_bplus_from_sorted_scan(c: &mut Criterion) {
    let pkeys: Vec<PId> = (0..N).map(PId::new).collect();
    let vkeys: Vec<VId> = (0..N).map(VId::new).collect();
    let mut g = c.benchmark_group("bplus/from_sorted_then_scan");
    g.bench_function("prod", |b| {
        b.iter(|| {
            let t = ProdTree::from_sorted(&pkeys);
            let mut cur = t.cursor();
            let mut acc = 0u64;
            while let Some(k) = cur.key() {
                acc = acc.wrapping_add(k.raw() as u64);
                cur.step();
            }
            black_box(acc)
        })
    });
    g.bench_function("verus", |b| {
        b.iter(|| {
            let t = VerusTree::try_from_sorted(&vkeys).expect("bench: sorted input");
            let mut cur = t.cursor();
            let mut acc = 0u64;
            while let Some(k) = cur.key() {
                acc = acc.wrapping_add(k.raw() as u64);
                cur.step();
            }
            black_box(acc)
        })
    });
    g.finish();
}

// Branchless arms mirror the BinarySearch groups above. The verified tree
// dispatches in-node search through its `S` parameter (bplus.rs
// leaf_find_ge/find_child route to S::find_ge/find_gt), so these arms
// exercise the branch-free linear scan on both sides.
fn bench_bplus_insert_branchless(c: &mut Criterion) {
    let keys = shuffled(N);
    let mut g = c.benchmark_group("bplus/insert_shuffled_branchless");
    g.bench_function("prod", |b| {
        b.iter_batched(
            ProdTreeBr::new,
            |mut t| {
                for &k in &keys {
                    t.insert(PId::new(k));
                }
                black_box(t.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.bench_function("verus", |b| {
        b.iter_batched(
            VerusTreeBr::new,
            |mut t| {
                for &k in &keys {
                    t.try_insert(VId::new(k)).expect("bench: within capacity");
                }
                black_box(t.len())
            },
            BatchSize::LargeInput,
        )
    });
    g.finish();
}

fn bench_bplus_seek_branchless(c: &mut Criterion) {
    let keys = shuffled(N);
    let mut pt = ProdTreeBr::new();
    let mut vt = VerusTreeBr::new();
    for &k in &keys {
        pt.insert(PId::new(k));
        vt.try_insert(VId::new(k)).expect("bench: within capacity");
    }
    let probes = shuffled(N);
    let mut g = c.benchmark_group("bplus/cursor_seek_branchless");
    g.bench_function("prod", |b| {
        b.iter(|| {
            let mut hits = 0u32;
            for &k in &probes {
                let mut c = pt.cursor();
                c.seek(PId::new(k));
                if c.key() == Some(PId::new(k)) {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });
    g.bench_function("verus", |b| {
        b.iter(|| {
            let mut hits = 0u32;
            for &k in &probes {
                let mut c = vt.cursor();
                c.seek(VId::new(k));
                if c.key() == Some(VId::new(k)) {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });
    g.finish();
}

fn bench_bitset(c: &mut Criterion) {
    let mut g = c.benchmark_group("bitset/set_test_churn");
    g.bench_function("prod", |b| {
        let mut s = prod::bitset::BitSet::new(N as usize);
        b.iter(|| {
            let mut acc = 0u32;
            let mut x = 0x9E37_79B9u64;
            for _ in 0..N {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let i = (x % N as u64) as usize;
                s.set(i);
                if s.test(i.wrapping_add(1) % N as usize) {
                    acc += 1;
                }
            }
            s.clear_all();
            black_box(acc)
        })
    });
    g.bench_function("verus", |b| {
        let mut s = verus::bitset::BitSet::new(N as usize);
        b.iter(|| {
            let mut acc = 0u32;
            let mut x = 0x9E37_79B9u64;
            for _ in 0..N {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let i = (x % N as u64) as usize;
                s.set(i);
                if s.test(i.wrapping_add(1) % N as usize) {
                    acc += 1;
                }
            }
            s.clear_all();
            black_box(acc)
        })
    });
    g.finish();
}

criterion_group!(
    benches,
    bench_bplus_insert,
    bench_bplus_seek,
    bench_bplus_from_sorted_scan,
    bench_bplus_insert_branchless,
    bench_bplus_seek_branchless,
    bench_bitset
);
criterion_main!(benches);
