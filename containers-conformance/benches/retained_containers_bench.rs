// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Phase 9.5 bench gate: the RETAINED containers (plan rev 3) — Vec
//! mark/restore and ListArena ops — verus vs production, same traces.
//! Gate: verus within 10% of production on each pair, or a reviewed
//! exception recorded in the PR. (The B+tree benches are data, gating
//! nothing, and live in compat_bplus_bench.rs / incremental_vs_rebuild.rs.)
//!
//! Workloads model the e-graph consumer:
//! - `vec/mark_set_restore`: interleaved set-heavy work under a mark, then
//!   restore — the union-find / caches / classes rollback pattern.
//! - `vec/push_pop_untracked`: TRACK=false push/pop — the plain-store use.
//! - `list/append_iter`: build many small lists, iterate them — the use-list
//!   build + walk pattern.
//! - `list/splice`: repeated list concatenation — the merge pattern.
//!
//! ## Baseline history
//!
//! Original exception record (Phase 9.5, before fixes 1 & 2):
//! vec/mark_set_restore +14%, vec/push_pop_untracked +112%,
//! list/append_iter +309%, list/splice +473%.
//!
//! ## Current (2026-07-26, after lazy CaptureBits + TRACK erasure (fix 2)
//! ## and niche-packed list nodes/heads (fix 1))
//!
//! | bench | production | verus | delta |
//! |---|---|---|---|
//! | vec/mark_set_restore | 522 µs | 562 µs | +7.6% ⚠️ straddles the gate (see below) |
//! | vec/push_pop_untracked | 102 µs | 90.6 µs | **verus 11% faster** ✅ (but see push-only residue) |
//! | list/append_iter | 304 µs | 242 µs | **verus 20% faster** ✅ |
//! | list/splice | 38.6 µs | 35.4 µs | **verus 8% faster** ✅ |
//! | map/intern | 1.31 ms | 1.31 ms | parity (+0.4%) ✅ |
//! | map/intern_string | 3.54 ms | 3.58 ms | parity (+1.2%) ✅ |
//! | map/intern_composite | 3.31 ms | 3.29 ms | parity (−0.6%) ✅ |
//! | sparse_set/churn | 469 µs | 384 µs | **verus 18% faster** ✅ |
//! | aov/log | 90.1 µs | 95.4 µs | +5.8% ✅ |
//!
//! The former SpMap hasher exception is CLOSED: SpMap's index now uses the same
//! hash ALGORITHM production does (`foldhash::fast::RandomState`, the type
//! hashbrown 0.17's `DefaultHashBuilder` wraps) via `std::HashMap<K, usize, S>`
//! — the container vstd already models generically over any `S: BuildHasher`.
//! One axiom (mirroring vstd's shipped `axiom_random_state_builds_valid_hashers`)
//! buys full production speed. Note it is the same algorithm, NOT the same
//! builder type and NOT the same hash values (each builder is randomly seeded
//! on both sides). See containers-verus/src/hasher_spec.rs.
//!
//! ## The ±10% gate is NOT yet established — two open rows
//!
//! 1. `vec/mark_set_restore` straddles the boundary run-to-run: +7.6% in the
//!    measurement above, +17.7% (515 → 607 µs) in an independent review run.
//!    Needs the automated perf gate to settle rather than a hand-read median.
//! 2. Untracked **push-only** retains a ~+40% residue (11-layout-parity.md,
//!    `ParallelStore` row). The combined `push_pop_untracked` row being
//!    verus-faster does NOT resolve it — pop is where verus wins it back.
//!
//! Also unmeasured: tracked `ListArena` (still deferred, wants the consumer's
//! merge workload). Numbers here are hand-read criterion medians from a single
//! machine; `map/intern` in particular moved 1.98 → 1.31 ms on the PRODUCTION
//! side between runs, so treat single-run ratios with suspicion. The enforced
//! numbers live in `perf_gate.rs`, which removes the positional confound and
//! gates each row against a recorded ceiling; prefer it over any ratio here.

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

// Typed ids for the ListArena pairs (same width both sides).
prod::define_id31! { pub struct PElem / StoredPElem, "e"; }
prod::define_id31! { pub struct PList / StoredPList, "l"; }
prod::define_id31! { pub struct PNode / StoredPNode, "n"; }
verus::define_id31! { pub struct VElem / StoredVElem, "e"; }
verus::define_id31! { pub struct VList / StoredVList, "l"; }
verus::define_id31! { pub struct VNode / StoredVNode, "n"; }

const VEC_N: usize = 100_000;
const VEC_TOUCHES: usize = 50_000;
const LISTS: usize = 2_000;
const PER_LIST: usize = 30;

// ---------------------------------------------------------------------------
// vec/mark_set_restore
// ---------------------------------------------------------------------------

fn bench_vec_mark_set_restore(c: &mut Criterion) {
    let mut g = c.benchmark_group("vec/mark_set_restore");

    g.bench_function("prod", |b| {
        b.iter_batched_ref(
            || {
                let mut v: prod::VecP<u64, u32, true> = prod::VecP::new();
                for i in 0..VEC_N {
                    v.push(i as u64);
                }
                v
            },
            |v| {
                let tok = v.mark(prod::ShrinkPolicy::Never);
                let mut x: u64 = 0x9E3779B97F4A7C15;
                for _ in 0..VEC_TOUCHES {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    let idx = (x % VEC_N as u64) as u32;
                    v.set(idx, x);
                }
                v.restore(tok);
                black_box(v.len());
            },
            BatchSize::LargeInput,
        )
    });

    g.bench_function("verus", |b| {
        type V = verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, true>;
        b.iter_batched_ref(
            || {
                let mut v: V = V::new();
                for i in 0..VEC_N {
                    v.try_push(i as u64).expect("push: within index word");
                }
                v
            },
            |v| {
                let tok = v
                    .try_mark(verus::vec::ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness");
                let mut x: u64 = 0x9E3779B97F4A7C15;
                for _ in 0..VEC_TOUCHES {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    let idx = (x % VEC_N as u64) as u32;
                    v.set(idx, x);
                }
                v.try_restore(tok).expect("restore: own token");
                black_box(v.len());
            },
            BatchSize::LargeInput,
        )
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// vec/push_pop_untracked
// ---------------------------------------------------------------------------

fn bench_vec_push_pop_untracked(c: &mut Criterion) {
    let mut g = c.benchmark_group("vec/push_pop_untracked");

    g.bench_function("prod", |b| {
        b.iter(|| {
            let mut v: prod::VecP<u64, u32, false> = prod::VecP::new();
            for i in 0..VEC_N {
                v.push(i as u64);
            }
            let mut acc = 0u64;
            while let Some(x) = v.pop() {
                acc = acc.wrapping_add(x);
            }
            black_box(acc)
        })
    });

    g.bench_function("verus", |b| {
        type V = verus::vec::Vec<u64, u32, verus::parallel_store::ParallelStore<u64, u32>, false>;
        b.iter(|| {
            let mut v: V = V::new();
            for i in 0..VEC_N {
                v.try_push(i as u64).expect("push: within index word");
            }
            let mut acc = 0u64;
            while let Some(x) = v.pop() {
                acc = acc.wrapping_add(x);
            }
            black_box(acc)
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// list/append_iter
// ---------------------------------------------------------------------------

fn bench_list_append_iter(c: &mut Criterion) {
    let mut g = c.benchmark_group("list/append_iter");

    g.bench_function("prod", |b| {
        b.iter(|| {
            let mut a: prod::ListArena<PElem, PList, PNode, false> = prod::ListArena::new();
            let mut lists = Vec::with_capacity(LISTS);
            for _ in 0..LISTS {
                lists.push(a.new_list());
            }
            for (k, &l) in lists.iter().enumerate() {
                for j in 0..PER_LIST {
                    a.append(l, PElem::new((k * PER_LIST + j) as u32 & 0x7FFF_FFFF));
                }
            }
            let mut acc = 0u64;
            for &l in &lists {
                for e in a.iter(l) {
                    acc = acc.wrapping_add(e.raw() as u64);
                }
            }
            black_box(acc)
        })
    });

    g.bench_function("verus", |b| {
        b.iter(|| {
            let mut a: verus::ListArena<VElem, VList, VNode, false> = verus::ListArena::new();
            let mut lists = Vec::with_capacity(LISTS);
            for _ in 0..LISTS {
                lists.push(a.try_new_list().expect("within id space"));
            }
            for (k, &l) in lists.iter().enumerate() {
                for j in 0..PER_LIST {
                    a.try_append(l, VElem::new((k * PER_LIST + j) as u32 & 0x7FFF_FFFF))
                        .expect("within id space");
                }
            }
            let mut acc = 0u64;
            for &l in &lists {
                for e in a.iter(l) {
                    acc = acc.wrapping_add(e.raw() as u64);
                }
            }
            black_box(acc)
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// list/splice
// ---------------------------------------------------------------------------

fn bench_list_splice(c: &mut Criterion) {
    let mut g = c.benchmark_group("list/splice");

    g.bench_function("prod", |b| {
        b.iter(|| {
            let mut a: prod::ListArena<PElem, PList, PNode, false> = prod::ListArena::new();
            let mut lists = Vec::with_capacity(LISTS);
            for k in 0..LISTS {
                let l = a.new_list();
                for j in 0..4 {
                    a.append(l, PElem::new((k * 4 + j) as u32 & 0x7FFF_FFFF));
                }
                lists.push(l);
            }
            // Tournament merge into lists[0].
            let dst = lists[0];
            for &src in &lists[1..] {
                a.splice(dst, src);
            }
            black_box(a.len(dst))
        })
    });

    g.bench_function("verus", |b| {
        b.iter(|| {
            let mut a: verus::ListArena<VElem, VList, VNode, false> = verus::ListArena::new();
            let mut lists = Vec::with_capacity(LISTS);
            for k in 0..LISTS {
                let l = a.try_new_list().expect("within id space");
                for j in 0..4 {
                    a.try_append(l, VElem::new((k * 4 + j) as u32 & 0x7FFF_FFFF))
                        .expect("within id space");
                }
                lists.push(l);
            }
            let dst = lists[0];
            for &src in &lists[1..] {
                a.splice(dst, src);
            }
            black_box(a.len(dst))
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// map/intern: SpMap as the interner it is in the e-graph (LitValStore
// pattern) — insert-or-hit with a mark/restore cycle. u64 keys (primitive
// key model on both sides).
// ---------------------------------------------------------------------------

fn bench_map_intern(c: &mut Criterion) {
    let mut g = c.benchmark_group("map/intern");
    const N: usize = 50_000;

    g.bench_function("prod", |b| {
        b.iter(|| {
            let mut m: prod::Map<u64, (), usize, true> = prod::Map::new();
            let mut x: u64 = 0x243F_6A88_85A3_08D3;
            let tok = {
                for _ in 0..N / 2 {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    // 50% duplicate rate: intern hits and misses both measured
                    let key = x % (N as u64 / 2);
                    if m.id_of(&key).is_none() {
                        m.insert(key, ());
                    }
                }
                m.mark(prod::ShrinkPolicy::Never)
            };
            for _ in 0..N / 2 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let key = x % (N as u64);
                if m.id_of(&key).is_none() {
                    m.insert(key, ());
                }
            }
            m.restore(tok);
            black_box(m.len())
        })
    });

    g.bench_function("verus", |b| {
        b.iter(|| {
            let mut m: verus::SpMap<u64, (), usize, true> = verus::SpMap::new();
            let mut x: u64 = 0x243F_6A88_85A3_08D3;
            let tok = {
                for _ in 0..N / 2 {
                    x ^= x << 13;
                    x ^= x >> 7;
                    x ^= x << 17;
                    let key = x % (N as u64 / 2);
                    if m.id_of(&key).is_none() {
                        m.try_insert(key, ()).expect("insert: within index word");
                    }
                }
                m.try_mark(verus::ShrinkPolicy::Never)
                    .expect("mark: depth bounded by this harness")
            };
            for _ in 0..N / 2 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let key = x % (N as u64);
                if m.id_of(&key).is_none() {
                    m.try_insert(key, ()).expect("insert: within index word");
                }
            }
            m.try_restore(tok).expect("restore: own token");
            black_box(m.len())
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// sparse_set/churn: add/remove churn under a mark, then restore — the
// e-class registry pattern (stable ids, recycled slots).
// ---------------------------------------------------------------------------

fn bench_sparse_set_churn(c: &mut Criterion) {
    let mut g = c.benchmark_group("sparse_set/churn");
    const N: usize = 20_000;

    g.bench_function("prod", |b| {
        b.iter(|| {
            let mut s: prod::SparseSet<u64, PElem, prod::ParallelStore<u64, PElem>, true> =
                prod::SparseSet::new();
            let mut ids = Vec::with_capacity(N);
            for i in 0..N {
                ids.push(s.add(i as u64));
            }
            let tok = s.mark(prod::ShrinkPolicy::Never);
            let mut x: u64 = 0xB5297A4D;
            for _ in 0..N / 2 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let k = (x % ids.len() as u64) as usize;
                let id = ids[k];
                if s.contains(id) {
                    s.remove(id);
                } else {
                    ids[k] = s.add(x);
                }
            }
            s.restore(tok);
            black_box(s.len().raw())
        })
    });

    g.bench_function("verus", |b| {
        b.iter(|| {
            let mut s: verus::SparseSet<u64, VElem, verus::ParallelStore<u64, VElem>, true> =
                verus::SparseSet::new();
            let mut ids = Vec::with_capacity(N);
            for i in 0..N {
                ids.push(s.try_add(i as u64).expect("add: within id space"));
            }
            let tok = s
                .try_mark(verus::ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness");
            let mut x: u64 = 0xB5297A4D;
            for _ in 0..N / 2 {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                let k = (x % ids.len() as u64) as usize;
                let id = ids[k];
                if s.contains(id) {
                    s.remove(id);
                } else {
                    ids[k] = s.try_add(x).expect("add: within id space");
                }
            }
            s.restore(tok);
            black_box(s.len().raw())
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// aov/log: AppendOnlyVec as the append log it is (node store pattern) —
// bulk push, slice scan, mark/restore.
// ---------------------------------------------------------------------------

fn bench_aov_log(c: &mut Criterion) {
    let mut g = c.benchmark_group("aov/log");
    const N: usize = 100_000;

    g.bench_function("prod", |b| {
        b.iter(|| {
            let mut v: prod::AppendOnlyVec<u64, usize, true> = prod::AppendOnlyVec::new();
            for i in 0..N / 2 {
                v.push(i as u64);
            }
            let tok = v.mark(prod::ShrinkPolicy::Never);
            for i in 0..N / 2 {
                v.push(i as u64);
            }
            let mut acc = 0u64;
            for x in v.as_slice() {
                acc = acc.wrapping_add(*x);
            }
            v.restore(tok);
            black_box((acc, v.len()))
        })
    });

    g.bench_function("verus", |b| {
        b.iter(|| {
            let mut v: verus::AppendOnlyVec<u64, usize, true> = verus::AppendOnlyVec::new();
            for i in 0..N / 2 {
                v.try_push(i as u64).expect("push: within index word");
            }
            let tok = v
                .try_mark(verus::ShrinkPolicy::Never)
                .expect("mark: depth bounded by this harness");
            for i in 0..N / 2 {
                v.try_push(i as u64).expect("push: within index word");
            }
            let mut acc = 0u64;
            for x in v.as_slice() {
                acc = acc.wrapping_add(*x);
            }
            v.try_restore(tok).expect("restore: own token");
            black_box((acc, v.len()))
        })
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// map/intern_string + map/intern_composite: the CONSUMER key shapes (the
// e-graph's registries key by String; AU maps key by tuples of ids). SipHash's
// per-byte cost is where the std-vs-hashbrown gap widens beyond the u64
// numbers — measured, not assumed (review: "bounded" requires these).
// ---------------------------------------------------------------------------

fn bench_map_intern_string(c: &mut Criterion) {
    let mut g = c.benchmark_group("map/intern_string");
    const N: usize = 20_000;

    fn keys() -> Vec<String> {
        (0..N)
            .map(|i| format!("op::namespace_{}::symbol_{:08}", i % 37, i))
            .collect()
    }

    g.bench_function("prod", |b| {
        let ks = keys();
        b.iter(|| {
            let mut m: prod::Map<String, u32, usize, true> = prod::Map::new();
            for (i, k) in ks.iter().enumerate() {
                if m.id_of(k).is_none() {
                    m.insert(k.clone(), i as u32);
                }
            }
            let mut hits = 0usize;
            for k in &ks {
                if m.id_of(k).is_some() {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });

    g.bench_function("verus", |b| {
        let ks = keys();
        b.iter(|| {
            let mut m: verus::SpMap<String, u32, usize, true> = verus::SpMap::new();
            for (i, k) in ks.iter().enumerate() {
                if m.id_of(k).is_none() {
                    m.try_insert(k.clone(), i as u32)
                        .expect("insert: within index word");
                }
            }
            let mut hits = 0usize;
            for k in &ks {
                if m.id_of(k).is_some() {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });

    g.finish();
}

fn bench_map_intern_composite(c: &mut Criterion) {
    let mut g = c.benchmark_group("map/intern_composite");
    const N: usize = 20_000;
    // (u32, Vec<u32>) — the AU by_structure / space-index key shape.
    fn keys() -> Vec<(u32, Vec<u32>)> {
        (0..N as u32)
            .map(|i| {
                (
                    i % 97,
                    vec![i, i.wrapping_mul(7), i.wrapping_mul(31), i % 13],
                )
            })
            .collect()
    }

    g.bench_function("prod", |b| {
        let ks = keys();
        b.iter(|| {
            let mut m: prod::Map<(u32, Vec<u32>), u32, usize, true> = prod::Map::new();
            for (i, k) in ks.iter().enumerate() {
                if m.id_of(k).is_none() {
                    m.insert(k.clone(), i as u32);
                }
            }
            let mut hits = 0usize;
            for k in &ks {
                if m.id_of(k).is_some() {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });

    g.bench_function("verus", |b| {
        let ks = keys();
        b.iter(|| {
            let mut m: verus::SpMap<(u32, Vec<u32>), u32, usize, true> = verus::SpMap::new();
            for (i, k) in ks.iter().enumerate() {
                if m.id_of(k).is_none() {
                    m.try_insert(k.clone(), i as u32)
                        .expect("insert: within index word");
                }
            }
            let mut hits = 0usize;
            for k in &ks {
                if m.id_of(k).is_some() {
                    hits += 1;
                }
            }
            black_box(hits)
        })
    });

    g.finish();
}
criterion_group!(
    benches,
    bench_vec_mark_set_restore,
    bench_vec_push_pop_untracked,
    bench_list_append_iter,
    bench_list_splice,
    bench_map_intern,
    bench_map_intern_string,
    bench_map_intern_composite,
    bench_sparse_set_churn,
    bench_aov_log,
);
criterion_main!(benches);
