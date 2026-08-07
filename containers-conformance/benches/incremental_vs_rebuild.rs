// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Incremental index maintenance vs per-round bulk rebuild — the e-graph
//! saturation scenario.
//!
//! Setup: TOTAL unique random ids, revealed in N equal random chunks (one
//! chunk per saturation round). After every round the index must cover all
//! ids seen so far. Two strategies:
//!
//!   - REBUILD (the egraph today): every round, reconstruct the index from
//!     scratch over the accumulated k·(TOTAL/N) ids. Round k touches k
//!     chunks, so N rounds touch TOTAL·(N+1)/2 elements — Θ(N·TOTAL) total
//!     work that grows with the round count.
//!   - INCREMENTAL (the planned B+tree): every round, insert ONLY the new
//!     chunk into a persistent tree. Each id is inserted exactly once —
//!     Θ(TOTAL·log TOTAL) total work, independent of N.
//!
//! Rebuild variants measured:
//!   - `rebuild/sortedvec`: collect + sort the accumulated set (what the
//!     egraph's ephemeral SortedVec indexes do today).
//!   - `rebuild/prod_bplus_from_sorted`: sort + production's O(n) bottom-up
//!     `from_sorted` (a hypothetical B+tree-rebuild strategy; sort dominates).
//!
//! Incremental variants:
//!   - `incremental/verus_bplus_insert`: the verus tree (current fat-node
//!     layout), per-chunk inserts.
//!   - `incremental/prod_bplus_insert`: the production tree, same strategy
//!     (isolates the verus per-op overhead from the strategy win).
//!
//! Every timing is the CUMULATIVE cost of all N rounds. TRACK=false on both
//! trees (isolates maintenance cost; semi-persistence is a further advantage
//! of the incremental tree not measured here — a rebuild strategy pays a
//! full rebuild after every restore, the persistent tree pays O(k) diffs).

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;

verus::define_id31! {
    pub struct VKey / StoredVKey, "v";
}
prod::define_id31! {
    pub struct PKey / StoredPKey, "p";
}

// 20M ids over 10 rounds (2M new ids per round) — the at-scale scenario.
// Note 20M < 2^31 ids exist comfortably; the dedup HashSet peaks ~500MB
// during generation, freed before measurement.
const TOTAL: usize = 20_000_000;

/// Unique random 31-bit ids, in insertion (arrival) order. Fixed seed.
fn make_ids(n: usize) -> Vec<u32> {
    let mut set = std::collections::HashSet::with_capacity(n);
    let mut out = Vec::with_capacity(n);
    let mut x: u64 = 0x5EED_CAFE;
    while out.len() < n {
        x = x
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let v = ((x >> 33) as u32) & 0x7FFF_FFFF;
        if set.insert(v) {
            out.push(v);
        }
    }
    out
}

/// REBUILD/sortedvec: round k sorts the full accumulated prefix.
fn rebuild_sortedvec(chunks: &[&[u32]]) -> usize {
    let mut checksum = 0usize;
    let mut acc: Vec<u32> = Vec::new();
    for chunk in chunks {
        acc.extend_from_slice(chunk);
        // The rebuild: a fresh sorted index over everything seen so far.
        let mut index = acc.clone();
        index.sort_unstable();
        checksum = checksum.wrapping_add(index.len() + index[0] as usize);
    }
    checksum
}

/// REBUILD/prod_bplus_from_sorted: round k sorts + bottom-up-builds the tree.
fn rebuild_prod_bplus(chunks: &[&[u32]]) -> usize {
    let mut checksum = 0usize;
    let mut acc: Vec<u32> = Vec::new();
    for chunk in chunks {
        acc.extend_from_slice(chunk);
        let mut sorted = acc.clone();
        sorted.sort_unstable();
        let keys: Vec<PKey> = sorted.iter().map(|&v| PKey::new(v)).collect();
        let t: prod::BPlusTreeSet<PKey, prod::Layout256, prod::BinarySearch, false> =
            prod::BPlusTreeSet::from_sorted(&keys);
        checksum = checksum.wrapping_add(t.len());
    }
    checksum
}

/// INCREMENTAL/verus: one persistent tree; each round inserts its chunk only.
fn incremental_verus(chunks: &[&[u32]]) -> usize {
    // Largest u32 layout (cap 62 — production's 256B recommendation).
    let mut t: verus::BPlusTreeSet<VKey, verus::Layout256U32, verus::BinarySearch, false> =
        verus::BPlusTreeSet::new();
    for chunk in chunks {
        for &v in *chunk {
            t.insert(VKey::new(v));
        }
    }
    t.len()
}

/// INCREMENTAL/std: the same strategy on std::collections::BTreeSet — the
/// mature, cache-tuned reference for incremental sorted-set maintenance.
fn incremental_std(chunks: &[&[u32]]) -> usize {
    let mut t: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
    for chunk in chunks {
        for &v in *chunk {
            t.insert(v);
        }
    }
    t.len()
}

/// INCREMENTAL/prod: the same strategy on the production tree (reference).
fn incremental_prod(chunks: &[&[u32]]) -> usize {
    let mut t: prod::BPlusTreeSet<PKey, prod::Layout256, prod::BinarySearch, false> =
        prod::BPlusTreeSet::new();
    for chunk in chunks {
        for &v in *chunk {
            t.insert(PKey::new(v));
        }
    }
    t.len()
}

fn bench_all(c: &mut Criterion) {
    let ids = make_ids(TOTAL);
    // Ascending arrival: same unique ids, sorted — models the e-graph's
    // dense increasing id allocation (each round's new ids all exceed the
    // accumulated set's).
    let mut ids_asc = ids.clone();
    ids_asc.sort_unstable();

    {
        let rounds = 10usize;
        let chunk_len = TOTAL / rounds;
        let chunks: Vec<&[u32]> = (0..rounds)
            .map(|k| &ids[k * chunk_len..(k + 1) * chunk_len])
            .collect();

        let mut g = c.benchmark_group(format!("saturation_{TOTAL}ids_{rounds}rounds"));
        g.sample_size(10);
        g.measurement_time(std::time::Duration::from_secs(120));
        g.warm_up_time(std::time::Duration::from_secs(5));

        g.bench_with_input(BenchmarkId::new("rebuild", "sortedvec"), &(), |b, _| {
            b.iter(|| std::hint::black_box(rebuild_sortedvec(&chunks)));
        });
        g.bench_with_input(
            BenchmarkId::new("rebuild", "prod_bplus_from_sorted"),
            &(),
            |b, _| {
                b.iter(|| std::hint::black_box(rebuild_prod_bplus(&chunks)));
            },
        );
        g.bench_with_input(
            BenchmarkId::new("incremental", "verus_bplus_insert"),
            &(),
            |b, _| {
                b.iter(|| std::hint::black_box(incremental_verus(&chunks)));
            },
        );
        g.bench_with_input(
            BenchmarkId::new("incremental", "prod_bplus_insert"),
            &(),
            |b, _| {
                b.iter(|| std::hint::black_box(incremental_prod(&chunks)));
            },
        );
        g.bench_with_input(
            BenchmarkId::new("incremental", "std_btreeset"),
            &(),
            |b, _| {
                b.iter(|| std::hint::black_box(incremental_std(&chunks)));
            },
        );
        g.finish();

        // ---- ascending-arrival group (the e-graph id pattern) ----
        let chunks_asc: Vec<&[u32]> = (0..rounds)
            .map(|k| &ids_asc[k * chunk_len..(k + 1) * chunk_len])
            .collect();

        let mut g = c.benchmark_group(format!("saturation_asc_{TOTAL}ids_{rounds}rounds"));
        g.sample_size(10);
        g.measurement_time(std::time::Duration::from_secs(120));
        g.warm_up_time(std::time::Duration::from_secs(5));

        g.bench_with_input(BenchmarkId::new("rebuild", "sortedvec"), &(), |b, _| {
            b.iter(|| std::hint::black_box(rebuild_sortedvec(&chunks_asc)));
        });
        g.bench_with_input(
            BenchmarkId::new("incremental", "verus_bplus_insert"),
            &(),
            |b, _| {
                b.iter(|| std::hint::black_box(incremental_verus(&chunks_asc)));
            },
        );
        g.bench_with_input(
            BenchmarkId::new("incremental", "prod_bplus_insert"),
            &(),
            |b, _| {
                b.iter(|| std::hint::black_box(incremental_prod(&chunks_asc)));
            },
        );
        g.bench_with_input(
            BenchmarkId::new("incremental", "std_btreeset"),
            &(),
            |b, _| {
                b.iter(|| std::hint::black_box(incremental_std(&chunks_asc)));
            },
        );
        g.finish();
    }
}

criterion_group! {
    name = benches;
    config = Criterion::default();
    targets = bench_all
}
criterion_main!(benches);
