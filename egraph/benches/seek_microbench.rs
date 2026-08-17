// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Isolates the single `seek()` cost difference between `SortedVecCursor`
//! and `BPlusCursor` on the workload shape that leapfrog actually produces:
//! many small-skip forward seeks into a large sorted set.
//!
//! Two B+tree build paths are benchmarked:
//!
//! - `bplus_bulk`: built via `from_sorted`, so arena order matches
//!   traversal order — best-case cache locality.
//! - `bplus_incremental`: built via randomly-ordered `insert` calls,
//!   producing an arena where leaves and internal nodes are interleaved
//!   in allocation order. This models the real e-matching index which
//!   grows one node at a time as new e-nodes are canonicalized.
//!
//! Setup: one sorted set of N keys. Drive a cursor through N seeks that
//! each advance by exactly 1 position. At this small-skip pattern,
//! binary search pays log N per seek while the B+tree fast path stays
//! inside the current leaf.
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use semi_persistent_containers::{
    SortedCursor,
    bplus::{BPlusTreeSet, BinarySearch, Layout256},
};
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::index::SortedVecCursor;

type Tree = BPlusTreeSet<ENodeId, Layout256, BinarySearch, false>;

/// Fisher-Yates shuffle seeded deterministically so benchmark runs are stable.
fn shuffled(mut v: Vec<u32>, seed: u64) -> Vec<u32> {
    let mut s = seed;
    for i in (1..v.len()).rev() {
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let j = (s >> 33) as usize % (i + 1);
        v.swap(i, j);
    }
    v
}

fn seek_microbench(c: &mut Criterion) {
    let mut group = c.benchmark_group("seek_microbench");
    group.sample_size(20);

    for &n in &[1_000usize, 100_000, 1_000_000] {
        // Keys: 0, 10, 20, ... (step 10 so seek targets can fall between).
        let data: Vec<u32> = (0..n as u32).map(|i| i * 10).collect();

        let svec: Vec<ENodeId> = data.iter().map(|&x| ENodeId::new(x)).collect();

        // Bulk-built tree: arena in traversal order.
        let data_ids: Vec<ENodeId> = data.iter().map(|&x| ENodeId::new(x)).collect();
        let tree_bulk = Tree::from_sorted(&data_ids);

        // Incrementally-built tree: same final contents, but inserted in
        // random order. Each `insert` allocates new leaves and splits
        // internal nodes on demand, so the arena ends up with leaves and
        // internals interleaved. Descending from root will chase pointers
        // to arbitrary arena slots — every node load is a cold cache line.
        let mut tree_inc = Tree::new();
        for &k in &shuffled(data.clone(), 0xA5A5_DEADBEEF) {
            tree_inc.insert(ENodeId::new(k));
        }
        // Sanity: same contents, same cursor behavior.
        assert_eq!(tree_bulk.len(), tree_inc.len());

        let targets: Vec<u32> = (0..n as u32).map(|i| i * 10).collect();

        group.bench_with_input(BenchmarkId::new("sortedvec", n), &(), |b, _| {
            b.iter(|| {
                let mut cur = SortedVecCursor::new(&svec);
                for &t in &targets {
                    <_ as SortedCursor>::seek(&mut cur, ENodeId::new(t));
                }
                std::hint::black_box(cur.key());
            });
        });

        group.bench_with_input(BenchmarkId::new("bplus_bulk", n), &(), |b, _| {
            b.iter(|| {
                let mut cur = tree_bulk.cursor();
                cur.seek_first();
                for &t in &targets {
                    <_ as SortedCursor>::seek(&mut cur, ENodeId::new(t));
                }
                std::hint::black_box(cur.key());
            });
        });

        group.bench_with_input(BenchmarkId::new("bplus_incremental", n), &(), |b, _| {
            b.iter(|| {
                let mut cur = tree_inc.cursor();
                cur.seek_first();
                for &t in &targets {
                    <_ as SortedCursor>::seek(&mut cur, ENodeId::new(t));
                }
                std::hint::black_box(cur.key());
            });
        });
    }

    group.finish();
}

/// Stride sweep for `SortedVecCursor::seek` alone.
///
/// `seek_microbench` above drives every seek one position forward, which is the
/// pattern leapfrog produces and the pattern galloping search is *for*. That
/// makes it the wrong bench to detect the gallop's downside: the acceptance
/// condition for E7 was that short strides improve **without long jumps
/// regressing past the random baseline**, and only a sweep can show that.
///
/// Three shapes over one 1M-key set:
///
/// - `stride/<k>` — every seek advances exactly `k` positions. `k = 1` is the
///   leapfrog case; growing `k` walks toward the gallop's break-even point.
/// - `random` — targets drawn uniformly, so the cursor jumps an average of
///   n/2 and resets. This is the reference: a search that cannot beat binary
///   search here has to at least match it.
/// - `adversarial` — alternates a 1-position step with a jump to near the end,
///   the shape that makes the gallop climb its full ladder and then bisect. If
///   galloping has a worst case, it is this one.
fn seek_stride_sweep(c: &mut Criterion) {
    let mut group = c.benchmark_group("seek_stride");
    group.sample_size(20);

    const N: usize = 1_000_000;
    let svec: Vec<ENodeId> = (0..N as u32).map(|i| ENodeId::new(i * 10)).collect();

    // Same seek count for every shape below, so the rows are comparable as
    // per-seek costs rather than as totals.
    const SEEKS: usize = 4096;

    for &stride in &[1usize, 4, 16, 64, 256, 1024] {
        let targets: Vec<ENodeId> = (0..SEEKS)
            .map(|i| ENodeId::new(((i * stride) % N) as u32 * 10))
            .collect();
        group.bench_with_input(BenchmarkId::new("stride", stride), &(), |b, _| {
            b.iter(|| {
                let mut cur = SortedVecCursor::new(&svec);
                for &t in &targets {
                    <_ as SortedCursor>::seek(&mut cur, t);
                }
                std::hint::black_box(cur.is_valid());
            });
        });
    }

    // Uniform random targets, sorted so the cursor still only moves forward —
    // an unsorted sequence would seek backwards, which leapfrog never does and
    // which `seek` does not support.
    let mut rnd: Vec<u32> = shuffled((0..N as u32).collect(), 0x5EED_1234)
        .into_iter()
        .take(SEEKS)
        .collect();
    rnd.sort_unstable();
    let rnd_targets: Vec<ENodeId> = rnd.iter().map(|&x| ENodeId::new(x * 10)).collect();
    group.bench_function("random", |b| {
        b.iter(|| {
            let mut cur = SortedVecCursor::new(&svec);
            for &t in &rnd_targets {
                <_ as SortedCursor>::seek(&mut cur, t);
            }
            std::hint::black_box(cur.is_valid());
        });
    });

    // One short step, then a long jump, repeatedly: the gallop pays its full
    // ladder on every other seek.
    let adv: Vec<ENodeId> = (0..SEEKS)
        .map(|i| {
            let half = i / 2;
            let pos = if i % 2 == 0 {
                half * (N / (SEEKS / 2 + 1))
            } else {
                half * (N / (SEEKS / 2 + 1)) + 1
            };
            ENodeId::new((pos.min(N - 1)) as u32 * 10)
        })
        .collect();
    group.bench_function("adversarial", |b| {
        b.iter(|| {
            let mut cur = SortedVecCursor::new(&svec);
            for &t in &adv {
                <_ as SortedCursor>::seek(&mut cur, t);
            }
            std::hint::black_box(cur.is_valid());
        });
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Seek strategy sweep: galloping, bisection, stride-hinted galloping
// ---------------------------------------------------------------------------

/// The three candidate seeks, written against a raw slice so the sweep prices
/// the search arithmetic and nothing else.
///
/// `gallop` is `SortedVecCursor::seek` transcribed: the early check, the
/// doubling ladder, the clamp, the bisection of the window doubling produced.
/// `binary` is what it replaced (E7), a `partition_point` over the remaining
/// run. `hinted` is `gallop` with the ladder's first offset set to a caller-
/// supplied expected stride instead of 1. That is correct for any hint at or
/// above 1, because the bisection's precondition is only that `data[lo]` is
/// below the target, which the early check establishes before the ladder runs.
mod strategy {
    use semi_persistent_egraph::id::ENodeId;

    #[inline]
    pub fn gallop(data: &[ENodeId], pos: &mut usize, target: ENodeId) {
        hinted(data, pos, target, 1)
    }

    #[inline]
    pub fn binary(data: &[ENodeId], pos: &mut usize, target: ENodeId) {
        let n = data.len();
        if *pos >= n || data[*pos] >= target {
            return;
        }
        *pos += data[*pos..].partition_point(|x| *x < target);
    }

    #[inline]
    pub fn hinted(data: &[ENodeId], pos: &mut usize, target: ENodeId, hint: usize) {
        let n = data.len();
        if *pos >= n || data[*pos] >= target {
            return;
        }
        let mut lo = *pos;
        let mut step = hint.max(1);
        while step < n - lo && data[lo + step] < target {
            lo += step;
            step *= 2;
        }
        let hi = if step < n - lo { lo + step } else { n };
        *pos = lo + 1 + data[lo + 1..hi].partition_point(|x| *x < target);
    }
}

/// Run lengths and advance distances the sweep crosses.
///
/// Both axes are read off the instrumented saturation runs
/// (`leapfrog::seek_stats`, `EGRAPH_SEEK=1`): on the programs under
/// `comparison/` the remaining run in front of a seek spans `2^0` to `2^16`
/// with mass at both ends, and the advance distance is bimodal: 30% to 95% of
/// seeks move by at most one element, and the rest spread almost flat out to
/// `2^12`. A crossover table has to cover both axes because the two strategies'
/// costs depend on different ones: galloping pays in *d*, bisection pays in
/// *rem*.
const SPANS: &[usize] = &[64, 1_024, 16_384, 262_144];
const STRIDES: &[usize] = &[1, 4, 16, 64, 256, 1_024];

/// Seeks confined to one bucket-sized span at a time, cycling spans across an
/// arena far larger than cache.
///
/// This is the layout the index actually has since R2: every bucket is a
/// contiguous `(offset, length)` window into one shared pool, so a seek's
/// working set is the span, and consecutive joins touch spans scattered through
/// a pool much larger than L2. Benchmarking on a single hot 1M-element array
/// instead would hand galloping a cache advantage it does not have in the
/// engine, which is the constant this whole comparison turns on.
///
/// `hinted/exact` is an oracle whose hint *is* the distance, so it bounds what
/// any stride estimator can pay for. `hinted/over` and `hinted/under` are the
/// same estimator wrong by 8x in each direction, which is the cost a real `n/m`
/// estimate has to be weighed against.
fn seek_strategy_sweep(c: &mut Criterion) {
    let mut group = c.benchmark_group("seek_strategy");
    group.sample_size(20);

    // 32 MB of ids: past this machine's last-level cache, so span selection is a
    // cold start the way a fresh join's first probe is.
    const ARENA: usize = 8 << 20;
    const SEEKS: usize = 4096;
    let arena: Vec<ENodeId> = (0..ARENA as u32).map(|i| ENodeId::new(i * 10)).collect();

    for &span in SPANS {
        let spans = ARENA / span;
        for &d in STRIDES {
            if d * 2 > span {
                continue;
            }
            // (span index, target) for every seek, precomputed so the timed loop
            // holds nothing but the seek. The cursor restarts at the head of the
            // next span whenever the current one runs out.
            let mut plan: Vec<(usize, ENodeId)> = Vec::with_capacity(SEEKS);
            let (mut si, mut p) = (0usize, 0usize);
            for _ in 0..SEEKS {
                if p + d >= span {
                    si = (si + 1) % spans;
                    p = 0;
                }
                p += d;
                plan.push((si, arena[si * span + p]));
            }

            macro_rules! case {
                ($name:literal, $seek:expr) => {
                    group.bench_with_input(
                        BenchmarkId::new($name, format!("{span}/{d}")),
                        &(),
                        |b, _| {
                            b.iter(|| {
                                let (mut cur, mut pos) = (usize::MAX, 0usize);
                                for &(si, t) in &plan {
                                    if si != cur {
                                        cur = si;
                                        pos = 0;
                                    }
                                    let run = &arena[si * span..(si + 1) * span];
                                    #[allow(clippy::redundant_closure_call)]
                                    ($seek)(run, &mut pos, t);
                                }
                                std::hint::black_box(pos)
                            });
                        },
                    );
                };
            }

            case!("gallop", strategy::gallop);
            case!("binary", strategy::binary);
            case!("hinted/exact", |r: &[ENodeId], p: &mut usize, t| {
                strategy::hinted(r, p, t, d)
            });
            case!("hinted/over", |r: &[ENodeId], p: &mut usize, t| {
                strategy::hinted(r, p, t, d * 8)
            });
            case!("hinted/under", |r: &[ENodeId], p: &mut usize, t| {
                strategy::hinted(r, p, t, d / 8)
            });
        }
    }

    group.finish();
}

criterion_group!(
    benches,
    seek_microbench,
    seek_stride_sweep,
    seek_strategy_sweep
);
criterion_main!(benches);
