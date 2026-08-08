// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Confound-free prod-vs-verus B+tree comparison, one call site per workload.
//!
//! `examples/bulkload.rs` reads the three B+tree workloads at 1.1x (ascending
//! insert) and 1.2-1.3x (shuffled insert). Those numbers are *not* trustworthy on
//! their own: that harness builds prod then verus in a fixed order inside one
//! iteration, which is precisely the shape `doc/design/11-layout-parity.md`
//! documents as worth +18% to whichever arm runs second (glibc heap reuse) plus
//! another +18% from hot-loop cache-line alignment. A 10-30% "gap" is exactly the
//! size those artifacts produce, so bulkload cannot distinguish a real
//! implementation difference from its own measurement order at that magnitude.
//!
//! This probe removes both confounds the same way `examples/onesite.rs` does:
//!
//! 1. **One call site.** The implementation is selected at *runtime* inside a
//!    single `#[inline(never)]` function, so both arms are reached through one
//!    identical call at one code offset. Neither arm can win by landing on a
//!    friendlier alignment.
//! 2. **Both orders.** Each arm is timed first *and* last, and the best time is
//!    taken. A heap-reuse advantage that depends on running second cancels.
//! 3. **Warmed, best-of.** 20 warmup builds then best-of-5, which discards the
//!    page-fault-heavy first touches rather than averaging them in.
//!
//! Any residual difference is the implementation and nothing else. Target: within
//! 1% on every row, or verus faster.
//!
//! Run: `cargo run --release --example onesite_bplus -p containers-conformance`.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;

prod::define_id31! { pub struct PId / StoredPId, "p"; }
verus::define_id31! { pub struct VId / StoredVId, "v"; }

type ProdTree =
    prod::bplus::BPlusTreeSet<PId, prod::bplus::Layout256, prod::bplus::BinarySearch, false>;
type VerusTree =
    verus::bplus::BPlusTreeSet<VId, verus::bplus::Layout256, verus::bplus::BinarySearch, false>;

const N: usize = 100_000;

// Small-tree variant: at n=2000 the whole arena (~35 nodes x 256B ~ 9KB) fits in
// L1, so cache misses cannot contribute. If the gap survives at this size it is
// pure instruction cost per level; if it collapses, it is memory-hierarchy.
const SMALL: usize = 2_000;

/// The three workloads, selected at runtime so all six (workload, impl) pairs
/// share one call site. `keys`/`vkeys` are pre-built so key construction is not
/// timed; the shuffled slices are the same permutation for both impls.
#[inline(never)]
fn run(workload: usize, which: usize, pk: &[PId], vk: &[VId]) -> usize {
    match (workload, which) {
        // from_sorted: the bulk path.
        (0, 0) => ProdTree::from_sorted(pk).len(),
        (0, _) => VerusTree::from_sorted(vk).len(),
        // Duplicate re-insert: build the tree once (untimed by being identical
        // on both arms and dwarfed by the 100k re-inserts), then re-insert every
        // key in shuffled order. Each one takes the full root-to-leaf descent,
        // finds the key present, and returns `false` WITHOUT mutating: no shift,
        // no split, no arena write. This row prices the descent alone, so
        // subtracting it from `insert shuffled` isolates the mutation path.
        (2, 0) => {
            let mut t = ProdTree::new();
            for &k in pk {
                t.insert(k);
            }
            let mut c = 0;
            for &k in pk {
                c += t.insert(k) as usize;
            }
            c
        }
        (2, _) => {
            let mut t = VerusTree::new();
            for &k in vk {
                t.insert(k);
            }
            let mut c = 0;
            for &k in vk {
                c += t.insert(k) as usize;
            }
            c
        }
        // Pure descent, ITERATIVE on both arms: prod's `cursor().seek` and
        // verus's `contains` are the same walk (`find_gt` per internal level,
        // `find_ge` at the leaf, no mutation), and neither recurses. Compared
        // against `redescent (dup)` — the same walk, but reached through verus's
        // *recursive* `insert_rec` — this separates the cost of the descent's
        // per-level work from the cost of its control structure.
        (3, 0) => {
            let mut t = ProdTree::new();
            for &k in pk {
                t.insert(k);
            }
            let mut c = 0;
            for &k in pk {
                let mut cur = t.cursor();
                cur.seek(k);
                c += cur.key().is_some() as usize;
            }
            c
        }
        (3, _) => {
            let mut t = VerusTree::new();
            for &k in vk {
                t.insert(k);
            }
            let mut c = 0;
            for &k in vk {
                c += t.contains(k) as usize;
            }
            c
        }
        // insert loop: ascending when the caller passes sorted keys, shuffled
        // when it passes the permutation. One arm serves both.
        (_, 0) => {
            let mut t = ProdTree::new();
            for &k in pk {
                t.insert(k);
            }
            t.len()
        }
        (_, _) => {
            let mut t = VerusTree::new();
            for &k in vk {
                t.insert(k);
            }
            t.len()
        }
    }
}

fn time(workload: usize, which: usize, pk: &[PId], vk: &[VId]) -> f64 {
    for _ in 0..20 {
        black_box(run(workload, which, pk, vk));
    }
    let mut best = f64::MAX;
    for _ in 0..5 {
        let t = std::time::Instant::now();
        black_box(run(workload, which, pk, vk));
        best = best.min(t.elapsed().as_nanos() as f64 / 1000.0);
    }
    best
}

/// Time both arms in both orders and report the best of each, so a
/// position-dependent effect cannot masquerade as an implementation difference.
fn compare(label: &str, workload: usize, pk: &[PId], vk: &[VId]) {
    let p1 = time(workload, 0, pk, vk);
    let v1 = time(workload, 1, pk, vk);
    let v2 = time(workload, 1, pk, vk);
    let p2 = time(workload, 0, pk, vk);
    let p = p1.min(p2);
    let v = v1.min(v2);
    println!(
        "{label:<16} prod {p:>9.1}µs   verus {v:>9.1}µs   {:>+7.1}%   \
         (p first={p1:.1} last={p2:.1} | v first={v1:.1} last={v2:.1})",
        (v / p - 1.0) * 100.0
    );
}

fn main() {
    let pk: Vec<PId> = (0..N as u32).map(PId::new).collect();
    let vk: Vec<VId> = (0..N as u32).map(VId::new).collect();

    // Shuffled order defeats both impls' `last_leaf` append fast path, so every
    // key pays a full root-to-leaf descent: this row prices the descent itself.
    let mut sh: Vec<u32> = (0..N as u32).collect();
    let mut st = 0x2545_F491_4F6C_DD1Du64;
    for i in (1..sh.len()).rev() {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        let j = (st >> 33) as usize % (i + 1);
        sh.swap(i, j);
    }
    let pks: Vec<PId> = sh.iter().copied().map(PId::new).collect();
    let vks: Vec<VId> = sh.iter().copied().map(VId::new).collect();

    println!("Layout256, n={N}, best-of-5 after 20 warmups, both orders\n");
    compare("from_sorted", 0, &pk, &vk);
    compare("insert asc", 1, &pk, &vk);
    compare("insert shuffled", 1, &pks, &vks);
    compare("redescent (dup)", 2, &pks, &vks);
    compare("descent (iter)", 3, &pks, &vks);

    // Same rows on an L1-resident tree, to split instruction cost from misses.
    let mut sh2: Vec<u32> = (0..SMALL as u32).collect();
    let mut st2 = 0x9E37_79B9_7F4A_7C15u64;
    for i in (1..sh2.len()).rev() {
        st2 ^= st2 << 13;
        st2 ^= st2 >> 7;
        st2 ^= st2 << 17;
        let j = (st2 >> 33) as usize % (i + 1);
        sh2.swap(i, j);
    }
    let pks2: Vec<PId> = sh2.iter().copied().map(PId::new).collect();
    let vks2: Vec<VId> = sh2.iter().copied().map(VId::new).collect();
    println!();
    compare("sm insert shuf", 1, &pks2, &vks2);
    compare("sm descent", 3, &pks2, &vks2);
}
