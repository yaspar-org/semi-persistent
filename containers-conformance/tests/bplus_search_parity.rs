// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Does the verified B+tree actually *binary search* inside a node?
//!
//! It is generic over `S: SearchKind` exactly as production is, and
//! `bplus_search` verifies both impls against production's contracts — and for a
//! while it called neither. Five hand-written linear scans stood in their place
//! (`grep -c 'S::'` over `containers-verus/src/bplus.rs`: 0, against six
//! production call sites), while two verified binary searches (`leaf_find_ge`,
//! `find_child`) sat in the same file, used only by `seek`. Cost: random-order
//! insertion ran 1.4-1.5x production's.
//!
//! Every other test in this crate is blind to it. The differential trace
//! (`differential.rs`) compares *results*, and a linear scan returns the same
//! index a bisection does. The proofs are indifferent by construction:
//! `leaf_find_ge`'s postcondition says where the boundary is, not how many probes
//! found it. `layout_parity.rs` measures sizes, which don't move.
//!
//! So the guard is a timing ratio against production, which bisects. Both trees
//! insert the same shuffled keys into the same layout in one binary; dividing
//! cancels machine speed and allocator state. It does not cancel heap position or
//! code layout (`containers-verus/doc/design/11-layout-parity.md`) — hence a
//! threshold with a wide margin rather than a tight one.
//!
//! **Calibrated, not guessed.** Measured on this machine, 6 trials each:
//!
//! | build | verus/prod insert ratio |
//! |---|---|
//! | binary search (correct) | 0.910 - 0.920 |
//! | `mid = lo` in both searches (linear) | 1.468 - 1.479 |
//!
//! Both bands are tight and 60% apart, and the sabotaged band reproduces the
//! original bug's 1.4-1.5x. The threshold is **1.20**, roughly midway in log
//! space. Note the correct build comes in *under* 1.0: the verified bisection is
//! slightly faster than production's `partition_point`, the same effect
//! [Chapter 12](../../containers-verus/doc/design/12-sorted-vec-cursor.md)
//! measured for the cursor.
//!
//! An earlier version of this test compared *widening* ratios (wide leaves vs
//! narrow, each side against itself) on the theory that a linear scan tracks
//! capacity while a bisection tracks its logarithm. It failed to catch the
//! sabotage — 0.97x healthy vs 1.25x fully sabotaged, under a 4x threshold. Two
//! reasons, both worth recording: `Layout256` is 256 *bytes*, so leaf capacity
//! only goes 14 → 62, not 14 → 256; and in-node search is a minority of insert
//! cost, so a ratio-of-ratios divides the signal away twice. Sabotage-test a
//! performance guard before trusting it.
use semi_persistent_containers as prod;
use semi_persistent_containers_verus as verus;
use std::hint::black_box;
use std::time::Instant;

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

/// Shuffle so production's `last_leaf` append fast path cannot fire. With
/// ascending keys production skips the descent entirely, and we would be
/// measuring that missing fast path (a separate, documented gap) instead of the
/// in-node search.
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

/// `min` over reps: the cleanest run, not the average of a shared machine.
fn bench(mut f: impl FnMut()) -> u128 {
    let mut best = u128::MAX;
    for _ in 0..7 {
        let t = Instant::now();
        f();
        best = best.min(t.elapsed().as_nanos());
    }
    best
}

/// Correct: 0.91. Linear scan: 1.47. Threshold 1.20.
const MAX_RATIO: f64 = 1.20;

#[test]
fn in_node_search_is_binary_not_linear() {
    // The calibration bands above are release-codegen properties. Unoptimized
    // or instrumented builds (plain `cargo test`, the coverage job's
    // `llvm-cov` debug profile) un-inline the search helpers — `sel_usize` /
    // `arr_get` are call boundaries there — and add per-probe counter work,
    // which moved the ratio to 1.435 under rustc 1.97 coverage with the
    // bisection demonstrably wired in. In those builds the two bands overlap
    // and the oracle reads noise, so the timing assertion is release-only.
    if cfg!(debug_assertions) {
        eprintln!("skipped: timing canary is calibrated for release codegen only");
        return;
    }
    let keys = shuffled(30_000);
    let pk: Vec<PId> = keys.iter().copied().map(PId::new).collect();
    let vk: Vec<VId> = keys.iter().copied().map(VId::new).collect();

    let p_ns = bench(|| {
        let mut t = ProdTree::new();
        for &k in &pk {
            t.insert(k);
        }
        black_box(t.len());
    });
    let v_ns = bench(|| {
        let mut t = VerusTree::new();
        for &k in &vk {
            t.insert(k);
        }
        black_box(t.len());
    });

    let ratio = v_ns as f64 / p_ns as f64;
    eprintln!(
        "shuffled insert, 30k keys, Layout256: prod {p_ns}ns, verus {v_ns}ns, \
         ratio {ratio:.3} (correct ~0.91, linear ~1.47, threshold {MAX_RATIO})"
    );

    assert!(
        ratio < MAX_RATIO,
        "verus insert is {ratio:.3}x production's (threshold {MAX_RATIO}); a \
         hand-written linear scan has most likely replaced a `leaf_find_ge` / \
         `find_child` call in containers-verus/src/bplus.rs. Check \
         `grep -c 'S::\\|leaf_find_ge\\|find_child' containers-verus/src/bplus.rs` \
         and see this file's header."
    );
}

/// The bug's own signature, as a direct check: both `SearchKind` impls must be
/// *reachable* through the tree's type parameter.
///
/// When the tree ignored `S`, `BinarySearch` and `Branchless` produced identical
/// behavior *and* identical timings — the parameter was decorative. Today the
/// descent's `leaf_find_ge` / `find_child` dispatch through `S::find_ge` /
/// `S::find_gt`, so the two instantiations run genuinely different search code
/// against the same verified contracts; this test pins that both agree with
/// production. The differential sweep below
/// (`branchless_differential_prod_vs_verus`) extends the check to cursor
/// traversal and seek.
#[test]
fn both_search_kinds_agree_with_production() {
    let keys = shuffled(4_000);
    let mut expected: Vec<u32> = keys.clone();
    expected.sort_unstable();

    let mut p = ProdTree::new();
    for &k in &keys {
        p.insert(PId::new(k));
    }

    let mut v_bin = VerusTree::new();
    let mut v_lin: verus::bplus::BPlusTreeSet<
        VId,
        verus::bplus_layout::Layout256,
        verus::bplus_search::Branchless,
        false,
    > = verus::bplus::BPlusTreeSet::new();
    for &k in &keys {
        v_bin.insert(VId::new(k));
        v_lin.insert(VId::new(k));
    }

    assert_eq!(
        p.len(),
        expected.len(),
        "production keeps every distinct key"
    );
    assert_eq!(v_bin.len(), expected.len(), "BinarySearch instantiation");
    assert_eq!(v_lin.len(), expected.len(), "Branchless instantiation");

    for &k in expected.iter().step_by(37) {
        assert!(v_bin.contains(VId::new(k)), "BinarySearch: {k} present");
        assert!(v_lin.contains(VId::new(k)), "Branchless: {k} present");
    }
    for k in (4_000u32..4_100).step_by(7) {
        assert!(!v_bin.contains(VId::new(k)), "BinarySearch: {k} absent");
        assert!(!v_lin.contains(VId::new(k)), "Branchless: {k} absent");
    }
}

type ProdTreeBr =
    prod::bplus::BPlusTreeSet<PId, prod::bplus::Layout256, prod::bplus::Branchless, false>;
type VerusTreeBr = verus::bplus::BPlusTreeSet<
    VId,
    verus::bplus_layout::Layout256,
    verus::bplus_search::Branchless,
    false,
>;

/// Differential sweep over all four (implementation x strategy) instantiations:
/// production/verus x BinarySearch/Branchless. Same shuffled inserts (with
/// re-inserted duplicates), then agreement on `len`, `contains` (present and
/// absent keys), full cursor traversal from `seek_first`, and cursor `seek` at
/// present, absent, and past-the-end targets. Any divergence between the
/// Branchless columns and the BinarySearch columns is a contract violation in
/// one of the search impls; any divergence between prod and verus columns is a
/// tree-level defect.
#[test]
fn branchless_differential_prod_vs_verus() {
    let keys = shuffled(10_000);
    let mut expected: Vec<u32> = keys.clone();
    expected.sort_unstable();

    let mut p_bin = ProdTree::new();
    let mut p_br = ProdTreeBr::new();
    let mut v_bin = VerusTree::new();
    let mut v_br = VerusTreeBr::new();
    for &k in &keys {
        p_bin.insert(PId::new(k));
        p_br.insert(PId::new(k));
        v_bin.insert(VId::new(k));
        v_br.insert(VId::new(k));
    }
    // Duplicate re-inserts must be no-ops in all four.
    for &k in keys.iter().step_by(101) {
        p_bin.insert(PId::new(k));
        p_br.insert(PId::new(k));
        v_bin.insert(VId::new(k));
        v_br.insert(VId::new(k));
    }

    assert_eq!(p_bin.len(), expected.len());
    assert_eq!(p_br.len(), expected.len());
    assert_eq!(v_bin.len(), expected.len());
    assert_eq!(v_br.len(), expected.len());

    // Membership: verus has `contains`; production answers through a cursor
    // (`seek` landing exactly on the key).
    let mut pm_bin = p_bin.cursor();
    let mut pm_br = p_br.cursor();
    for k in (0u32..10_500).step_by(13) {
        let want = (k as usize) < expected.len();
        pm_bin.seek(PId::new(k));
        pm_br.seek(PId::new(k));
        assert_eq!(
            pm_bin.key().map(|x| x.raw()) == Some(k),
            want,
            "prod/bin member {k}"
        );
        assert_eq!(
            pm_br.key().map(|x| x.raw()) == Some(k),
            want,
            "prod/br member {k}"
        );
        assert_eq!(v_bin.contains(VId::new(k)), want, "verus/bin contains {k}");
        assert_eq!(v_br.contains(VId::new(k)), want, "verus/br contains {k}");
    }

    // Full in-order traversal through each cursor.
    let p_bin_walk: Vec<u32> = {
        let mut c = p_bin.cursor();
        c.seek_first();
        let mut out = Vec::new();
        while let Some(k) = c.key() {
            out.push(k.raw());
            c.step();
        }
        out
    };
    let p_br_walk: Vec<u32> = {
        let mut c = p_br.cursor();
        c.seek_first();
        let mut out = Vec::new();
        while let Some(k) = c.key() {
            out.push(k.raw());
            c.step();
        }
        out
    };
    let v_bin_walk: Vec<u32> = {
        let mut c = v_bin.cursor();
        c.seek_first();
        let mut out = Vec::new();
        while let Some(k) = c.key() {
            out.push(k.raw());
            c.step();
        }
        out
    };
    let v_br_walk: Vec<u32> = {
        let mut c = v_br.cursor();
        c.seek_first();
        let mut out = Vec::new();
        while let Some(k) = c.key() {
            out.push(k.raw());
            c.step();
        }
        out
    };
    assert_eq!(p_bin_walk, expected, "prod/bin traversal");
    assert_eq!(p_br_walk, expected, "prod/br traversal");
    assert_eq!(v_bin_walk, expected, "verus/bin traversal");
    assert_eq!(v_br_walk, expected, "verus/br traversal");

    // Cursor seek at present, absent-in-range, and past-the-end targets.
    let mut pc_bin = p_bin.cursor();
    let mut pc_br = p_br.cursor();
    let mut vc_bin = v_bin.cursor();
    let mut vc_br = v_br.cursor();
    for t in (0u32..10_400).step_by(97) {
        let want = expected.iter().copied().find(|&k| k >= t);
        pc_bin.seek(PId::new(t));
        pc_br.seek(PId::new(t));
        vc_bin.seek(VId::new(t));
        vc_br.seek(VId::new(t));
        assert_eq!(pc_bin.key().map(|k| k.raw()), want, "prod/bin seek {t}");
        assert_eq!(pc_br.key().map(|k| k.raw()), want, "prod/br seek {t}");
        assert_eq!(vc_bin.key().map(|k| k.raw()), want, "verus/bin seek {t}");
        assert_eq!(vc_br.key().map(|k| k.raw()), want, "verus/br seek {t}");
    }
}

/// Backward seeks on a positioned cursor: production's current-leaf fast
/// path answered from the current leaf whenever `target <= leaf last key`,
/// so a target below the leaf's FIRST key returned the leaf's first
/// position instead of the true global position (the twin always descends
/// and is absolute). Pins the corrected lower bound: both sides now agree
/// on random forward/backward seek sequences, checked against the sorted
/// key set directly.
#[test]
fn seek_backward_on_positioned_cursor_is_absolute() {
    const N: u32 = 200;
    let pkeys: Vec<PId> = (0..N).map(|i| PId::new(2 * i)).collect();
    let vkeys: Vec<VId> = (0..N).map(|i| VId::new(2 * i)).collect();
    let pt = ProdTree::from_sorted(&pkeys);
    let vt = VerusTree::try_from_sorted(&vkeys).expect("sorted");

    let mut pc = pt.cursor();
    let mut vc = vt.cursor();
    // Deterministic forward/backward pattern crossing leaf boundaries both
    // ways, including exact hits, gaps (odd targets), 0, and past-the-end.
    let mut st = 0x9E37_79B9u64;
    let mut targets: Vec<u32> = Vec::new();
    for _ in 0..400 {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        targets.push((st % (2 * N as u64 + 8)) as u32);
    }
    targets.extend_from_slice(&[3, 0, 2 * N - 1, 1, 2 * N, 7, 6, 5, 4, 0]);
    for &t in &targets {
        pc.seek(PId::new(t));
        vc.seek(VId::new(t));
        // Oracle: first even key >= t, i.e. 2*ceil(t/2) while it exists.
        let expect = {
            let e = t.div_ceil(2) * 2;
            if e <= 2 * (N - 1) { Some(e) } else { None }
        };
        assert_eq!(pc.key().map(|k| k.raw()), expect, "prod seek({t})");
        assert_eq!(vc.key().map(|k| k.raw()), expect, "verus seek({t})");
    }
}
