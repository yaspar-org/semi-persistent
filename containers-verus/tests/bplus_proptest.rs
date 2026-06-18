// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Property-based runtime tests for the verified `BPlusTreeSet`.
//!
//! These run the *executable* tree (Verus `requires`/`ensures` are erased under
//! plain `cargo test`) and check, at runtime, that the structural conjectures we
//! prove statically actually hold — by re-deriving the wf invariants over the
//! arena and walking the leaf-link chain. Instrumented with prints (run with
//! `cargo test -- --nocapture`).
//!
//! IMPORTANT SCOPE (matches current code, 2026-06): the public `insert` is the
//! M4b version — it requires a *leaf root*, so it handles the no-split case and
//! exactly ONE root-leaf split (to height 1). A second split would misread the
//! now-internal root as a leaf. So these tests cap N at `LEAF_CAP + 1` (= 15 for
//! Layout64U32): enough to exercise no-split inserts AND one split + the
//! leaf-link splice, but not multi-level propagation (that is M4c, the recursive
//! insert, not yet wired into `insert`). There is no cursor yet (M5), so the
//! "cursor in order" check is done by hand-walking the `link` chain.

use semi_persistent_containers_verus::bplus::BPlusTreeSet;
use semi_persistent_containers_verus::bplus_layout::{Layout64U32, NodeLayout};
use semi_persistent_containers_verus::bplus_search::BinarySearch;
use semi_persistent_containers_verus::dense_id::DenseId31;

type L = Layout64U32; // leaf_cap = 14, key_cap = 7, u32 words/arena
type Tree = BPlusTreeSet<DenseId31, L, BinarySearch, false>;

const LEAF_CAP: usize = 14;
const KEY_CAP: usize = 7;
const NIL: u32 = u32::MAX;

// ---------------------------------------------------------------------------
// Reproducible shuffle (no rand dep; fixed-seed LCG so failures are debuggable).
// ---------------------------------------------------------------------------
fn shuffled(n: u32, seed: u64) -> Vec<u32> {
    let mut v: Vec<u32> = (0..n).collect();
    let mut s = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
    // Fisher–Yates with an LCG.
    let mut i = v.len();
    while i > 1 {
        i -= 1;
        s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let j = (s >> 33) as usize % (i + 1);
        v.swap(i, j);
    }
    v
}

// ---------------------------------------------------------------------------
// Runtime wf checker — re-derives the textbook B+tree invariants over the ARENA
// (not the erased ghost Tree), returning the in-order leaf-key sequence obtained
// by walking the leaf-link chain. Panics with a diagnostic if any clause fails.
// ---------------------------------------------------------------------------

/// Recursively check one node and return (its in-order keys, its height, its
/// leftmost leaf arena index, its rightmost leaf arena index).
fn check_node(
    t: &Tree,
    idx: u32,
    is_root: bool,
    lo: Option<u32>, // exclusive-ish lower bound on every key (>= lo)
    hi: Option<u32>, // upper bound on every key (< hi)
    verbose: bool,
) -> (Vec<u32>, usize, u32, u32) {
    let node = t.nodes.get(idx);
    let count = L::count(&node);
    let is_leaf = L::is_leaf(&node);
    if verbose {
        println!(
            "  node[{idx}] {} count={count}",
            if is_leaf { "LEAF" } else { "INTERNAL" }
        );
    }

    // capacity: count <= cap; non-root nodes >= min occupancy.
    if is_leaf {
        assert!(count <= LEAF_CAP, "leaf {idx} overfull: {count} > {LEAF_CAP}");
        if !is_root {
            assert!(count >= LEAF_CAP / 2, "leaf {idx} underfull: {count} < {}", LEAF_CAP / 2);
        }
    } else {
        assert!(count <= KEY_CAP, "internal {idx} overfull: {count} > {KEY_CAP}");
        if !is_root {
            assert!(count >= KEY_CAP / 2, "internal {idx} underfull: {count} < {}", KEY_CAP / 2);
        }
        assert!(count >= 1, "internal {idx} has no separators");
    }

    // node-local sortedness of data[0..count], and the (lo, hi) range bound.
    let mut prev: Option<u32> = None;
    for i in 0..count {
        let k = L::key(&node, i);
        if let Some(p) = prev {
            assert!(p < k, "node {idx} not sorted at {i}: {p} !< {k}");
        }
        prev = Some(k);
        if let Some(l) = lo {
            assert!(k >= l, "node {idx} key {k} < lower bound {l}");
        }
        if let Some(h) = hi {
            assert!(k < h, "node {idx} key {k} >= upper bound {h}");
        }
    }

    if is_leaf {
        let keys: Vec<u32> = (0..count).map(|i| L::key(&node, i)).collect();
        return (keys, 0, idx, idx);
    }

    // internal: count separators, count+1 children; recurse with the search
    // ordering bounds (child i: keys in [sep[i-1], sep[i]) ).
    let seps: Vec<u32> = (0..count).map(|i| L::key(&node, i)).collect();
    let mut all_keys: Vec<u32> = Vec::new();
    let mut child_height: Option<usize> = None;
    let mut leftmost = NIL;
    let mut rightmost = NIL;
    for i in 0..=count {
        let child_idx = L::child(&node, i);
        let clo = if i == 0 { lo } else { Some(seps[i - 1]) };
        let chi = if i == count { hi } else { Some(seps[i]) };
        let (ckeys, ch, cl, cr) = check_node(t, child_idx, false, clo, chi, verbose);
        // balance: all children same height.
        match child_height {
            None => child_height = Some(ch),
            Some(h) => assert!(h == ch, "unbalanced under {idx}: child heights {h} != {ch}"),
        }
        if i == 0 {
            leftmost = cl;
        }
        rightmost = cr;
        all_keys.extend(ckeys);
    }
    (all_keys, child_height.unwrap() + 1, leftmost, rightmost)
}

/// Walk the leaf-link chain from `start` and return the concatenated leaf keys.
/// Checks the chain visits each leaf once and terminates at NIL.
fn walk_leaf_chain(t: &Tree, start: u32, expected_leaves: usize, verbose: bool) -> Vec<u32> {
    let mut out = Vec::new();
    let mut cur = start;
    let mut steps = 0;
    while cur != NIL {
        steps += 1;
        assert!(steps <= expected_leaves + 1, "leaf chain too long / cyclic at {cur}");
        let node = t.nodes.get(cur);
        assert!(L::is_leaf(&node), "leaf chain hit non-leaf node {cur}");
        let count = L::count(&node);
        for i in 0..count {
            out.push(L::key(&node, i));
        }
        let next = L::link(&node);
        if verbose {
            println!("  chain: leaf[{cur}] -> {}", if next == NIL { "NIL".to_string() } else { next.to_string() });
        }
        cur = next;
    }
    out
}

/// Full invariant check: structural recursion + leaf-chain agreement, returning
/// the in-order model (the tree's keys, sorted).
fn check_wf_and_model(t: &Tree, verbose: bool) -> Vec<u32> {
    // root index: read it via the public API surface. root is `pub`.
    let root = t.root;
    if verbose {
        println!("wf-check: root={root} nkeys={}", t.len());
    }
    let (tree_keys, height, leftmost, _rightmost) = check_node(t, root, true, None, None, verbose);

    // clause: tree keys are globally sorted, no dups.
    for w in tree_keys.windows(2) {
        assert!(w[0] < w[1], "global order violated: {} !< {}", w[0], w[1]);
    }
    // clause: nkeys cache == model length.
    assert!(
        t.len() == tree_keys.len(),
        "nkeys {} != model len {}",
        t.len(),
        tree_keys.len()
    );

    // clause 5: the leaf-link chain (from the leftmost leaf) equals the tree's
    // in-order keys. This is the conjecture the cursor will rely on.
    let chain_keys = walk_leaf_chain(t, leftmost, tree_keys.len() + 1, verbose);
    assert!(
        chain_keys == tree_keys,
        "leaf-link chain disagrees with tree order:\n  chain = {:?}\n  tree  = {:?}",
        chain_keys,
        tree_keys
    );
    if verbose {
        println!("  height={height} model={:?}", tree_keys);
    }
    tree_keys
}

fn key(n: u32) -> DenseId31 {
    DenseId31::new(n)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// Insert 0..N in random order; after each insert, the wf invariants hold and
/// the leaf chain yields the inserted keys in order without gaps. N capped at
/// LEAF_CAP so the root stays a LEAF for every `insert` call — the current
/// public `insert`'s contract (`requires is_leaf(root)`). The per-step re-insert
/// no-op check also relies on the root staying a leaf. (One-split behaviour is
/// covered separately by `the_one_split`; multi-level insert is M4c, pending.)
#[test]
fn insert_random_then_cursor_in_order() {
    for &n in &[1u32, 2, 7, 13, 14] {
        for seed in 0..8u64 {
            let order = shuffled(n, seed);
            let verbose = n == 14 && seed == 0;
            if verbose {
                println!("\n=== N={n} seed={seed} order={:?} ===", order);
            }
            let mut t = Tree::new();
            assert!(t.is_empty());

            for (step, &x) in order.iter().enumerate() {
                let added = t.insert(key(x));
                assert!(added, "N={n} seed={seed}: insert {x} (step {step}) reported not-added");
                // re-insert is a no-op (root is still a leaf since N <= LEAF_CAP).
                let again = t.insert(key(x));
                assert!(!again, "N={n} seed={seed}: re-insert {x} reported added");

                // every key inserted so far must be present.
                for &y in order.iter().take(step + 1) {
                    assert!(t.contains(key(y)), "N={n} seed={seed}: {y} missing after inserting {x}");
                }
                // wf + cursor order holds at every step.
                let model = check_wf_and_model(&t, verbose);
                assert_eq!(model.len(), step + 1, "N={n} seed={seed}: model size wrong");
            }

            // final: the model is exactly 0..n in order.
            let model = check_wf_and_model(&t, verbose);
            let want: Vec<u32> = (0..n).collect();
            assert_eq!(model, want, "N={n} seed={seed}: final model != 0..N");
            assert!(!t.contains(key(n)), "N={n}: absent key reported present");
        }
    }
    println!("\ninsert_random_then_cursor_in_order: OK");
}

/// Sanity: an empty tree and a single key.
#[test]
fn empty_and_singleton() {
    let mut t = Tree::new();
    assert!(t.is_empty());
    assert_eq!(t.len(), 0);
    assert!(!t.contains(key(0)));
    assert_eq!(check_wf_and_model(&t, true), Vec::<u32>::new());

    assert!(t.insert(key(42)));
    assert!(!t.is_empty());
    assert_eq!(t.len(), 1);
    assert!(t.contains(key(42)));
    assert!(!t.contains(key(41)));
    assert_eq!(check_wf_and_model(&t, true), vec![42]);
    println!("empty_and_singleton: OK");
}

/// The exact boundary: fill a leaf to LEAF_CAP (no split), then one more forces
/// the single split to height 1. Verifies the split preserves order + chain.
#[test]
fn the_one_split() {
    let mut t = Tree::new();
    // ascending insert fills the root leaf, then splits on the 15th.
    for x in 0..LEAF_CAP as u32 {
        assert!(t.insert(key(x)));
    }
    println!("after {LEAF_CAP} inserts (should be a single full leaf root):");
    let m1 = check_wf_and_model(&t, true);
    assert_eq!(m1, (0..LEAF_CAP as u32).collect::<Vec<_>>());

    // the split.
    assert!(t.insert(key(LEAF_CAP as u32)));
    println!("after the split (should be height 1: internal root + 2 leaves):");
    let m2 = check_wf_and_model(&t, true);
    assert_eq!(m2, (0..=LEAF_CAP as u32).collect::<Vec<_>>());
    println!("the_one_split: OK");
}

/// The split from many random fill orders: insert LEAF_CAP+1 distinct keys in
/// shuffled order (root-leaf the whole time until the last insert splits it).
/// Exercises both split cases (the inserted key landing in the left vs right
/// half) and checks the resulting height-1 tree is wf with the chain in order.
#[test]
fn random_fill_then_split() {
    let n = LEAF_CAP as u32 + 1; // 15: fills the leaf, last insert splits.
    for seed in 0..64u64 {
        let order = shuffled(n, seed);
        let mut t = Tree::new();
        for &x in &order {
            // only valid while the root is a leaf; the LAST insert does the split.
            t.insert(key(x));
        }
        let model = check_wf_and_model(&t, false);
        let want: Vec<u32> = (0..n).collect();
        assert_eq!(model, want, "seed={seed} order={:?}: model != 0..{n}", order);
        // every key present, absent key absent.
        for x in 0..n {
            assert!(t.contains(key(x)), "seed={seed}: {x} missing");
        }
        assert!(!t.contains(key(n)));
    }
    println!("random_fill_then_split: OK (64 seeds)");
}
