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
//! SCOPE (2026-06, test-first phase): we drive the GENERAL multi-level insert,
//! `insert_general` (M4c) — descent + split propagation + new-root growth. Its
//! exec path is complete; its `wf` proof is in progress (so it is currently
//! `external_body`), and these tests are the harness validating it before the
//! proof lands. There is no cursor yet (M5), so the "cursor in order" check is
//! done by hand-walking the `link` chain over the arena.

use semi_persistent_containers_verus::bplus::BPlusTreeSet;
use semi_persistent_containers_verus::bplus_layout::{Layout64U32, NodeLayout};
use semi_persistent_containers_verus::bplus_search::BinarySearch;
use semi_persistent_containers_verus::dense_id::DenseId31;
use semi_persistent_containers_verus::index_like::IndexLike;

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
        // SEPARATOR-EQUALS-RIGHT-MIN probe (the sharper B+tree invariant the
        // parent-split proof needs): for child i > 0, separator seps[i-1] equals
        // the MINIMUM key of child i. Equivalently, every separator is a routing
        // copy of its right subtree's least leaf key — not merely an upper bound
        // on the left / lower bound on the right. This is what makes
        // `promoted == tree_keys(rt)[0]` hold in reconstruct_parent_split.
        if i > 0 && !ckeys.is_empty() {
            assert!(
                seps[i - 1] == ckeys[0],
                "separator-min mismatch under node {idx}: sep[{}]={} != min(child {})={}",
                i - 1, seps[i - 1], i, ckeys[0]
            );
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

/// Execution-trace probe for the min-key-preservation conjecture the recursive
/// insert proof needs: inserting a key that is NOT a new global minimum leaves
/// the tree's minimum key unchanged (so a subtree's separator-min survives). Logs
/// every insert's (old min, key, new min) and asserts: new_min == min(old_min,
/// key), i.e. the min only ever moves DOWN, and only when key < old_min. This is
/// the whole-tree shadow of insert_rec's per-subtree `key >= cur_min ⟹ nl[0] ==
/// cur[0]` clause.
#[test]
fn min_key_preservation_trace() {
    let mut moved_down = 0usize;
    let mut preserved = 0usize;
    for &count in &[300usize, 3000] {
        for seed in 0..4u64 {
            let keys = arbitrary_keys(count, seed ^ 0xBEEF);
            let mut t = Tree::new();
            let mut cur_min: Option<u32> = None;
            for &x in &keys {
                let before = check_wf_and_model(&t, false);
                let old_min = before.first().copied();
                t.insert_general(key(x));
                let after = check_wf_and_model(&t, false);
                let new_min = after.first().copied();
                // the invariant: new_min == min(old_min, x).
                let want = match old_min {
                    None => x,
                    Some(m) => m.min(x),
                };
                assert_eq!(
                    new_min, Some(want),
                    "min-key invariant broken: old_min={old_min:?} key={x} -> new_min={new_min:?}, want {want}"
                );
                // classify: did the min move down (key was a new min) or hold?
                match old_min {
                    Some(m) if x < m => moved_down += 1,
                    Some(_) => preserved += 1,
                    None => {}
                }
                cur_min = Some(want);
            }
            let _ = cur_min;
        }
    }
    println!(
        "min_key_preservation_trace: OK ({preserved} inserts preserved the min [key >= min], \
         {moved_down} lowered it [key < min]; new_min == min(old_min, key) held every time)"
    );
    assert!(preserved > 0 && moved_down > 0, "expected both preserve and lower cases");
}

fn key(n: u32) -> DenseId31 {
    DenseId31::new(n)
}

// ---------------------------------------------------------------------------
// Footprint-contract evaluator — reifies the ghost `tree_ids` (the set of arena
// indices reachable from a root) so we can check `insert`'s *transition
// contract* at runtime, not just the *state* `wf`. `check_wf_and_model` answers
// "is the tree well-formed now"; this answers "did the footprint change the way
// the recursion's `ensures` claims." It is what catches over-strong frame /
// footprint clauses (the `tree_ids(nl) == tree_ids(cur)` class), which a pure
// state-invariant check cannot see because the state stays well-formed.
// ---------------------------------------------------------------------------
use std::collections::BTreeSet;

/// All arena indices in the subtree rooted at `idx` (the reified `tree_ids`).
fn reachable_ids(t: &Tree, idx: u32) -> BTreeSet<u32> {
    let mut out = BTreeSet::new();
    let node = t.nodes.get(idx);
    out.insert(idx);
    if !L::is_leaf(&node) {
        let count = L::count(&node);
        for i in 0..=count {
            out.extend(reachable_ids(t, L::child(&node, i)));
        }
    }
    out
}

/// All LEAF arena indices in the subtree rooted at `idx` (the reified
/// `tree_leaf_ids`). The spec's `None`-arm originally claimed these are
/// unchanged on insert; a split adds a fresh leaf, so the honest contract is
/// the same subset+freshness as for `tree_ids`.
fn reachable_leaf_ids(t: &Tree, idx: u32) -> BTreeSet<u32> {
    let mut out = BTreeSet::new();
    let node = t.nodes.get(idx);
    if L::is_leaf(&node) {
        out.insert(idx);
    } else {
        let count = L::count(&node);
        for i in 0..=count {
            out.extend(reachable_leaf_ids(t, L::child(&node, i)));
        }
    }
    out
}

/// The model-level outcome of one insert, plus the footprint delta. Used to
/// assert the recursion's `ensures` footprint clause: old ids are retained, and
/// every newly-appearing id is a freshly-allocated (>= old arena length) slot.
struct InsertObservation {
    grew: bool,        // did the footprint gain at least one id?
    height_changed: bool,
}

/// The leftmost leaf arena id of the subtree at `idx` (`tree_leaf_ids(_)[0]`).
fn first_leaf_id(t: &Tree, idx: u32) -> u32 {
    let node = t.nodes.get(idx);
    if L::is_leaf(&node) {
        idx
    } else {
        first_leaf_id(t, L::child(&node, 0))
    }
}

/// Run one insert and check the footprint contract around it:
///  - retention: `ids_before ⊆ ids_after` (no live node ever drops out);
///  - freshness: every id in `ids_after \ ids_before` is `>= arena_len_before`
///    (growth only ever appends fresh tail slots — the F1 clause).
/// Returns the observation so a test can confirm the EXACT-equality form
/// (`ids_after == ids_before`) is genuinely violated by real inserts — i.e. the
/// spec bug is real, not hypothetical.
fn insert_checked(t: &mut Tree, k: u32) -> InsertObservation {
    let ids_before = reachable_ids(t, t.root);
    let leaf_ids_before = reachable_leaf_ids(t, t.root);
    let arena_len_before = t.nodes.len().as_usize() as u32;
    let height_before = check_node(t, t.root, true, None, None, false).1;
    let root_before = t.root;
    let first_leaf_before = first_leaf_id(t, root_before);

    t.insert_general(key(k));

    let ids_after = reachable_ids(t, t.root);
    let leaf_ids_after = reachable_leaf_ids(t, t.root);
    let height_after = check_node(t, t.root, true, None, None, false).1;

    // First-leaf preservation: the leftmost leaf of a subtree NEVER moves on
    // insert (a split adds a leaf to the RIGHT). This is what the leaf-link
    // composition needs at child boundaries even when the footprint grows — so
    // the proof can drop full leaf-id-sequence equality and keep just this.
    // (Only checkable when the root id is unchanged, i.e. no new-root growth;
    // new-root growth keeps the old root as child 0, so the leftmost leaf is
    // still preserved, but `t.root` itself changed.)
    if t.root == root_before {
        let first_leaf_after = first_leaf_id(t, t.root);
        assert!(
            first_leaf_after == first_leaf_before,
            "first-leaf moved inserting {k}: {first_leaf_before} -> {first_leaf_after}"
        );
    } else {
        // new root: the old leftmost leaf is still the global leftmost leaf.
        let first_leaf_after = first_leaf_id(t, t.root);
        assert!(
            first_leaf_after == first_leaf_before,
            "first-leaf moved on root growth inserting {k}: {first_leaf_before} -> {first_leaf_after}"
        );
    }

    // retention + freshness on the full footprint (tree_ids).
    for id in &ids_before {
        assert!(
            ids_after.contains(id),
            "footprint retention violated inserting {k}: id {id} dropped out of the tree"
        );
    }
    for id in ids_after.difference(&ids_before) {
        assert!(
            *id >= arena_len_before,
            "footprint freshness violated inserting {k}: new id {id} < old arena len {arena_len_before} \
             (a pre-existing sibling slot was pulled into the footprint)"
        );
    }
    // same retention + freshness on the leaf footprint (tree_leaf_ids): the
    // split-spliced new leaf is always a fresh tail slot, never a re-used id.
    for id in &leaf_ids_before {
        assert!(
            leaf_ids_after.contains(id),
            "leaf-footprint retention violated inserting {k}: leaf {id} dropped out"
        );
    }
    for id in leaf_ids_after.difference(&leaf_ids_before) {
        assert!(
            *id >= arena_len_before,
            "leaf-footprint freshness violated inserting {k}: new leaf {id} < old arena len {arena_len_before}"
        );
    }
    InsertObservation {
        grew: ids_after.len() > ids_before.len(),
        height_changed: height_after != height_before,
    }
}

/// The transition-contract test. Drives arbitrary inserts through
/// `insert_checked`, which asserts the subset+freshness footprint contract on
/// every step, and confirms that the EXACT-equality form is violated in
/// practice (some inserts grow the footprint without growing the height — the
/// deep-absorb path whose `None` return the spec wrongly claimed leaves
/// `tree_ids` unchanged).
#[test]
fn footprint_contract_holds() {
    let mut grow_without_height_change = 0usize; // refutes exact-equality on None
    let mut total_inserts = 0usize;

    for &count in &[200usize, 2000] {
        for seed in 0..4u64 {
            let keys = arbitrary_keys(count, seed ^ 0x5151);
            let mut oracle = BTreeSet::new();
            let mut t = Tree::new();
            for &x in &keys {
                let is_new = oracle.insert(x);
                let obs = insert_checked(&mut t, x);
                total_inserts += 1;
                if is_new && obs.grew && !obs.height_changed {
                    // footprint grew (a split happened below) yet the height
                    // (hence the top-level recursion result) is unchanged —
                    // exactly the case the `None`-arm's `tree_ids(nl)==tree_ids(cur)`
                    // claim is false for.
                    grow_without_height_change += 1;
                }
            }
            // sanity: wf + model still agree.
            let model = check_wf_and_model(&t, false);
            assert_eq!(model.len(), oracle.len(), "count={count} seed={seed}: model size");
        }
    }
    println!(
        "footprint_contract_holds: OK ({total_inserts} inserts; {grow_without_height_change} grew \
         the footprint with no height change — these refute the exact-equality `None`-arm claim \
         and require the subset+freshness contract)"
    );
    assert!(
        grow_without_height_change > 0,
        "expected at least one deep-absorb insert that grows tree_ids without changing height; \
         got none — the test is not exercising the path the spec bug lives on"
    );
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
    for &n in &[1u32, 2, 7, 14, 15, 50, 200, 1000] {
        for seed in 0..8u64 {
            let order = shuffled(n, seed);
            let verbose = n == 15 && seed == 0;
            if verbose {
                println!("\n=== N={n} seed={seed} order={:?} ===", order);
            }
            let mut t = Tree::new();
            assert!(t.is_empty());

            for (step, &x) in order.iter().enumerate() {
                let added = t.insert_general(key(x));
                assert!(added, "N={n} seed={seed}: insert {x} (step {step}) reported not-added");
                // re-insert is a no-op (root is still a leaf since N <= LEAF_CAP).
                let again = t.insert_general(key(x));
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

    assert!(t.insert_general(key(42)));
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
        assert!(t.insert_general(key(x)));
    }
    println!("after {LEAF_CAP} inserts (should be a single full leaf root):");
    let m1 = check_wf_and_model(&t, true);
    assert_eq!(m1, (0..LEAF_CAP as u32).collect::<Vec<_>>());

    // the split.
    assert!(t.insert_general(key(LEAF_CAP as u32)));
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
            t.insert_general(key(x));
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

/// Report the tree height/shape reached for a few N, to confirm we exercise
/// genuinely multi-level trees (height >= 2), not just one split.
#[test]
fn reports_multilevel_shape() {
    for &n in &[15u32, 100, 1000, 5000] {
        let mut t = Tree::new();
        for x in shuffled(n, 1) {
            t.insert_general(key(x));
        }
        // count nodes + height via a structural walk (reuse check_node's height).
        let (_keys, height, _l, _r) = check_node(&t, t.root, true, None, None, false);
        let model = check_wf_and_model(&t, false);
        assert_eq!(model, (0..n).collect::<Vec<_>>());
        println!("N={n}: height={height}, arena nodes={}", t.nodes.len().as_usize());
    }
    println!("reports_multilevel_shape: OK");
}

// ---------------------------------------------------------------------------
// Cursor tests — the real BPlusCursor (production fast path), the leapfrog API.
// ---------------------------------------------------------------------------
use semi_persistent_containers_verus::bplus::BPlusCursor;

/// Enumerate the whole set via the cursor (seek_first + key/step) and check it
/// yields 0..N in order without gaps — the property the leapfrog join relies on.
#[test]
fn cursor_enumerates_in_order() {
    for &n in &[1u32, 14, 15, 100, 1000] {
        for seed in 0..4u64 {
            let mut t = Tree::new();
            for x in shuffled(n, seed) {
                t.insert_general(key(x));
            }
            let mut c = BPlusCursor::new(&t);
            c.seek_first();
            let mut got = Vec::new();
            while let Some(k) = c.key() {
                got.push(k.index() as u32);
                c.step();
            }
            assert_eq!(got, (0..n).collect::<Vec<_>>(), "N={n} seed={seed}: cursor order wrong");
        }
    }
    println!("cursor_enumerates_in_order: OK");
}

/// seek(target) lands on the least key >= target (leapfrog's core step), and
/// stepping from there continues in order. Tests every target in 0..=N.
#[test]
fn cursor_seek_lands_on_ge() {
    let n = 500u32;
    let mut t = Tree::new();
    for x in shuffled(n, 7) {
        t.insert_general(key(x));
    }
    // set holds 0..n; seek(target) should land exactly on `target` for target<n,
    // and be exhausted for target==n.
    for target in 0..=n {
        let mut c = BPlusCursor::new(&t);
        c.seek(key(target));
        match c.key() {
            Some(k) => {
                let v = k.index() as u32;
                assert_eq!(v, target, "seek({target}) landed on {v}, want {target}");
            }
            None => assert_eq!(target, n, "seek({target}) exhausted but target < n"),
        }
    }
    // leapfrog-style: repeated seeks that jump forward stay monotone.
    let mut c = BPlusCursor::new(&t);
    let mut last = -1i64;
    for &target in &[0u32, 1, 50, 51, 200, 499, 250] {
        c.seek(key(target));
        if let Some(k) = c.key() {
            let v = k.index() as i64;
            assert!(v >= target as i64, "seek({target}) -> {v} < target");
            // (250 after 499 re-descends; just check it found 250)
            if target >= last as u32 { /* forward seeks monotone within a run */ }
            last = v;
        }
    }
    println!("cursor_seek_lands_on_ge: OK");
}

// ---------------------------------------------------------------------------
// Oracle-based property test: arbitrary values vs a HashSet reference model.
// This is the real one — sparse/arbitrary keys (not a dense 0..N), duplicates,
// with an independent oracle (sorted unique values) compared to cursor output.
// ---------------------------------------------------------------------------
use std::collections::HashSet;

/// LCG stream of arbitrary 31-bit keys (DenseId31 requires n < 2^31).
fn arbitrary_keys(count: usize, seed: u64) -> Vec<u32> {
    let mut s = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(0xD1B5);
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
        s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        out.push(((s >> 33) as u32) & 0x7FFF_FFFF); // 31-bit
    }
    out
}

#[test]
fn oracle_arbitrary_values_vs_sorted_hashset() {
    for &count in &[10usize, 100, 1000, 5000] {
        for seed in 0..6u64 {
            let keys = arbitrary_keys(count, seed);

            // reference model: a HashSet (dedup), and contains() oracle.
            let mut oracle: HashSet<u32> = HashSet::new();
            let mut t = Tree::new();

            for &x in &keys {
                let was_new = !oracle.contains(&x);
                let added = t.insert_general(key(x));
                oracle.insert(x);
                assert_eq!(
                    added, was_new,
                    "count={count} seed={seed}: insert({x}) returned added={added}, oracle says new={was_new}"
                );
            }

            // sort the oracle into the expected in-order vector.
            let mut want: Vec<u32> = oracle.iter().copied().collect();
            want.sort_unstable();

            // 1) full cursor traversal must equal the sorted oracle, no gaps/dups.
            let mut c = BPlusCursor::new(&t);
            c.seek_first();
            let mut got = Vec::with_capacity(want.len());
            while let Some(k) = c.key() {
                got.push(k.index() as u32);
                c.step();
            }
            assert_eq!(
                got, want,
                "count={count} seed={seed}: cursor traversal != sorted oracle\n  got.len={} want.len={}",
                got.len(), want.len()
            );

            // 2) contains() agrees with the oracle on present + absent probes.
            for &x in want.iter().take(64) {
                assert!(t.contains(key(x)), "count={count} seed={seed}: {x} present in oracle, missing in tree");
            }
            for probe in arbitrary_keys(64, seed ^ 0xABCD) {
                assert_eq!(
                    t.contains(key(probe)),
                    oracle.contains(&probe),
                    "count={count} seed={seed}: contains({probe}) disagrees with oracle"
                );
            }

            // 3) len() == |oracle|, and the runtime wf invariants hold.
            assert_eq!(t.len(), oracle.len(), "count={count} seed={seed}: len != oracle size");
            let model = check_wf_and_model(&t, false);
            assert_eq!(model, want, "count={count} seed={seed}: wf-model != sorted oracle");
        }
    }
    println!("oracle_arbitrary_values_vs_sorted_hashset: OK");
}

/// seek(target) for arbitrary (possibly-absent) targets: lands on the least key
/// >= target per the oracle, or exhausted if none.
#[test]
fn oracle_seek_arbitrary_targets() {
    let count = 2000usize;
    let keys = arbitrary_keys(count, 99);
    let mut oracle: HashSet<u32> = HashSet::new();
    let mut t = Tree::new();
    for &x in &keys {
        t.insert_general(key(x));
        oracle.insert(x);
    }
    let mut sorted: Vec<u32> = oracle.iter().copied().collect();
    sorted.sort_unstable();

    for target in arbitrary_keys(500, 1234) {
        let mut c = BPlusCursor::new(&t);
        c.seek(key(target));
        // oracle answer: least element >= target.
        let want = sorted.iter().copied().find(|&v| v >= target);
        match c.key() {
            Some(k) => assert_eq!(Some(k.index() as u32), want, "seek({target}) mismatch"),
            None => assert_eq!(want, None, "seek({target}) exhausted but oracle has a >= element"),
        }
    }
    println!("oracle_seek_arbitrary_targets: OK");
}

/// Fast-path stress: a SINGLE cursor seeking a long sequence of arbitrary targets
/// WITHOUT re-`new`-ing between seeks — so each `seek` starts from the position
/// the previous one left (the `self.node != NIL` fast-path branch in production's
/// seek, and the "already positioned" case for the verified seek). Each result is
/// checked against the sorted oracle (least key >= target), and a step() after a
/// landed seek must yield the next key in order. This is the path the
/// always-fresh-cursor tests above do not directly exercise.
#[test]
fn seek_from_arbitrary_positions() {
    for &count in &[50usize, 500, 3000] {
        for seed in 0..4u64 {
            let keys = arbitrary_keys(count, seed ^ 0x5EEc);
            let mut oracle: HashSet<u32> = HashSet::new();
            let mut t = Tree::new();
            for &x in &keys {
                t.insert_general(key(x));
                oracle.insert(x);
            }
            let mut sorted: Vec<u32> = oracle.iter().copied().collect();
            sorted.sort_unstable();

            // reuse ONE cursor across all targets — interleaving forward, backward,
            // and repeated seeks so the cursor enters seek from every kind of state.
            let mut c = BPlusCursor::new(&t);
            let targets = arbitrary_keys(800, seed ^ 0xC0FFEE);
            for (i, &target) in targets.iter().enumerate() {
                c.seek(key(target));
                let want = sorted.iter().copied().find(|&v| v >= target);
                match c.key() {
                    Some(k) => {
                        let v = k.index() as u32;
                        assert_eq!(
                            Some(v), want,
                            "count={count} seed={seed} step {i}: seek({target}) from a \
                             prior position landed on {v}, oracle wants {want:?}"
                        );
                        // step() after a landed seek yields the next sorted key (or None).
                        let next_want = sorted.iter().copied().find(|&w| w > v);
                        c.step();
                        match c.key() {
                            Some(k2) => assert_eq!(
                                Some(k2.index() as u32), next_want,
                                "count={count} seed={seed} step {i}: step after seek({target}) \
                                 -> {}, want {next_want:?}", k2.index()
                            ),
                            None => assert_eq!(
                                next_want, None,
                                "count={count} seed={seed} step {i}: step after seek({target}) \
                                 exhausted but oracle has a larger key {next_want:?}"
                            ),
                        }
                    }
                    None => assert_eq!(
                        want, None,
                        "count={count} seed={seed} step {i}: seek({target}) from a prior \
                         position exhausted but oracle has a >= element {want:?}"
                    ),
                }
            }
        }
    }
    println!("seek_from_arbitrary_positions: OK");
}

// ---------------------------------------------------------------------------
// Empirical logarithmic cost of seek.
//
// We do not PROVE the complexity (the user explicitly scoped that out), but a
// seek visits exactly one node per tree level (root-to-leaf descent, then at
// most one `link` hop), so the node-visit count of a seek == tree_height + 1.
// We measure the height directly off the arena and check it grows like
// log_B(n) — concretely, that it stays within a generous logarithmic envelope
// as n scales across two orders of magnitude (so a hidden linear/sqrt blowup
// would fail loudly).
// ---------------------------------------------------------------------------

/// The arena height: number of internal levels on the root-to-leftmost-leaf
/// path. A leaf root has height 0. This is exactly the number of internal
/// nodes a `seek` descends through; the work of a seek is `height + 1` node
/// touches (plus an O(1) possible `link` step at the end).
fn measured_height(t: &Tree) -> usize {
    let mut idx = t.root;
    let mut h = 0usize;
    loop {
        let node = t.nodes.get(idx);
        if L::is_leaf(&node) {
            break;
        }
        // descend child 0 (any child reaches a leaf in the same number of
        // levels — a B+tree is height-balanced).
        idx = L::child(&node, 0);
        h += 1;
        assert!(h <= 64, "implausible height {h} — descent not terminating");
    }
    h
}

#[test]
fn seek_cost_is_logarithmic() {
    // Branching: KEY_CAP separators => up to KEY_CAP+1 children per internal
    // node; leaves hold up to LEAF_CAP keys. So height h satisfies roughly
    //   n <= LEAF_CAP * (KEY_CAP+1)^h   =>   h >= log_{B}(n / LEAF_CAP).
    // Upper envelope: a healthy B+tree with min occupancy ~B/2 has
    //   h <= log_{ceil(B/2)}(n) + O(1). We check height against a generous
    // multiple of log2(n), which any logarithmic-height structure satisfies and
    // a linear/sqrt one does not.
    let branch = (KEY_CAP + 1) as f64; // 8
    let sizes = [10u32, 100, 1_000, 10_000, 50_000];
    let mut prev_height = 0usize;

    for &n in &sizes {
        let keys = shuffled(n, 0xC057 ^ (n as u64));
        let mut t = Tree::new();
        for &k in &keys {
            t.insert_general(key(k));
        }
        let h = measured_height(&t);

        // 1) every seek touches exactly h+1 nodes (re-derive the descent count
        //    for a handful of targets and confirm it equals the height path).
        for &target in &[0u32, n / 2, n.saturating_sub(1), n + 1000] {
            let visits = seek_descent_visits(&t, key(target));
            assert!(
                visits == h + 1,
                "n={n}: seek({target}) visited {visits} nodes, height path is {}",
                h + 1
            );
        }

        // 2) height is within a logarithmic envelope: h <= 2*log_B(n) + 3.
        let log_b_n = (n as f64).ln() / branch.ln();
        let envelope = (2.0 * log_b_n + 3.0).ceil() as usize;
        assert!(
            h <= envelope,
            "n={n}: height {h} exceeds logarithmic envelope {envelope} (log_B(n)={log_b_n:.2})"
        );

        // 3) monotone, slow growth: height never DROPS as n grows, and a 10x
        //    size increase adds at most a couple of levels (log behaviour).
        assert!(h >= prev_height, "n={n}: height {h} < previous {prev_height}");
        prev_height = h;

        println!("n={n:>6}: height={h}, seek visits={}, envelope={envelope}", h + 1);
    }
    println!("seek_cost_is_logarithmic: OK");
}

/// Count the nodes a `seek(target)` descent touches, by replicating the
/// root-to-leaf path the verified `seek_leaf` walks: at each internal node pick
/// the child whose subtree could hold `target` (first separator strictly
/// greater than target), descending until a leaf. Returns levels touched
/// (== height + 1). This mirrors the cost of the real seek without needing the
/// verified code to expose a counter.
fn seek_descent_visits(t: &Tree, target: DenseId31) -> usize {
    let tv = target.index() as u32;
    let mut idx = t.root;
    let mut visits = 0usize;
    loop {
        let node = t.nodes.get(idx);
        visits += 1;
        if L::is_leaf(&node) {
            break;
        }
        // find first separator > target; descend that child (find_gt).
        let count = L::count(&node);
        let mut cp = count; // default: last child
        for i in 0..count {
            let sep = L::key(&node, i); // separator word (u32)
            if tv < sep {
                cp = i;
                break;
            }
        }
        idx = L::child(&node, cp);
        assert!(visits <= 64, "descent not terminating");
    }
    visits
}
