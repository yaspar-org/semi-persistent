// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The ghost recursive B+tree model, and its structural well-formedness.
//!
//! Following the arena / dynamic-frames method
//! ([Ch 9](../design/09-arena-aliasing-dynamic-frames.md)) and the
//! [`wf` invariant analysis](../../doc/future/bplus-wf-invariant-analysis.md),
//! the executable `BPlusTreeSet` (a node arena + root id) is a *representation*
//! of a ghost mathematical object: a recursive `Tree`. This module defines that
//! ghost object and its *structural* invariant `tree_wf` — the textbook B+tree
//! invariants (balance, node-local sortedness, cross-node search ordering, key
//! counts) stated purely over the `Tree`, with **no reference to the arena**.
//! [`bplus`](crate::bplus) ties the arena to a `Tree` via a flat binding
//! predicate; keeping the recursion here (on the ghost object) and the binding
//! there (one `forall` over ids) is the split that keeps both tractable — the
//! same "content off the ghost object, ids only in-range" lesson that made the
//! flat arena containers go through.
//!
//! Keys are modeled as `nat` (the `IndexLike::as_nat` projection of the stored
//! word), so ordering is `nat` `<`, where transitivity/totality are free.
//!
//! ## The recursive-datatype idiom (see proof-attempts log)
//!
//! `Tree` carries its children as `Seq<Tree>`. A spec fn over `Tree` and its
//! companion over `Seq<Tree>` are mutually recursive, and their `decreases`
//! clauses must be *type-compatible*: the node fn uses `decreases t`, the forest
//! fn `decreases kids` (the `Seq<Tree>` value, which Verus orders by element
//! height) — **not** `decreases kids.len()` (an `int`), which is rejected. The
//! recursion must be explicit cons (`f(kids[0]) ++ forest(kids.drop_first())`);
//! a closure `Seq::new(len, |i| f(kids[i]))` hides `kids[i] < t` from the
//! termination checker. One-step unfolding needs a `lemma_*_cons`.

use vstd::prelude::*;

verus! {

/// The ghost B+tree. Leaves carry their key sequence; internal nodes carry
/// separator keys and child subtrees. `id` is the arena index the node lives
/// at (the dynamic-frames "location"); keys/separators are `as_nat` values.
pub enum Tree {
    Leaf { id: nat, keys: Seq<nat> },
    Inner { id: nat, seps: Seq<nat>, kids: Seq<Tree> },
}

// ===========================================================================
// Derived views: keys (in-order), ids (footprint), height. Each is a node fn
// + a forest companion, decreasing on the datatype height.
// ===========================================================================

/// In-order key sequence (the abstract sorted-set model). Leaf: its keys.
/// Inner: the concatenation of its children's key sequences left to right.
pub open spec fn tree_keys(t: Tree) -> Seq<nat>
    decreases t
{
    match t {
        Tree::Leaf { keys, .. } => keys,
        Tree::Inner { kids, .. } => forest_keys(kids),
    }
}

pub open spec fn forest_keys(kids: Seq<Tree>) -> Seq<nat>
    decreases kids
{
    if kids.len() == 0 {
        Seq::empty()
    } else {
        tree_keys(kids[0]) + forest_keys(kids.drop_first())
    }
}

/// The set of arena ids occupied by the tree (its dynamic-frames region).
pub open spec fn tree_ids(t: Tree) -> Set<nat>
    decreases t
{
    match t {
        Tree::Leaf { id, .. } => set![id],
        Tree::Inner { id, kids, .. } => set![id].union(forest_ids(kids)),
    }
}

pub open spec fn forest_ids(kids: Seq<Tree>) -> Set<nat>
    decreases kids
{
    if kids.len() == 0 {
        Set::empty()
    } else {
        tree_ids(kids[0]).union(forest_ids(kids.drop_first()))
    }
}

/// Height: a leaf is 0; an internal node is 1 + the max child height. (Balance,
/// below, forces all children to the *same* height, but `tree_height` is the
/// general max so it is well-defined before balance is assumed.)
pub open spec fn tree_height(t: Tree) -> nat
    decreases t
{
    match t {
        Tree::Leaf { .. } => 0,
        Tree::Inner { kids, .. } => 1 + forest_max_height(kids),
    }
}

pub open spec fn forest_max_height(kids: Seq<Tree>) -> nat
    decreases kids
{
    if kids.len() == 0 {
        0
    } else {
        let h0 = tree_height(kids[0]);
        let hr = forest_max_height(kids.drop_first());
        if h0 > hr { h0 } else { hr }
    }
}

/// The id at a node's root (its own arena index).
pub open spec fn tree_root_id(t: Tree) -> nat {
    match t {
        Tree::Leaf { id, .. } => id,
        Tree::Inner { id, .. } => id,
    }
}

// ===========================================================================
// One-step unfolding lemmas for the forest companions (the `lemma_*_cons` the
// idiom requires — Verus does not unfold a `decreases kids` fn automatically in
// a caller). Stated for non-empty `kids`.
// ===========================================================================

pub proof fn lemma_forest_keys_cons(kids: Seq<Tree>)
    requires kids.len() > 0,
    ensures forest_keys(kids) == tree_keys(kids[0]) + forest_keys(kids.drop_first()),
{
}

pub proof fn lemma_forest_ids_cons(kids: Seq<Tree>)
    requires kids.len() > 0,
    ensures forest_ids(kids) == tree_ids(kids[0]).union(forest_ids(kids.drop_first())),
{
}

pub proof fn lemma_forest_max_height_cons(kids: Seq<Tree>)
    requires kids.len() > 0,
    ensures
        forest_max_height(kids) == {
            let h0 = tree_height(kids[0]);
            let hr = forest_max_height(kids.drop_first());
            if h0 > hr { h0 } else { hr }
        },
{
}

// ===========================================================================
// Structural well-formedness of the ghost tree (textbook B+tree invariants).
// Pure ghost — no arena. `cap`/`key_cap` are the layout's capacities, passed in
// from `bplus` so this module need not know the geometry.
// ===========================================================================

/// A `nat` sequence is strictly increasing.
pub open spec fn strictly_sorted(s: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> (#[trigger] s[i]) < (#[trigger] s[j])
}

/// Every key in the tree is `< bound` (used to state the cross-node ordering:
/// a child subtree's keys are bounded above by its right separator).
pub open spec fn keys_all_lt(t: Tree, bound: nat) -> bool {
    forall|i: int| 0 <= i < tree_keys(t).len() ==> (#[trigger] tree_keys(t)[i]) < bound
}

/// Every key in the tree is `>= bound` (bounded below by the left separator).
pub open spec fn keys_all_ge(t: Tree, bound: nat) -> bool {
    forall|i: int| 0 <= i < tree_keys(t).len() ==> bound <= (#[trigger] tree_keys(t)[i])
}

/// Structural well-formedness, height-indexed for balance. `tree_wf(t, h, cap,
/// key_cap, is_root)` holds when `t` is a valid B+tree of height exactly `h`:
///   - balance: every leaf is at depth `h` (a Leaf requires `h == 0`; an Inner
///     requires every child `wf` at height `h-1`);
///   - counts: leaf `keys.len() <= cap`; inner `seps.len() <= key_cap` and
///     `kids.len() == seps.len() + 1` (one more child than separators);
///     non-root nodes additionally `>= ceil(cap/2)` / `>= ceil(key_cap/2)`
///     (the B+tree balance lower bound; insert-only only ever establishes it);
///   - sortedness: leaf keys / inner separators strictly increasing;
///   - cross-node ordering: child `i`'s keys are `< seps[i]` (for `i < count`)
///     and `>= seps[i-1]` (for `i > 0`).
pub open spec fn tree_wf(t: Tree, h: nat, cap: nat, key_cap: nat, is_root: bool) -> bool
    decreases t
{
    match t {
        Tree::Leaf { keys, .. } => {
            &&& h == 0
            &&& keys.len() <= cap
            &&& strictly_sorted(keys)
            // root may underflow (even be empty); non-root leaves are >= ceil(cap/2)
            &&& (is_root || keys.len() >= (cap + 1) / 2)
        }
        Tree::Inner { seps, kids, .. } => {
            &&& h >= 1
            &&& seps.len() <= key_cap
            &&& kids.len() == seps.len() + 1
            &&& strictly_sorted(seps)
            &&& (is_root || seps.len() >= (key_cap + 1) / 2)
            // every child is a wf subtree of height h-1 (balance)
            &&& forest_wf(kids, (h - 1) as nat, cap, key_cap)
            // cross-node ordering: child i bounded by surrounding separators
            &&& (forall|i: int| 0 <= i < seps.len() ==>
                    keys_all_lt(#[trigger] kids[i], seps[i]))
            &&& (forall|i: int| 0 < i < kids.len() ==>
                    keys_all_ge(#[trigger] kids[i], seps[i - 1]))
        }
    }
}

/// Every tree in the forest is `wf` at height `h` (children are never the root).
pub open spec fn forest_wf(kids: Seq<Tree>, h: nat, cap: nat, key_cap: nat) -> bool
    decreases kids
{
    if kids.len() == 0 {
        true
    } else {
        &&& tree_wf(kids[0], h, cap, key_cap, false)
        &&& forest_wf(kids.drop_first(), h, cap, key_cap)
    }
}

pub proof fn lemma_forest_wf_cons(kids: Seq<Tree>, h: nat, cap: nat, key_cap: nat)
    requires kids.len() > 0,
    ensures
        forest_wf(kids, h, cap, key_cap) == (tree_wf(kids[0], h, cap, key_cap, false)
            && forest_wf(kids.drop_first(), h, cap, key_cap)),
{
}

// ===========================================================================
// Membership and the contains-descent lemmas. `contains(k)` decides
// `tree_keys(t).contains(k)`; these reduce that to the per-node search steps a
// root-to-leaf descent performs.
// ===========================================================================

/// Key membership in a tree's model (the spec `contains` decides).
pub open spec fn tree_contains(t: Tree, k: nat) -> bool {
    tree_keys(t).contains(k)
}

/// Leaf step. In a sorted leaf, `find_ge` lands at the first index `>= k`;
/// membership is exactly "that index is in range and holds `k`". This is the
/// spec justification for the exec leaf test `r < count && keys[r] == k`.
pub proof fn lemma_leaf_search_membership(keys: Seq<nat>, k: nat, r: int)
    requires
        strictly_sorted(keys),
        0 <= r <= keys.len(),
        forall|i: int| 0 <= i < r ==> keys[i] < k,
        forall|i: int| r <= i < keys.len() ==> k <= keys[i],
    ensures
        keys.contains(k) <==> (r < keys.len() && keys[r] == k),
{
    if r < keys.len() && keys[r] == k {
        assert(keys.contains(k));
    } else {
        // No element equals k: indices < r are < k, indices >= r are > k
        // (>= k and != k, using r's element if present).
        assert forall|i: int| 0 <= i < keys.len() implies keys[i] != k by {
            if i < r {
                // keys[i] < k
            } else {
                // i >= r: k <= keys[i]; if keys[i] == k then i == r contradicts
                // the else branch (strictly_sorted makes the first >= unique).
                if keys[i] == k {
                    // then keys[r] <= keys[i] == k <= keys[r] ⟹ keys[r] == k,
                    // and r < len, contradicting the else branch.
                    assert(r <= i);
                    assert(k <= keys[r]);   // r-arm of the hypothesis at i=r (if r<len)
                    assert(keys[r] <= keys[i]);  // sorted, r <= i
                }
            }
        }
        assert(!keys.contains(k));
    }
}

// ===========================================================================
// Sanity: a concrete two-level tree computes its views and is wf.
// ===========================================================================

#[cfg(verus_keep_ghost)]
proof fn sanity_single_leaf() {
    let t = Tree::Leaf { id: 0, keys: Seq::<nat>::empty() };
    assert(tree_keys(t) =~= Seq::<nat>::empty());
    assert(tree_ids(t) =~= set![0nat]);
    assert(tree_height(t) == 0);
    assert(strictly_sorted(Seq::<nat>::empty()));
    assert(tree_wf(t, 0, 14, 7, true));  // empty root leaf is wf
}

#[cfg(verus_keep_ghost)]
proof fn sanity_two_level() {
    let l0 = Tree::Leaf { id: 1, keys: seq![10nat, 20nat] };
    let l1 = Tree::Leaf { id: 2, keys: seq![30nat, 40nat] };
    let root = Tree::Inner { id: 0, seps: seq![30nat], kids: seq![l0, l1] };

    lemma_forest_keys_cons(seq![l0, l1]);
    assert(seq![l0, l1].drop_first() =~= seq![l1]);
    lemma_forest_keys_cons(seq![l1]);
    assert(seq![l1].drop_first() =~= Seq::<Tree>::empty());
    assert(tree_keys(l0) =~= seq![10nat, 20nat]);
    assert(tree_keys(root) =~= seq![10nat, 20nat, 30nat, 40nat]);

    lemma_forest_ids_cons(seq![l0, l1]);
    lemma_forest_ids_cons(seq![l1]);
    assert(tree_ids(root).contains(0nat));
    assert(tree_ids(root).contains(1nat));
    assert(tree_ids(root).contains(2nat));
}

} // verus!
