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

/// Inserting a fresh key `k` at its sorted position `pos` (the `find_ge`
/// landing) into a strictly-sorted sequence keeps it strictly sorted, and the
/// resulting key set is the old set plus `k`. The position is characterized by
/// `[0..pos) < k <= [pos..len)` and `k` absent. This is the leaf-insert
/// correctness step: `model' == model ∪ {k}`.
pub proof fn lemma_sorted_insert(keys: Seq<nat>, k: nat, pos: int)
    requires
        strictly_sorted(keys),
        0 <= pos <= keys.len(),
        forall|i: int| 0 <= i < pos ==> keys[i] < k,
        forall|i: int| pos <= i < keys.len() ==> k < keys[i],   // k fresh ⟹ strict
    ensures
        strictly_sorted(keys.insert(pos, k)),
        keys.insert(pos, k).to_set() == keys.to_set().insert(k),
{
    let r = keys.insert(pos, k);
    // strict sortedness of r: case-split each pair (i<j) on their relation to pos.
    assert forall|i: int, j: int| 0 <= i < j < r.len() implies r[i] < r[j] by {
        // r[m] == keys[m] for m < pos; r[pos] == k; r[m] == keys[m-1] for m > pos.
        if j < pos {
        } else if i < pos && j == pos {
        } else if i < pos && j > pos {
        } else if i == pos {
            // r[i] == k < keys[j-1] == r[j]  (j-1 >= pos)
        } else {
            // pos < i < j: keys[i-1] < keys[j-1]
        }
    }
    // set equality: r's elements are keys' elements plus k.
    assert(r.to_set() =~= keys.to_set().insert(k)) by {
        assert forall|x: nat| r.to_set().contains(x) <==> keys.to_set().insert(k).contains(x) by {
            // forward: every r element is k or a keys element (by index region).
            if r.to_set().contains(x) {
                let m = choose|m: int| 0 <= m < r.len() && r[m] == x;
                assert(0 <= m < r.len() && r[m] == x);
                if m < pos {
                    assert(keys[m] == x);
                    assert(keys.to_set().contains(x));
                } else if m == pos {
                    assert(x == k);
                } else {
                    assert(keys[m - 1] == x);
                    assert(keys.to_set().contains(x));
                }
            }
            // backward: k is r[pos]; a keys element keys[i] is r[i] or r[i+1].
            if keys.to_set().insert(k).contains(x) {
                if x == k {
                    assert(r[pos] == k);
                    assert(r.to_set().contains(x));
                } else {
                    let i = choose|i: int| 0 <= i < keys.len() && keys[i] == x;
                    assert(0 <= i < keys.len() && keys[i] == x);
                    if i < pos {
                        assert(r[i] == x);
                    } else {
                        assert(r[i + 1] == x);
                    }
                    assert(r.to_set().contains(x));
                }
            }
        }
    }
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
// Descent (the cross-node-ordering / clause-3 reduction). A root-to-leaf
// `contains`/`insert` descent picks, at each internal node, the child
// `cp = find_gt(seps, k)`; these lemmas justify that the search may follow that
// one child without losing `k`: `tree_contains(Inner, k) <==>
// tree_contains(kids[cp], k)`.
// ===========================================================================

/// Concatenation membership: `k` is in `a + b` iff it is in `a` or in `b`.
pub proof fn lemma_concat_contains<A>(a: Seq<A>, b: Seq<A>, k: A)
    ensures (a + b).contains(k) <==> a.contains(k) || b.contains(k),
{
    let c = a + b;
    if c.contains(k) {
        let i = choose|i: int| 0 <= i < c.len() && c[i] == k;
        if i < a.len() {
            assert(a[i] == k);
        } else {
            assert(b[i - a.len()] == k);
        }
    }
    if a.contains(k) {
        let i = choose|i: int| 0 <= i < a.len() && a[i] == k;
        assert(c[i] == k);
    }
    if b.contains(k) {
        let j = choose|j: int| 0 <= j < b.len() && b[j] == k;
        assert(c[a.len() + j] == k);
    }
}

/// Forest membership: a key is in the forest's in-order keys iff it is in some
/// child's keys. (The recursive companion of `lemma_concat_contains`.)
pub proof fn lemma_forest_keys_membership(kids: Seq<Tree>, k: nat)
    ensures
        forest_keys(kids).contains(k) <==> (exists|m: int|
            0 <= m < kids.len() && (#[trigger] tree_keys(kids[m])).contains(k)),
    decreases kids,
{
    if kids.len() == 0 {
        assert(forest_keys(kids) =~= Seq::<nat>::empty());
    } else {
        let df = kids.drop_first();
        lemma_forest_keys_cons(kids);
        lemma_concat_contains(tree_keys(kids[0]), forest_keys(df), k);
        lemma_forest_keys_membership(df, k);
        // df[m'] == kids[m' + 1]; bridge the existentials in both directions.
        assert forall|m2: int| 0 <= m2 < df.len() implies df[m2] == kids[m2 + 1] by {}
        if forest_keys(kids).contains(k) {
            if tree_keys(kids[0]).contains(k) {
                assert(tree_keys(kids[0]).contains(k));  // witness m == 0
            } else {
                let m2 = choose|m2: int| 0 <= m2 < df.len() && tree_keys(df[m2]).contains(k);
                assert(tree_keys(kids[m2 + 1]).contains(k));  // witness m == m2 + 1
            }
        }
        if exists|m: int| 0 <= m < kids.len() && tree_keys(kids[m]).contains(k) {
            let m = choose|m: int| 0 <= m < kids.len() && tree_keys(kids[m]).contains(k);
            if m == 0 {
            } else {
                assert(df[m - 1] == kids[m]);
                assert(tree_keys(df[m - 1]).contains(k));  // forest_keys(df) contains k
            }
        }
    }
}

/// `tree_wf` pins the height: a tree well-formed at height `h` has
/// `tree_height == h`. Lets a descent that knows a child is `wf` at `h-1`
/// conclude its `tree_height` is `h-1` (so the loop measure is the child's own
/// `tree_height`).
pub proof fn lemma_tree_wf_height(t: Tree, h: nat, cap: nat, key_cap: nat, is_root: bool)
    requires tree_wf(t, h, cap, key_cap, is_root),
    ensures tree_height(t) == h,
    decreases t,
{
    match t {
        Tree::Leaf { .. } => {}
        Tree::Inner { seps, kids, .. } => {
            lemma_forest_wf_height(kids, (h - 1) as nat, cap, key_cap);
        }
    }
}

/// Forest companion: a non-empty forest `wf` at height `h` has
/// `forest_max_height == h` (balance — every child is at the same height).
pub proof fn lemma_forest_wf_height(kids: Seq<Tree>, h: nat, cap: nat, key_cap: nat)
    requires forest_wf(kids, h, cap, key_cap), kids.len() > 0,
    ensures forest_max_height(kids) == h,
    decreases kids,
{
    lemma_forest_wf_cons(kids, h, cap, key_cap);
    lemma_forest_max_height_cons(kids);
    lemma_tree_wf_height(kids[0], h, cap, key_cap, false);
    let df = kids.drop_first();
    if df.len() > 0 {
        lemma_forest_wf_height(df, h, cap, key_cap);
    }
}

/// A child's height is at most the forest max (so a descent into child `m`
/// strictly decreases `tree_height` of an `Inner` node, `1 + forest_max`). The
/// descent loop's `decreases` measure.
pub proof fn lemma_forest_max_height_at(kids: Seq<Tree>, m: int)
    requires 0 <= m < kids.len(),
    ensures tree_height(kids[m]) <= forest_max_height(kids),
    decreases kids,
{
    lemma_forest_max_height_cons(kids);
    if m == 0 {
    } else {
        let df = kids.drop_first();
        assert(df[m - 1] == kids[m]);
        lemma_forest_max_height_at(df, m - 1);
    }
}

/// Project `forest_wf` to one child: every child is `wf` at the forest height
/// (non-root). The arena descent needs the specific child it follows.
pub proof fn lemma_forest_wf_at(kids: Seq<Tree>, h: nat, cap: nat, key_cap: nat, m: int)
    requires
        forest_wf(kids, h, cap, key_cap),
        0 <= m < kids.len(),
    ensures
        tree_wf(kids[m], h, cap, key_cap, false),
    decreases kids,
{
    lemma_forest_wf_cons(kids, h, cap, key_cap);
    if m == 0 {
    } else {
        let df = kids.drop_first();
        assert(df[m - 1] == kids[m]);
        lemma_forest_wf_at(df, h, cap, key_cap, m - 1);
    }
}

/// A non-root-wf tree is also root-wf (the root form only drops the minimum-
/// occupancy lower bound; everything else is shared). Lets the descent carry a
/// single root-form `tree_wf` while stepping into children, which bind at the
/// stronger non-root form.
pub proof fn lemma_tree_wf_relax_root(t: Tree, h: nat, cap: nat, key_cap: nat)
    requires tree_wf(t, h, cap, key_cap, false),
    ensures tree_wf(t, h, cap, key_cap, true),
{
    match t {
        Tree::Leaf { .. } => {}
        Tree::Inner { .. } => {}
    }
}

/// Descent step. In a wf internal node, if `cp` is the `find_gt` position over
/// the separators (`seps[i] <= k` for `i < cp`, `k < seps[i]` for `i >= cp`),
/// then `k` is in the node's key space iff it is in child `cp` — so a search may
/// follow that one child. `cp` is a valid child index (`cp < kids.len()`).
pub proof fn lemma_descent_step(
    id: nat,
    seps: Seq<nat>,
    kids: Seq<Tree>,
    k: nat,
    cp: int,
    h: nat,
    cap: nat,
    key_cap: nat,
    is_root: bool,
)
    requires
        tree_wf(Tree::Inner { id, seps, kids }, h, cap, key_cap, is_root),
        0 <= cp <= seps.len(),
        forall|i: int| 0 <= i < cp ==> seps[i] <= k,
        forall|i: int| cp <= i < seps.len() ==> k < seps[i],
    ensures
        cp < kids.len(),
        tree_contains(Tree::Inner { id, seps, kids }, k) <==> tree_contains(kids[cp], k),
{
    let t = Tree::Inner { id, seps, kids };
    // tree_wf Inner arm: kids.len() == seps.len() + 1, so cp <= seps.len() < kids.len().
    assert(kids.len() == seps.len() + 1);
    assert(tree_keys(t) == forest_keys(kids));
    lemma_forest_keys_membership(kids, k);
    if tree_contains(t, k) {
        // k in forest ⟹ k in some kids[m]; show m == cp via cross-node ordering.
        let m = choose|m: int| 0 <= m < kids.len() && tree_keys(kids[m]).contains(k);
        if m < cp {
            // keys_all_lt(kids[m], seps[m]): k < seps[m] <= k, contradiction.
            let j = choose|j: int| 0 <= j < tree_keys(kids[m]).len() && tree_keys(kids[m])[j] == k;
            assert(keys_all_lt(kids[m], seps[m]));
            assert(tree_keys(kids[m])[j] < seps[m]);
            assert(seps[m] <= k);
            assert(false);
        } else if m > cp {
            // keys_all_ge(kids[m], seps[m-1]): k >= seps[m-1] > k, contradiction.
            let j = choose|j: int| 0 <= j < tree_keys(kids[m]).len() && tree_keys(kids[m])[j] == k;
            assert(keys_all_ge(kids[m], seps[m - 1]));
            assert(seps[m - 1] <= tree_keys(kids[m])[j]);
            assert(k < seps[m - 1]);
            assert(false);
        }
        assert(m == cp);
    }
    if tree_contains(kids[cp], k) {
        assert(tree_keys(kids[cp]).contains(k));  // witness m == cp for forest membership
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
