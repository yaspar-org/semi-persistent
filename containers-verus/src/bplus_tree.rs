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

/// The leaf-id offset where child `m` begins in `forest_leaf_ids(kids)`: the
/// summed leaf counts of the children before `m`.
pub open spec fn leaf_id_offset(kids: Seq<Tree>, m: int) -> nat
    decreases m
{
    if m <= 0 {
        0
    } else {
        leaf_id_offset(kids, m - 1) + tree_leaf_ids(kids[m - 1]).len()
    }
}

/// Child `m`'s leaf ids occupy the contiguous slice `[off, off + len)` of the
/// forest's leaf ids, where `off = leaf_id_offset(kids, m)`. So a property of
/// `forest_leaf_ids` at those positions projects to `tree_leaf_ids(kids[m])`.
/// The inverse of the concatenation, needed to decompose a parent's leaf-link
/// chain to one child's.
pub proof fn lemma_forest_leaf_ids_slice(kids: Seq<Tree>, m: int)
    requires 0 <= m < kids.len(),
    ensures
        leaf_id_offset(kids, m) + tree_leaf_ids(kids[m]).len() <= forest_leaf_ids(kids).len(),
        forall|q: int| 0 <= q < tree_leaf_ids(kids[m]).len() ==>
            (#[trigger] forest_leaf_ids(kids)[leaf_id_offset(kids, m) + q]) == tree_leaf_ids(kids[m])[q],
    decreases m,
{
    lemma_forest_leaf_ids_cons(kids);
    let head = tree_leaf_ids(kids[0]);
    let df = kids.drop_first();
    if m == 0 {
        // offset 0; forest_leaf_ids(kids) == head + forest_leaf_ids(df).
        assert(leaf_id_offset(kids, 0) == 0);
        assert forall|q: int| 0 <= q < tree_leaf_ids(kids[0]).len() implies
            forest_leaf_ids(kids)[0 + q] == tree_leaf_ids(kids[0])[q] by {
            assert(forest_leaf_ids(kids)[q] == head[q]);
        }
    } else {
        assert(df[m - 1] == kids[m]);
        lemma_forest_leaf_ids_slice(df, m - 1);
        // offset(kids, m) == head.len() + offset(df, m-1) (peel one child).
        lemma_leaf_id_offset_cons(kids, m);
        let offd = leaf_id_offset(df, m - 1);
        assert forall|q: int| 0 <= q < tree_leaf_ids(kids[m]).len() implies
            forest_leaf_ids(kids)[leaf_id_offset(kids, m) + q] == tree_leaf_ids(kids[m])[q] by {
            // forest_leaf_ids(kids)[head.len() + i] == forest_leaf_ids(df)[i].
            assert(forest_leaf_ids(kids)[head.len() + (offd + q)] == forest_leaf_ids(df)[offd + q]);
            assert(forest_leaf_ids(df)[offd + q] == tree_leaf_ids(df[m - 1])[q]);
        }
    }
}

/// `leaf_id_offset(kids, m) == tree_leaf_ids(kids[0]).len() + leaf_id_offset(
/// kids.drop_first(), m-1)` for `m >= 1`. The peel-one-child identity.
pub proof fn lemma_leaf_id_offset_cons(kids: Seq<Tree>, m: int)
    requires 1 <= m < kids.len(),
    ensures
        leaf_id_offset(kids, m)
            == tree_leaf_ids(kids[0]).len() + leaf_id_offset(kids.drop_first(), m - 1),
    decreases m,
{
    let df = kids.drop_first();
    reveal_with_fuel(leaf_id_offset, 2);
    if m == 1 {
        assert(leaf_id_offset(df, 0) == 0);
        // leaf_id_offset(kids,1) == leaf_id_offset(kids,0) + tlids(kids[0]).len()
        //                        == 0 + head.len().
    } else {
        // IH: leaf_id_offset(kids,m-1) == head.len() + leaf_id_offset(df,m-2).
        lemma_leaf_id_offset_cons(kids, m - 1);
        assert(df[m - 2] == kids[m - 1]);
        // LHS one-step unfold (m >= 1): offset(kids,m) == offset(kids,m-1) + tlids(kids[m-1]).len().
        assert(leaf_id_offset(kids, m)
            == leaf_id_offset(kids, m - 1) + tree_leaf_ids(kids[m - 1]).len());
        // RHS one-step unfold (m-1 >= 1): offset(df,m-1) == offset(df,m-2) + tlids(df[m-2]).len().
        assert(leaf_id_offset(df, m - 1)
            == leaf_id_offset(df, m - 2) + tree_leaf_ids(df[m - 2]).len());
    }
}

/// `leaf_id_offset(kids, cp+1) == leaf_id_offset(kids, cp) +
/// tree_leaf_ids(kids[cp]).len()` (the offset advances by the child's leaf
/// count). Definitional, but stated for use in the leaf-links projection.
pub proof fn lemma_leaf_id_offset_succ(kids: Seq<Tree>, cp: int)
    requires 0 <= cp,
    ensures leaf_id_offset(kids, cp + 1) == leaf_id_offset(kids, cp) + tree_leaf_ids(kids[cp]).len(),
{
}

/// The last child's slice reaches the end: `leaf_id_offset(kids, len-1) +
/// tree_leaf_ids(kids[len-1]).len() == forest_leaf_ids(kids).len()`.
pub proof fn lemma_leaf_id_offset_last(kids: Seq<Tree>, cp: int)
    requires 0 <= cp < kids.len(), cp + 1 == kids.len(),
    ensures leaf_id_offset(kids, cp) + tree_leaf_ids(kids[cp]).len() == forest_leaf_ids(kids).len(),
    decreases kids,
{
    lemma_forest_leaf_ids_cons(kids);
    let df = kids.drop_first();
    if cp == 0 {
        // single child: offset 0, forest_leaf_ids == tree_leaf_ids(kids[0]) + [].
        assert(df.len() == 0);
        assert(forest_leaf_ids(df) =~= Seq::<nat>::empty());
    } else {
        assert(df[cp - 1] == kids[cp]);
        assert(cp == df.len());
        lemma_leaf_id_offset_last(df, cp - 1);
        lemma_leaf_id_offset_cons(kids, cp);
    }
}

/// Updating child `m` to a subtree with the same in-order leaf ids preserves the
/// forest's in-order leaf ids. (Absorb keeps the child's leaf sequence — the
/// leaf base case adds keys not leaves; the internal absorb's recursion preserves
/// the leaf-id seq by its own ensures.)
pub proof fn lemma_forest_leaf_ids_update(kids: Seq<Tree>, m: int, nc: Tree)
    requires
        0 <= m < kids.len(),
        tree_leaf_ids(nc) == tree_leaf_ids(kids[m]),
    ensures
        forest_leaf_ids(kids.update(m, nc)) == forest_leaf_ids(kids),
    decreases kids,
{
    lemma_forest_leaf_ids_cons(kids);
    let u = kids.update(m, nc);
    lemma_forest_leaf_ids_cons(u);
    if m == 0 {
        assert(u[0] == nc);
        assert(u.drop_first() =~= kids.drop_first());
    } else {
        let df = kids.drop_first();
        assert(u[0] == kids[0]);
        assert(u.drop_first() =~= df.update(m - 1, nc));
        assert(df[m - 1] == kids[m]);
        lemma_forest_leaf_ids_update(df, m - 1, nc);
    }
}

/// An internal node's own id is not in any child's footprint (`tree_disjoint`'s
/// first clause). So a mutation confined to a child's region leaves the parent
/// node's arena slot untouched.
pub proof fn lemma_node_id_not_in_child(t: Tree, cp: int)
    requires
        t is Inner,
        tree_disjoint(t),
        0 <= cp < t->Inner_kids.len(),
    ensures
        !tree_ids(t->Inner_kids[cp]).contains(t->Inner_id),
{
    let id = t->Inner_id;
    let kids = t->Inner_kids;
    // tree_disjoint(Inner): !forest_ids(kids).contains(id). tree_ids(kids[cp]) ⊆
    // forest_ids(kids), so id not in tree_ids(kids[cp]).
    if tree_ids(kids[cp]).contains(id) {
        lemma_child_ids_in_forest(kids, cp, id);
        assert(forest_ids(kids).contains(id));
        assert(false);
    }
}

/// `tree_ids(kids[m]) ⊆ forest_ids(kids)` at a point: if `id ∈ tree_ids(kids[m])`
/// then `id ∈ forest_ids(kids)`.
pub proof fn lemma_child_ids_in_forest(kids: Seq<Tree>, m: int, id: nat)
    requires 0 <= m < kids.len(), tree_ids(kids[m]).contains(id),
    ensures forest_ids(kids).contains(id),
    decreases kids,
{
    lemma_forest_ids_cons(kids);
    if m == 0 {
    } else {
        let df = kids.drop_first();
        assert(df[m - 1] == kids[m]);
        lemma_child_ids_in_forest(df, m - 1, id);
    }
}

/// Membership in a forest footprint comes from some child: `forest_ids(kids)
/// .contains(id) ==> exists m. tree_ids(kids[m]).contains(id)`. The reverse of
/// the union definition; needed to derive pairwise facts from `forest_ids`.
pub proof fn lemma_forest_id_in_some_child(kids: Seq<Tree>, id: nat)
    requires forest_ids(kids).contains(id),
    ensures exists|m: int| 0 <= m < kids.len() && (#[trigger] tree_ids(kids[m])).contains(id),
    decreases kids,
{
    lemma_forest_ids_cons(kids);
    if tree_ids(kids[0]).contains(id) {
        assert(tree_ids(kids[0]).contains(id));  // witness m == 0
    } else {
        let df = kids.drop_first();
        assert(forest_ids(df).contains(id));
        lemma_forest_id_in_some_child(df, id);
        let m = choose|m: int| 0 <= m < df.len() && tree_ids(df[m]).contains(id);
        assert(df[m] == kids[m + 1]);
        assert(tree_ids(kids[m + 1]).contains(id));  // witness m + 1
    }
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

/// `keys_all_lt` via membership: it holds iff every key in the model set is `<
/// bound`. The index form and the set form coincide; this bridge lets the absorb
/// step argue over `to_set()` (where the new child's keys are old ∪ {key}).
pub proof fn lemma_keys_all_lt_set(t: Tree, bound: nat)
    ensures keys_all_lt(t, bound) == (forall|k: nat| tree_keys(t).to_set().contains(k) ==> k < bound),
{
    if keys_all_lt(t, bound) {
        assert forall|k: nat| tree_keys(t).to_set().contains(k) implies k < bound by {
            let i = choose|i: int| 0 <= i < tree_keys(t).len() && tree_keys(t)[i] == k;
        }
    }
    if forall|k: nat| tree_keys(t).to_set().contains(k) ==> k < bound {
        assert forall|i: int| 0 <= i < tree_keys(t).len() implies (#[trigger] tree_keys(t)[i]) < bound by {
            assert(tree_keys(t).to_set().contains(tree_keys(t)[i]));
        }
    }
}

/// Companion set bridge for `keys_all_ge`.
pub proof fn lemma_keys_all_ge_set(t: Tree, bound: nat)
    ensures keys_all_ge(t, bound) == (forall|k: nat| tree_keys(t).to_set().contains(k) ==> bound <= k),
{
    if keys_all_ge(t, bound) {
        assert forall|k: nat| tree_keys(t).to_set().contains(k) implies bound <= k by {
            let i = choose|i: int| 0 <= i < tree_keys(t).len() && tree_keys(t)[i] == k;
        }
    }
    if forall|k: nat| tree_keys(t).to_set().contains(k) ==> bound <= k {
        assert forall|i: int| 0 <= i < tree_keys(t).len() implies bound <= (#[trigger] tree_keys(t)[i]) by {
            assert(tree_keys(t).to_set().contains(tree_keys(t)[i]));
        }
    }
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
            // Non-root internal minimum: `ceil(child_cap/2)` children, i.e.
            // `key_cap / 2` separators (floor). A split's left half has exactly
            // `key_cap / 2` separators, so this is the tight bound it meets;
            // `(key_cap + 1) / 2` (ceil) would be too strong for odd `key_cap`
            // (Layout64U32, key_cap = 7: a split gives 3 separators, ceil wants
            // 4). Insert-only ever *establishes* this; deletion (which would
            // consume it) is out of scope.
            &&& (is_root || seps.len() >= key_cap / 2)
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

/// Replace child `m` by a new subtree `nc` that is itself `wf` at height `h`:
/// the forest stays `wf`. The internal-node *absorb* step (a child that did not
/// split returns an updated subtree at the same position).
pub proof fn lemma_forest_wf_update(kids: Seq<Tree>, h: nat, cap: nat, key_cap: nat, m: int, nc: Tree)
    requires
        forest_wf(kids, h, cap, key_cap),
        0 <= m < kids.len(),
        tree_wf(nc, h, cap, key_cap, false),
    ensures
        forest_wf(kids.update(m, nc), h, cap, key_cap),
    decreases kids,
{
    lemma_forest_wf_cons(kids, h, cap, key_cap);
    let u = kids.update(m, nc);
    if m == 0 {
        assert(u[0] == nc);
        assert(u.drop_first() =~= kids.drop_first());
        lemma_forest_wf_cons(u, h, cap, key_cap);
    } else {
        assert(u[0] == kids[0]);
        assert(u.drop_first() =~= kids.drop_first().update(m - 1, nc));
        lemma_forest_wf_update(kids.drop_first(), h, cap, key_cap, m - 1, nc);
        lemma_forest_wf_cons(u, h, cap, key_cap);
    }
}

/// Updating child `m` to a subtree with the *same root id* and the *same id
/// footprint* preserves the forest's id set and disjointness. The absorb step's
/// new subtree keeps the child's arena slot (id unchanged) and allocates no new
/// nodes that escape the old footprint, so `tree_ids(nc) == tree_ids(kids[m])`.
pub proof fn lemma_forest_disjoint_update(kids: Seq<Tree>, m: int, nc: Tree)
    requires
        forest_disjoint(kids),
        0 <= m < kids.len(),
        tree_disjoint(nc),
        tree_ids(nc) == tree_ids(kids[m]),
        (forall|i: int| 0 <= i < kids.len() && i != m ==>
            (#[trigger] tree_ids(kids[i])).disjoint(tree_ids(kids[m]))),
    ensures
        forest_disjoint(kids.update(m, nc)),
        forest_ids(kids.update(m, nc)) == forest_ids(kids),
    decreases kids,
{
    lemma_forest_disjoint_cons(kids);
    lemma_forest_ids_cons(kids);
    let u = kids.update(m, nc);
    lemma_forest_disjoint_cons(u);
    lemma_forest_ids_cons(u);
    if m == 0 {
        assert(u[0] == nc);
        assert(u.drop_first() =~= kids.drop_first());
        assert(tree_ids(u[0]) == tree_ids(kids[0]));
    } else {
        let df = kids.drop_first();
        assert(u[0] == kids[0]);
        assert(u.drop_first() =~= df.update(m - 1, nc));
        assert(df[m - 1] == kids[m]);
        assert forall|i: int| 0 <= i < df.len() && i != m - 1 implies
            (#[trigger] tree_ids(df[i])).disjoint(tree_ids(df[m - 1])) by {
            assert(df[i] == kids[i + 1]);
        }
        lemma_forest_disjoint_update(df, m - 1, nc);
    }
}

/// Updating child `m` to a subtree with the same in-order keys preserves the
/// forest's in-order keys. (The absorb step changes one child's keys; this is
/// used with the child's *new* keys, so the caller supplies the per-child key
/// relation; here we state the structural `update`-splits-`forest_keys` fact.)
pub proof fn lemma_forest_keys_update(kids: Seq<Tree>, m: int, nc: Tree)
    requires 0 <= m < kids.len(),
    ensures
        forest_keys(kids.update(m, nc))
            == forest_keys(kids.subrange(0, m)) + tree_keys(nc)
                + forest_keys(kids.subrange(m + 1, kids.len() as int)),
{
    let u = kids.update(m, nc);
    // u == kids[0..m] + [nc] + kids[m+1..]; forest_keys splits at m and m+1.
    lemma_forest_keys_split(u, m);
    lemma_forest_keys_split(u.subrange(m, u.len() as int), 1);
    assert(u.subrange(0, m) =~= kids.subrange(0, m));
    assert(u.subrange(m, u.len() as int).subrange(0, 1) =~= seq![nc]);
    assert(u.subrange(m, u.len() as int).subrange(1, u.subrange(m, u.len() as int).len() as int)
        =~= kids.subrange(m + 1, kids.len() as int));
    lemma_forest_keys_cons(seq![nc]);
    assert(seq![nc].drop_first() =~= Seq::<Tree>::empty());
}

/// A contiguous subrange `[lo, hi)` of a wf forest is itself a wf forest. The
/// internal split carves the children into two subranges, each of which must be
/// a wf forest for the two halves to be wf.
/// `forest_wf` is preserved by concatenation: if `a` and `b` are both wf
/// forests at height `h`, so is `a + b`. (The split-child reconstruction builds
/// the new children as `left ++ [ncl, ncr] ++ right`.)
pub proof fn lemma_forest_wf_concat(a: Seq<Tree>, b: Seq<Tree>, h: nat, cap: nat, key_cap: nat)
    requires forest_wf(a, h, cap, key_cap), forest_wf(b, h, cap, key_cap),
    ensures forest_wf(a + b, h, cap, key_cap),
    decreases a,
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        lemma_forest_wf_cons(a, h, cap, key_cap);
        let adf = a.drop_first();
        lemma_forest_wf_concat(adf, b, h, cap, key_cap);
        assert((a + b).drop_first() =~= adf + b);
        assert((a + b)[0] == a[0]);
        lemma_forest_wf_cons(a + b, h, cap, key_cap);
    }
}

pub proof fn lemma_forest_wf_subrange(kids: Seq<Tree>, h: nat, cap: nat, key_cap: nat, lo: int, hi: int)
    requires
        forest_wf(kids, h, cap, key_cap),
        0 <= lo <= hi <= kids.len(),
    ensures
        forest_wf(kids.subrange(lo, hi), h, cap, key_cap),
    decreases hi - lo,
{
    let sub = kids.subrange(lo, hi);
    if lo == hi {
        assert(sub.len() == 0);
    } else {
        lemma_forest_wf_at(kids, h, cap, key_cap, lo);
        assert(sub[0] == kids[lo]);
        lemma_forest_wf_subrange(kids, h, cap, key_cap, lo + 1, hi);
        assert(sub.drop_first() =~= kids.subrange(lo + 1, hi));
        lemma_forest_wf_cons(sub, h, cap, key_cap);
    }
}

/// Every child's height is `<= forest_max_height(kids)`, so a subrange's max
/// height is too: `forest_max_height(kids.subrange(lo,hi)) <= forest_max_height(kids)`.
/// Lets the split halves' heights be bounded by the parent's child height.
pub proof fn lemma_forest_max_height_subrange(kids: Seq<Tree>, lo: int, hi: int)
    requires 0 <= lo <= hi <= kids.len(),
    ensures forest_max_height(kids.subrange(lo, hi)) <= forest_max_height(kids),
    decreases hi - lo,
{
    let sub = kids.subrange(lo, hi);
    if lo == hi {
        assert(sub.len() == 0);
    } else {
        lemma_forest_max_height_cons(sub);
        assert(sub[0] == kids[lo]);
        assert(sub.drop_first() =~= kids.subrange(lo + 1, hi));
        lemma_forest_max_height_at(kids, lo);          // height(kids[lo]) <= max(kids)
        lemma_forest_max_height_subrange(kids, lo + 1, hi);
    }
}

/// If every child in a forest is `wf` at height `h`, then `forest_max_height <=
/// h` (each child has `tree_height <= h`). Combined with the subrange lemma this
/// pins a split half's height.
pub proof fn lemma_forest_wf_max_height(kids: Seq<Tree>, h: nat, cap: nat, key_cap: nat)
    requires forest_wf(kids, h, cap, key_cap),
    ensures forest_max_height(kids) <= h,
    decreases kids,
{
    if kids.len() == 0 {
    } else {
        lemma_forest_wf_cons(kids, h, cap, key_cap);
        lemma_forest_max_height_cons(kids);
        lemma_tree_wf_height(kids[0], h, cap, key_cap, false);  // height(kids[0]) == h
        lemma_forest_wf_max_height(kids.drop_first(), h, cap, key_cap);
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
// Disjointness (the dynamic-frames separation clause). No arena id repeats
// within the tree: an internal node's own id is outside every child's
// footprint, and distinct children have disjoint footprints. This is what makes
// "this subtree" a well-defined region a descent-based split can mutate while
// framing out every other subtree (via `bplus::lemma_binds_frame`).
// ===========================================================================

/// No id repeats anywhere in `t`. Leaf: trivially true. Inner: the node's id is
/// not in any child's footprint, the children's footprints are pairwise
/// disjoint, and each child is itself disjoint.
pub open spec fn tree_disjoint(t: Tree) -> bool
    decreases t
{
    match t {
        Tree::Leaf { .. } => true,
        Tree::Inner { id, kids, .. } => {
            &&& !forest_ids(kids).contains(id)
            &&& forest_disjoint(kids)
            &&& (forall|i: int, j: int| 0 <= i < j < kids.len() ==>
                    (#[trigger] tree_ids(kids[i])).disjoint(#[trigger] tree_ids(kids[j])))
        }
    }
}

pub open spec fn forest_disjoint(kids: Seq<Tree>) -> bool
    decreases kids
{
    if kids.len() == 0 {
        true
    } else {
        tree_disjoint(kids[0]) && forest_disjoint(kids.drop_first())
    }
}

pub proof fn lemma_forest_disjoint_cons(kids: Seq<Tree>)
    requires kids.len() > 0,
    ensures forest_disjoint(kids) == (tree_disjoint(kids[0]) && forest_disjoint(kids.drop_first())),
{
}

/// Project `forest_disjoint` to one child.
pub proof fn lemma_forest_disjoint_at(kids: Seq<Tree>, m: int)
    requires forest_disjoint(kids), 0 <= m < kids.len(),
    ensures tree_disjoint(kids[m]),
    decreases kids,
{
    lemma_forest_disjoint_cons(kids);
    if m == 0 {
    } else {
        let df = kids.drop_first();
        assert(df[m - 1] == kids[m]);
        lemma_forest_disjoint_at(df, m - 1);
    }
}

// ===========================================================================
// Leaf-id order (clause 5 support). `tree_leaf_ids(t)` is the in-order
// (left-to-right) sequence of leaf arena ids. The executable leaf `link`
// pointers are *bound* to this sequence (see `bplus::leaf_links_ok`): walking
// `link` from the leftmost leaf visits ids in exactly this order, NIL-
// terminated. This backs the incremental sorted cursor (leapfrog join). No
// second independent view: the links realize the tree's own in-order leaf order.
// ===========================================================================

/// In-order sequence of leaf arena ids. A leaf contributes its own id; an
/// internal node concatenates its children's leaf-id sequences left to right.
pub open spec fn tree_leaf_ids(t: Tree) -> Seq<nat>
    decreases t
{
    match t {
        Tree::Leaf { id, .. } => seq![id],
        Tree::Inner { kids, .. } => forest_leaf_ids(kids),
    }
}

pub open spec fn forest_leaf_ids(kids: Seq<Tree>) -> Seq<nat>
    decreases kids
{
    if kids.len() == 0 {
        Seq::empty()
    } else {
        tree_leaf_ids(kids[0]) + forest_leaf_ids(kids.drop_first())
    }
}

pub proof fn lemma_forest_leaf_ids_cons(kids: Seq<Tree>)
    requires kids.len() > 0,
    ensures forest_leaf_ids(kids) == tree_leaf_ids(kids[0]) + forest_leaf_ids(kids.drop_first()),
{
}

/// Every in-order leaf id is in the tree's footprint: `tree_leaf_ids(t)[p] ∈
/// tree_ids(t)`. So a frame agreeing on `tree_ids(t)` agrees on every leaf-link
/// slot — the basis of the leaf-link frame lemma.
pub proof fn lemma_leaf_id_in_tree_ids(t: Tree, p: int)
    requires 0 <= p < tree_leaf_ids(t).len(),
    ensures tree_ids(t).contains(tree_leaf_ids(t)[p]),
    decreases t,
{
    match t {
        Tree::Leaf { id, .. } => {
            // tree_leaf_ids(Leaf) == [id], tree_ids(Leaf) == {id}.
        }
        Tree::Inner { id, kids, .. } => {
            // tree_leaf_ids(Inner) == forest_leaf_ids(kids); find the child.
            lemma_forest_leaf_id_in_forest_ids(kids, p);
            assert(forest_ids(kids).subset_of(tree_ids(t)));
        }
    }
}

/// Forest companion: `forest_leaf_ids(kids)[p] ∈ forest_ids(kids)`.
pub proof fn lemma_forest_leaf_id_in_forest_ids(kids: Seq<Tree>, p: int)
    requires 0 <= p < forest_leaf_ids(kids).len(),
    ensures forest_ids(kids).contains(forest_leaf_ids(kids)[p]),
    decreases kids,
{
    lemma_forest_leaf_ids_cons(kids);
    lemma_forest_ids_cons(kids);
    let head = tree_leaf_ids(kids[0]);
    if p < head.len() {
        // leaf id comes from kids[0]: in tree_ids(kids[0]) ⊆ forest_ids(kids).
        lemma_leaf_id_in_tree_ids(kids[0], p);
        assert(forest_leaf_ids(kids)[p] == head[p]);
    } else {
        let df = kids.drop_first();
        assert(forest_leaf_ids(kids)[p] == forest_leaf_ids(df)[p - head.len()]);
        lemma_forest_leaf_id_in_forest_ids(df, p - head.len());
    }
}

/// The in-order leaf-id sequence is non-empty for any tree (a leaf has one id;
/// an internal node has `kids.len() >= 1` under `tree_wf`, and the head child
/// contributes at least one). Lets the cursor/link clause name a first leaf.
pub proof fn lemma_tree_leaf_ids_nonempty(t: Tree, h: nat, cap: nat, key_cap: nat, is_root: bool)
    requires tree_wf(t, h, cap, key_cap, is_root),
    ensures tree_leaf_ids(t).len() >= 1,
    decreases t,
{
    match t {
        Tree::Leaf { .. } => {}
        Tree::Inner { seps, kids, .. } => {
            // kids.len() == seps.len() + 1 >= 1; head child is wf at h-1.
            lemma_forest_leaf_ids_cons(kids);
            lemma_forest_wf_cons(kids, (h - 1) as nat, cap, key_cap);
            lemma_tree_leaf_ids_nonempty(kids[0], (h - 1) as nat, cap, key_cap, false);
        }
    }
}

// ===========================================================================
// Median split (the leaf-split key redistribution, as a pure Seq fact). The
// full leaf's keys plus the inserted key form a strictly sorted `combined` of
// length `cap + 1`; splitting at `mid` gives a left prefix and right suffix that
// recombine to `combined`, each strictly sorted, with `right[0]` a true B+tree
// separator (every left key `<`, every right key `>=` it). De-risked in a
// standalone probe before lifting here.
// ===========================================================================

pub proof fn lemma_median_split(combined: Seq<nat>, mid: int)
    requires
        strictly_sorted(combined),
        0 < mid < combined.len(),
    ensures
        ({
            let left = combined.subrange(0, mid);
            let right = combined.subrange(mid, combined.len() as int);
            &&& strictly_sorted(left)
            &&& strictly_sorted(right)
            &&& left + right == combined
            &&& left.len() == mid
            &&& right.len() == combined.len() - mid
            &&& (forall|i: int| 0 <= i < left.len() ==> #[trigger] left[i] < right[0])
            &&& (forall|i: int| 0 <= i < right.len() ==> right[0] <= #[trigger] right[i])
        }),
{
    let left = combined.subrange(0, mid);
    let right = combined.subrange(mid, combined.len() as int);
    assert(left + right =~= combined);
    assert forall|i: int, j: int| 0 <= i < j < left.len() implies #[trigger] left[i] < #[trigger] left[j] by {
        assert(left[i] == combined[i]);
        assert(left[j] == combined[j]);
    }
    assert forall|i: int, j: int| 0 <= i < j < right.len() implies #[trigger] right[i] < #[trigger] right[j] by {
        assert(right[i] == combined[mid + i]);
        assert(right[j] == combined[mid + j]);
    }
    assert forall|i: int| 0 <= i < left.len() implies #[trigger] left[i] < right[0] by {
        assert(left[i] == combined[i]);
        assert(right[0] == combined[mid]);
    }
    assert forall|i: int| 0 <= i < right.len() implies right[0] <= #[trigger] right[i] by {
        assert(right[i] == combined[mid + i]);
        assert(right[0] == combined[mid]);
    }
}

// ===========================================================================
// Leaf-split tree reconstruction. After splitting a full root leaf into two
// sorted leaves with separator `right_keys[0]`, the new height-1 root
// `Inner{ new_root_id, [sep], [left_leaf, right_leaf] }` is a wf B+tree whose
// in-order keys are `left_keys + right_keys`. Isolates the structural B+tree
// reasoning (balance, ordering, occupancy) from the arena plumbing in `insert`.
// ===========================================================================

pub proof fn lemma_split_tree_wf(
    new_root_id: nat,
    lid: nat,
    rid: nat,
    left_keys: Seq<nat>,
    right_keys: Seq<nat>,
    cap: nat,
    key_cap: nat,
)
    requires
        strictly_sorted(left_keys),
        strictly_sorted(right_keys),
        right_keys.len() >= 1,
        left_keys.len() == (cap + 1) / 2,
        right_keys.len() == (cap + 1 - (cap + 1) / 2) as nat,
        cap >= 1,
        key_cap >= 1,
        forall|i: int| 0 <= i < left_keys.len() ==> #[trigger] left_keys[i] < right_keys[0],
        forall|i: int| 0 <= i < right_keys.len() ==> right_keys[0] <= #[trigger] right_keys[i],
    ensures
        ({
            let lt = Tree::Leaf { id: lid, keys: left_keys };
            let rt = Tree::Leaf { id: rid, keys: right_keys };
            let root = Tree::Inner { id: new_root_id, seps: seq![right_keys[0]], kids: seq![lt, rt] };
            &&& tree_wf(root, 1, cap, key_cap, true)
            &&& tree_height(root) == 1
            &&& tree_keys(root) == left_keys + right_keys
        }),
{
    let lt = Tree::Leaf { id: lid, keys: left_keys };
    let rt = Tree::Leaf { id: rid, keys: right_keys };
    let kids = seq![lt, rt];
    let root = Tree::Inner { id: new_root_id, seps: seq![right_keys[0]], kids };

    // occupancy: left == (cap+1)/2; right == cap+1-(cap+1)/2 >= (cap+1)/2 (floor).
    assert(left_keys.len() <= cap);
    assert(right_keys.len() <= cap);
    assert(left_keys.len() >= (cap + 1) / 2);
    assert(right_keys.len() >= (cap + 1) / 2);

    // both children wf at height 0 (non-root): sorted, count bounds, occupancy.
    assert(tree_wf(lt, 0, cap, key_cap, false));
    assert(tree_wf(rt, 0, cap, key_cap, false));
    // forest_wf(kids, 0): head wf + tail (single rt) wf.
    lemma_forest_wf_cons(kids, 0, cap, key_cap);
    assert(kids.drop_first() =~= seq![rt]);
    lemma_forest_wf_cons(seq![rt], 0, cap, key_cap);
    assert(seq![rt].drop_first() =~= Seq::<Tree>::empty());
    assert(forest_wf(kids, 0, cap, key_cap));

    // cross-node ordering clauses, instantiated at the single separator.
    assert forall|i: int| 0 <= i < 1 implies keys_all_lt(#[trigger] kids[i], seq![right_keys[0]][i]) by {
        // i == 0: kids[0] == lt; every left key < right_keys[0] == seps[0].
        assert(kids[0] == lt);
        assert(tree_keys(lt) == left_keys);
    }
    assert forall|i: int| 0 < i < 2 implies keys_all_ge(#[trigger] kids[i], seq![right_keys[0]][i - 1]) by {
        // i == 1: kids[1] == rt; every right key >= right_keys[0] == seps[0].
        assert(kids[1] == rt);
        assert(tree_keys(rt) == right_keys);
    }
    assert(tree_wf(root, 1, cap, key_cap, true));

    // height: 1 + forest_max_height(kids) == 1 (both leaves height 0).
    lemma_forest_max_height_cons(kids);
    lemma_forest_max_height_cons(seq![rt]);
    assert(tree_height(root) == 1);

    // in-order keys: forest_keys([lt, rt]) == left_keys + right_keys.
    lemma_forest_keys_cons(kids);
    lemma_forest_keys_cons(seq![rt]);
    assert(forest_keys(Seq::<Tree>::empty()) =~= Seq::<nat>::empty());
    assert(tree_keys(root) =~= left_keys + right_keys);
}

// ===========================================================================
// Internal-split tree reconstruction. A full internal node, after absorbing a
// new (separator, child), has `cseps` (length key_cap+1) separators and `ckids`
// (length key_cap+2) child subtrees, arranged as a wf internal node would be
// (sorted seps, children wf at h-1, cross-node ordering). Splitting at `imid`
// produces a left `Inner{lid, cseps[0..imid], ckids[0..=imid]}`, a promoted
// separator `cseps[imid]`, and a right `Inner{rid, cseps[imid+1..],
// ckids[imid+1..]}`. The lemma: both halves are wf at height `h`, the promoted
// key separates them, and the in-order keys recombine. Analogue of
// `lemma_split_tree_wf` (leaf) but the children are subtrees that transfer.
// ===========================================================================

pub proof fn lemma_internal_split_tree_wf(
    lid: nat,
    rid: nat,
    cseps: Seq<nat>,
    ckids: Seq<Tree>,
    imid: int,
    h: nat,
    cap: nat,
    key_cap: nat,
)
    requires
        h >= 1,
        cseps.len() == key_cap + 1,
        ckids.len() == cseps.len() + 1,
        0 <= imid < cseps.len(),
        imid == key_cap / 2,
        cap >= 1,
        key_cap >= 1,
        strictly_sorted(cseps),
        forest_wf(ckids, (h - 1) as nat, cap, key_cap),
        // cross-node ordering of the combined arrangement.
        (forall|i: int| 0 <= i < cseps.len() ==> keys_all_lt(#[trigger] ckids[i], cseps[i])),
        (forall|i: int| 0 < i < ckids.len() ==> keys_all_ge(#[trigger] ckids[i], cseps[i - 1])),
    ensures
        ({
            let lseps = cseps.subrange(0, imid);
            let rseps = cseps.subrange(imid + 1, cseps.len() as int);
            let lkids = ckids.subrange(0, imid + 1);
            let rkids = ckids.subrange(imid + 1, ckids.len() as int);
            let lt = Tree::Inner { id: lid, seps: lseps, kids: lkids };
            let rt = Tree::Inner { id: rid, seps: rseps, kids: rkids };
            &&& tree_wf(lt, h, cap, key_cap, false)
            &&& tree_wf(rt, h, cap, key_cap, false)
            // The promoted separator is a routing COPY, present in the right
            // subtree's leaves (B+tree), not removed from the model. The model
            // is just the two halves' leaf keys concatenated.
            &&& tree_keys(lt) + tree_keys(rt) == forest_keys(ckids)
        }),
{
    let lseps = cseps.subrange(0, imid);
    let rseps = cseps.subrange(imid + 1, cseps.len() as int);
    let lkids = ckids.subrange(0, imid + 1);
    let rkids = ckids.subrange(imid + 1, ckids.len() as int);
    let lt = Tree::Inner { id: lid, seps: lseps, kids: lkids };
    let rt = Tree::Inner { id: rid, seps: rseps, kids: rkids };

    // counts: lseps.len()==imid, rseps.len()==key_cap-imid, kids = seps+1.
    assert(lseps.len() == imid);
    assert(rseps.len() == key_cap - imid);
    assert(lkids.len() == imid + 1);
    assert(rkids.len() == (key_cap + 1) - imid);

    // occupancy: imid == key_cap/2 (>= key_cap/2 ✓); right key_cap-imid >= key_cap/2.
    // seps.len() <= key_cap for both.

    // sortedness of the sep subranges (subrange of strictly_sorted).
    assert(strictly_sorted(lseps)) by {
        assert forall|i: int, j: int| 0 <= i < j < lseps.len() implies #[trigger] lseps[i] < #[trigger] lseps[j] by {
            assert(lseps[i] == cseps[i]); assert(lseps[j] == cseps[j]);
        }
    }
    assert(strictly_sorted(rseps)) by {
        assert forall|i: int, j: int| 0 <= i < j < rseps.len() implies #[trigger] rseps[i] < #[trigger] rseps[j] by {
            assert(rseps[i] == cseps[imid + 1 + i]); assert(rseps[j] == cseps[imid + 1 + j]);
        }
    }

    // children forests wf at h-1 (subranges of a wf forest).
    lemma_forest_wf_subrange(ckids, (h - 1) as nat, cap, key_cap, 0, imid + 1);
    lemma_forest_wf_subrange(ckids, (h - 1) as nat, cap, key_cap, imid + 1, ckids.len() as int);

    // cross-node ordering for the left half: lkids[i] < lseps[i], lkids[i] >= lseps[i-1].
    assert forall|i: int| 0 <= i < lseps.len() implies keys_all_lt(#[trigger] lkids[i], lseps[i]) by {
        assert(lkids[i] == ckids[i]); assert(lseps[i] == cseps[i]);
    }
    assert forall|i: int| 0 < i < lkids.len() implies keys_all_ge(#[trigger] lkids[i], lseps[i - 1]) by {
        assert(lkids[i] == ckids[i]); assert(lseps[i - 1] == cseps[i - 1]);
    }
    // right half: rkids[i] == ckids[imid+1+i], rseps[i] == cseps[imid+1+i].
    assert forall|i: int| 0 <= i < rseps.len() implies keys_all_lt(#[trigger] rkids[i], rseps[i]) by {
        assert(rkids[i] == ckids[imid + 1 + i]); assert(rseps[i] == cseps[imid + 1 + i]);
    }
    assert forall|i: int| 0 < i < rkids.len() implies keys_all_ge(#[trigger] rkids[i], rseps[i - 1]) by {
        assert(rkids[i] == ckids[imid + 1 + i]); assert(rseps[i - 1] == cseps[imid + 1 + i - 1]);
    }

    // heights: both halves wf at h-1 ⟹ forest_max_height <= h-1, so tree_height
    // (1 + max) <= h; and >= 1 step gives == h via wf. tree_wf requires h>=1.
    lemma_forest_wf_max_height(lkids, (h - 1) as nat, cap, key_cap);
    lemma_forest_wf_max_height(rkids, (h - 1) as nat, cap, key_cap);

    assert(tree_wf(lt, h, cap, key_cap, false));
    assert(tree_wf(rt, h, cap, key_cap, false));

    // in-order keys: forest_keys(ckids) == forest_keys(lkids) + forest_keys(rkids),
    // and the promoted separator is a routing copy not in any leaf, so the model
    // recombination is tree_keys(lt) + [promoted] + tree_keys(rt) — BUT the
    // promoted key is NOT in the leaves; the model is forest_keys(lkids) +
    // forest_keys(rkids). The ensures states the routing arrangement; we prove
    // the keys identity via the forest split.
    lemma_forest_keys_split(ckids, imid + 1);
    assert(tree_keys(lt) == forest_keys(lkids));
    assert(tree_keys(rt) == forest_keys(rkids));
}

/// `forest_keys` splits at a cut: `forest_keys(kids) == forest_keys(kids[0..c])
/// + forest_keys(kids[c..])`. (Needed for the internal-split key recombination.)
pub proof fn lemma_forest_keys_split(kids: Seq<Tree>, c: int)
    requires 0 <= c <= kids.len(),
    ensures
        forest_keys(kids) == forest_keys(kids.subrange(0, c)) + forest_keys(kids.subrange(c, kids.len() as int)),
    decreases c,
{
    if c == 0 {
        assert(kids.subrange(0, 0) =~= Seq::<Tree>::empty());
        assert(kids.subrange(0, kids.len() as int) =~= kids);
    } else {
        // peel kids[0]: forest_keys(kids) = tree_keys(kids[0]) + forest_keys(df).
        lemma_forest_keys_cons(kids);
        let df = kids.drop_first();
        lemma_forest_keys_split(df, c - 1);
        // kids.subrange(0,c)[0] == kids[0]; subrange(0,c).drop_first() == df.subrange(0,c-1).
        lemma_forest_keys_cons(kids.subrange(0, c));
        assert(kids.subrange(0, c).drop_first() =~= df.subrange(0, c - 1));
        assert(kids.subrange(0, c)[0] == kids[0]);
        assert(df.subrange(c - 1, df.len() as int) =~= kids.subrange(c, kids.len() as int));
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
