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
/// Updating child `m` to a subtree whose FIRST leaf is unchanged (and which is
/// non-empty) preserves the forest's first leaf id and keeps every child's
/// first-leaf at the same boundary position. Full leaf-id-sequence equality is
/// NOT required (a deep-absorb split grows the sequence) — only the leftmost
/// leaf is pinned, which is all `forest_links_to` reads at child boundaries.
/// (Part of the subset+freshness contract fix; see `insert_rec` (F0).)
pub proof fn lemma_forest_leaf_ids_update_first(kids: Seq<Tree>, m: int, nc: Tree)
    requires
        0 <= m < kids.len(),
        tree_leaf_ids(nc).len() >= 1,
        tree_leaf_ids(kids[m]).len() >= 1,
        tree_leaf_ids(nc)[0] == tree_leaf_ids(kids[m])[0],
        forall|i: int| 0 <= i < kids.len() ==> #[trigger] tree_leaf_ids(kids[i]).len() >= 1,
    ensures
        // the forest's leftmost leaf is unchanged, and so is every child's first
        // leaf at its own index (the only leaf-id facts the link chain needs).
        forest_leaf_ids(kids.update(m, nc)).len() >= 1,
        forest_leaf_ids(kids.update(m, nc))[0] == forest_leaf_ids(kids)[0],
        forall|i: int| 0 <= i < kids.len() ==>
            #[trigger] tree_leaf_ids(kids.update(m, nc)[i])[0] == tree_leaf_ids(kids[i])[0],
    decreases kids,
{
    lemma_forest_leaf_ids_cons(kids);
    let u = kids.update(m, nc);
    lemma_forest_leaf_ids_cons(u);
    // per-index first-leaf preservation (i==m gives nc's preserved first leaf).
    assert forall|i: int| 0 <= i < kids.len() implies
        #[trigger] tree_leaf_ids(u[i])[0] == tree_leaf_ids(kids[i])[0] by {
        if i == m { assert(u[i] == nc); } else { assert(u[i] == kids[i]); }
    }
    // forest_leaf_ids(_) head == tree_leaf_ids(child 0) head (cons unfold), and
    // child 0's first leaf is preserved by the per-index fact above.
    assert(tree_leaf_ids(u[0]).len() >= 1);
    assert(forest_leaf_ids(u)[0] == tree_leaf_ids(u[0])[0]);
    assert(forest_leaf_ids(kids)[0] == tree_leaf_ids(kids[0])[0]);
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

/// A strictly-sorted sequence has no duplicates, hence its length equals its
/// set's cardinality (`vstd`'s `unique_seq_to_set`). Bridges the model sequence
/// (`tree_keys`, strictly sorted by `wf`) to the cached `nkeys` count: lets the
/// insert track `nkeys == model.len()` via the set, since the set is what the
/// model-transition ensures (`model' set == old set ∪ {key}`) speaks about.
pub proof fn lemma_strictly_sorted_len_eq_set(s: Seq<nat>)
    requires strictly_sorted(s),
    ensures s.len() == s.to_set().len(),
{
    assert(s.no_duplicates()) by {
        assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j
            implies s[i] != s[j] by {
            if i < j { assert(s[i] < s[j]); } else { assert(s[j] < s[i]); }
        }
    }
    s.unique_seq_to_set();
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

/// Concatenation of two sorted sequences is sorted when every element of the
/// left is strictly below every element of the right.
pub proof fn lemma_concat_sorted(a: Seq<nat>, b: Seq<nat>)
    requires
        strictly_sorted(a),
        strictly_sorted(b),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> (#[trigger] a[i]) < (#[trigger] b[j]),
    ensures strictly_sorted(a + b),
{
    assert forall|i: int, j: int| 0 <= i < j < (a + b).len() implies (#[trigger] (a + b)[i]) < (#[trigger] (a + b)[j]) by {
        if j < a.len() {
            assert((a + b)[i] == a[i]); assert((a + b)[j] == a[j]);
        } else if i >= a.len() {
            assert((a + b)[i] == b[i - a.len()]); assert((a + b)[j] == b[j - a.len()]);
        } else {
            // i in a, j in b: a[i] < b[j-a.len()] by the cross bound.
            assert((a + b)[i] == a[i]); assert((a + b)[j] == b[j - a.len()]);
        }
    }
}

/// THE IN-ORDER CORRECTNESS KEYSTONE: a wf ghost tree's in-order key sequence is
/// strictly increasing. This is the general (any-height) version of
/// `lemma_leaf_sorted`, and the literal statement that in-order traversal yields
/// keys in ascending order without duplicates. The cursor's soundness rests on
/// it. Induction over `t`: a leaf is sorted by `tree_wf`'s leaf arm; an internal
/// node's `forest_keys(kids)` is sorted because each child is sorted (IH) and the
/// cross-node ordering (`keys_all_lt`/`keys_all_ge` around the separators) places
/// every child's keys strictly below the next child's.
pub proof fn lemma_tree_wf_sorted(t: Tree, h: nat, cap: nat, key_cap: nat, is_root: bool)
    requires tree_wf(t, h, cap, key_cap, is_root),
    ensures strictly_sorted(tree_keys(t)),
    decreases t,
{
    match t {
        Tree::Leaf { keys, .. } => {
            // tree_wf leaf arm gives strictly_sorted(keys); tree_keys(Leaf) == keys.
        }
        Tree::Inner { seps, kids, .. } => {
            // tree_keys(Inner) == forest_keys(kids). Reduce to the forest lemma,
            // which needs each child sorted (IH) + the cross-node ordering.
            assert(forest_wf(kids, (h - 1) as nat, cap, key_cap));
            lemma_forest_keys_sorted(kids, seps, (h - 1) as nat, cap, key_cap);
        }
    }
}

/// `forest_keys(kids)` is sorted, given each child wf (so sorted, by the tree
/// lemma) and the cross-node ordering around `seps` (child i's keys `< seps[i]`,
/// child i+1's keys `>= seps[i]`). Induction on `kids`, peeling the head: the
/// head is sorted and entirely below `seps[0]`, while the tail's keys are all
/// `>= seps[0]` (every later child is `>= seps[i-1] >= seps[0]`), so the head
/// concatenates below the tail.
pub proof fn lemma_forest_keys_sorted(kids: Seq<Tree>, seps: Seq<nat>, h: nat, cap: nat, key_cap: nat)
    requires
        forest_wf(kids, h, cap, key_cap),
        kids.len() == seps.len() + 1,
        strictly_sorted(seps),
        (forall|i: int| 0 <= i < seps.len() ==> keys_all_lt(#[trigger] kids[i], seps[i])),
        (forall|i: int| 0 < i < kids.len() ==> keys_all_ge(#[trigger] kids[i], seps[i - 1])),
    ensures strictly_sorted(forest_keys(kids)),
    decreases kids,
{
    if kids.len() == 1 {
        // forest_keys([c]) == tree_keys(c); c is wf hence sorted.
        lemma_forest_keys_cons(kids);
        assert(kids.drop_first().len() == 0);
        assert(forest_keys(kids.drop_first()) =~= Seq::<nat>::empty());
        lemma_forest_wf_cons(kids, h, cap, key_cap);
        lemma_tree_wf_sorted(kids[0], h, cap, key_cap, false);
        assert(forest_keys(kids) =~= tree_keys(kids[0]));
    } else {
        let df = kids.drop_first();
        let dseps = seps.drop_first();
        lemma_forest_keys_cons(kids);
        lemma_forest_wf_cons(kids, h, cap, key_cap);
        // head sorted (IH-tree); tail sorted (IH-forest on df with dseps).
        lemma_tree_wf_sorted(kids[0], h, cap, key_cap, false);
        assert forall|i: int| 0 <= i < dseps.len() implies keys_all_lt(#[trigger] df[i], dseps[i]) by {
            assert(df[i] == kids[i + 1]); assert(dseps[i] == seps[i + 1]);
        }
        assert forall|i: int| 0 < i < df.len() implies keys_all_ge(#[trigger] df[i], dseps[i - 1]) by {
            assert(df[i] == kids[i + 1]); assert(dseps[i - 1] == seps[i]);
        }
        lemma_forest_keys_sorted(df, dseps, h, cap, key_cap);
        // cross bound: every head key < seps[0] <= every tail key. Tail keys are
        // in some df[m] == kids[m+1], all >= seps[m] >= seps[0] (seps sorted).
        assert(keys_all_lt(kids[0], seps[0]));  // head bound
        lemma_keys_all_lt_set(kids[0], seps[0]);
        assert forall|i: int, j: int| 0 <= i < tree_keys(kids[0]).len()
            && 0 <= j < forest_keys(df).len()
            implies (#[trigger] tree_keys(kids[0])[i]) < (#[trigger] forest_keys(df)[j]) by {
            // head key i < seps[0].
            assert(tree_keys(kids[0]).to_set().contains(tree_keys(kids[0])[i]));
            // tail key j >= seps[0]: it lives in some df[m] == kids[m+1], >= seps[m] >= seps[0].
            let tk = forest_keys(df)[j];
            assert(forest_keys(df).to_set().contains(tk));
            lemma_forest_keys_membership(df, tk);
            let m = choose|m: int| 0 <= m < df.len() && tree_keys(df[m]).contains(tk);
            assert(df[m] == kids[m + 1]);
            assert(keys_all_ge(kids[m + 1], seps[m]));
            lemma_keys_all_ge_set(kids[m + 1], seps[m]);
            // seps[m] >= seps[0] (sorted, m >= 0).
            if m > 0 { assert(seps[0] < seps[m]); }
        }
        lemma_concat_sorted(tree_keys(kids[0]), forest_keys(df));
        assert(forest_keys(kids) =~= tree_keys(kids[0]) + forest_keys(df));
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
            // (weakening) separator-min clause REMOVED (was seps[i-1] == tree_keys(kids[i])[0]).
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

/// Updating child `m` to a GROWN subtree (same root id; old ids retained; new
/// ids all `>= bound`, where `bound` is above every old forest id) preserves
/// `forest_disjoint`. This is the absorb step's real footprint relation: a node
/// deep under child `m` split, so `nc` has more ids than `kids[m]` — but the new
/// ids are freshly-allocated tail slots (`>= bound`), hence disjoint from every
/// sibling (whose ids are all `< bound`). The old exact-`==` form was a spec bug
/// (a `None` recursion result can still grow the footprint); see `bplus.rs`
/// `insert_rec`'s `(F0)` clause and the `footprint_contract_holds` runtime test.
pub proof fn lemma_forest_disjoint_update(kids: Seq<Tree>, m: int, nc: Tree, bound: nat)
    requires
        forest_disjoint(kids),
        0 <= m < kids.len(),
        tree_disjoint(nc),
        // old ids retained, new ids fresh (>= bound).
        tree_ids(kids[m]).subset_of(tree_ids(nc)),
        (forall|id: nat| tree_ids(nc).contains(id)
            ==> tree_ids(kids[m]).contains(id) || id >= bound),
        // bound is above every old forest id (so siblings are all < bound).
        (forall|id: nat| #[trigger] forest_ids(kids).contains(id) ==> id < bound),
        // FULL pairwise disjointness of the old children (tree_disjoint(parent)).
        (forall|i: int, j: int| 0 <= i < j < kids.len() ==>
            (#[trigger] tree_ids(kids[i])).disjoint(#[trigger] tree_ids(kids[j]))),
    ensures
        forest_disjoint(kids.update(m, nc)),
        // footprint grew monotonically by fresh ids only.
        forest_ids(kids).subset_of(forest_ids(kids.update(m, nc))),
        (forall|id: nat| #[trigger] forest_ids(kids.update(m, nc)).contains(id)
            ==> forest_ids(kids).contains(id) || id >= bound),
        // pairwise disjointness propagates to the updated forest (so the caller
        // can re-establish tree_disjoint's explicit pairwise clause on the parent).
        (forall|i: int, j: int| 0 <= i < j < kids.len() ==>
            (#[trigger] tree_ids(kids.update(m, nc)[i]))
                .disjoint(#[trigger] tree_ids(kids.update(m, nc)[j]))),
    decreases kids,
{
    lemma_forest_disjoint_cons(kids);
    // pairwise disjointness of the GROWN forest. For a pair (i, j): if neither is
    // m, both are old children, disjoint by hypothesis. If one is m, nc's ids are
    // old-child-m ids (disjoint from the other, by hypothesis) PLUS fresh (>=
    // bound) ids; the other child's ids are all < bound, so they cannot collide.
    let u0 = kids.update(m, nc);
    assert forall|i: int, j: int| 0 <= i < j < kids.len() implies
        (#[trigger] tree_ids(u0[i])).disjoint(#[trigger] tree_ids(u0[j])) by {
        assert forall|id: nat| tree_ids(u0[i]).contains(id) && tree_ids(u0[j]).contains(id)
            implies false by {
            if i != m && j != m {
                assert(u0[i] == kids[i] && u0[j] == kids[j]);
                assert(tree_ids(kids[i]).disjoint(tree_ids(kids[j])));
            } else if i == m {
                // u0[i] == nc, u0[j] == kids[j] (j != i == m). id in both.
                assert(u0[j] == kids[j]);
                // id in kids[j] ⟹ id < bound (forest_id). id in nc and < bound
                // ⟹ id in kids[m] (freshness). but kids[m]⊥kids[j].
                lemma_forest_id_in_forest(kids, j, id);
                assert(tree_ids(kids[m]).contains(id));
                assert(tree_ids(kids[m]).disjoint(tree_ids(kids[j])));
            } else {
                // j == m: u0[j] == nc, u0[i] == kids[i] (i != m).
                assert(u0[i] == kids[i]);
                lemma_forest_id_in_forest(kids, i, id);
                assert(tree_ids(kids[m]).contains(id));
                assert(tree_ids(kids[i]).disjoint(tree_ids(kids[m])));
            }
        }
    }
    lemma_forest_ids_cons(kids);
    let u = kids.update(m, nc);
    lemma_forest_disjoint_cons(u);
    lemma_forest_ids_cons(u);
    // sibling ids are all < bound (subset of forest_ids(kids)), so they are
    // disjoint from nc's fresh (>= bound) ids; on the old ids nc agrees with
    // kids[m]. Establish nc disjoint from each sibling.
    assert forall|i: int| 0 <= i < kids.len() && i != m implies
        (#[trigger] tree_ids(kids[i])).disjoint(tree_ids(nc)) by {
        assert forall|id: nat| tree_ids(kids[i]).contains(id) && tree_ids(nc).contains(id)
            implies false by {
            // id in sibling i ⟹ id in forest_ids(kids) ⟹ id < bound.
            lemma_forest_id_in_forest(kids, i, id);
            // id in nc and < bound ⟹ id in kids[m] (freshness contrapositive).
            assert(tree_ids(kids[m]).contains(id));
            // but kids[i] disjoint kids[m] — contradiction.
            assert(tree_ids(kids[i]).disjoint(tree_ids(kids[m])));
        }
    }
    if m == 0 {
        assert(u[0] == nc);
        assert(u.drop_first() =~= kids.drop_first());
        // forest_ids(u) == tree_ids(nc) ∪ forest_ids(df); forest_ids(kids) ==
        // tree_ids(kids[0]) ∪ forest_ids(df). subset + freshness follow.
        assert forall|i: int| 0 <= i < kids.drop_first().len() implies
            (#[trigger] tree_ids(kids.drop_first()[i])).disjoint(tree_ids(nc)) by {
            assert(kids.drop_first()[i] == kids[i + 1]);
        }
    } else {
        let df = kids.drop_first();
        assert(u[0] == kids[0]);
        assert(u.drop_first() =~= df.update(m - 1, nc));
        assert(df[m - 1] == kids[m]);
        assert forall|i: int, j: int| 0 <= i < j < df.len() implies
            (#[trigger] tree_ids(df[i])).disjoint(#[trigger] tree_ids(df[j])) by {
            assert(df[i] == kids[i + 1]); assert(df[j] == kids[j + 1]);
        }
        assert forall|id: nat| #[trigger] forest_ids(df).contains(id) implies id < bound by {
            lemma_forest_ids_tail_subset(kids, id);
        }
        lemma_forest_disjoint_update(df, m - 1, nc, bound);
        // head kids[0] is a sibling (0 != m), disjoint from nc, all its ids < bound.
        assert(tree_ids(kids[0]).disjoint(tree_ids(nc)));
    }
}

/// `tree_ids(kids[i]) ⊆ forest_ids(kids)` for any valid child index.
pub proof fn lemma_forest_id_in_forest(kids: Seq<Tree>, i: int, id: nat)
    requires 0 <= i < kids.len(), tree_ids(kids[i]).contains(id),
    ensures forest_ids(kids).contains(id),
    decreases kids,
{
    lemma_forest_ids_cons(kids);
    if i == 0 {
    } else {
        let df = kids.drop_first();
        assert(df[i - 1] == kids[i]);
        lemma_forest_id_in_forest(df, i - 1, id);
    }
}

/// `forest_ids(kids.drop_first()) ⊆ forest_ids(kids)`.
pub proof fn lemma_forest_ids_tail_subset(kids: Seq<Tree>, id: nat)
    requires kids.len() > 0, forest_ids(kids.drop_first()).contains(id),
    ensures forest_ids(kids).contains(id),
{
    lemma_forest_ids_cons(kids);
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
/// `forest_keys` distributes over concatenation: `forest_keys(a + b) ==
/// forest_keys(a) + forest_keys(b)`. (Split-child model recombination.)
pub proof fn lemma_forest_keys_concat(a: Seq<Tree>, b: Seq<Tree>)
    ensures forest_keys(a + b) == forest_keys(a) + forest_keys(b),
    decreases a,
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        lemma_forest_keys_cons(a);
        let adf = a.drop_first();
        lemma_forest_keys_concat(adf, b);
        assert((a + b).drop_first() =~= adf + b);
        assert((a + b)[0] == a[0]);
        lemma_forest_keys_cons(a + b);
    }
}

/// `forest_ids` distributes over concatenation (as a set union).
pub proof fn lemma_forest_ids_concat(a: Seq<Tree>, b: Seq<Tree>)
    ensures forest_ids(a + b) == forest_ids(a).union(forest_ids(b)),
    decreases a,
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(forest_ids(a) =~= Set::<nat>::empty());
    } else {
        lemma_forest_ids_cons(a);
        let adf = a.drop_first();
        lemma_forest_ids_concat(adf, b);
        assert((a + b).drop_first() =~= adf + b);
        assert((a + b)[0] == a[0]);
        lemma_forest_ids_cons(a + b);
        assert(forest_ids(a + b) =~= forest_ids(a).union(forest_ids(b)));
    }
}

/// `forest_leaf_ids` distributes over concatenation.
pub proof fn lemma_forest_leaf_ids_concat(a: Seq<Tree>, b: Seq<Tree>)
    ensures forest_leaf_ids(a + b) == forest_leaf_ids(a) + forest_leaf_ids(b),
    decreases a,
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        lemma_forest_leaf_ids_cons(a);
        let adf = a.drop_first();
        lemma_forest_leaf_ids_concat(adf, b);
        assert((a + b).drop_first() =~= adf + b);
        assert((a + b)[0] == a[0]);
        lemma_forest_leaf_ids_cons(a + b);
    }
}

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

/// A FULL node that is root-wf is also non-root-wf: the only clause the non-root
/// form adds is the minimum-occupancy lower bound, which a full node (leaf at
/// `cap` keys / internal at `key_cap` separators) trivially meets (`cap >=
/// (cap+1)/2`, `key_cap >= key_cap/2`). Lets the split branch — which fires only
/// on a full node — feed a root-form `cur` to the non-root reconstruction.
pub proof fn lemma_tree_wf_full_nonroot(t: Tree, h: nat, cap: nat, key_cap: nat)
    requires
        tree_wf(t, h, cap, key_cap, true),
        match t {
            Tree::Leaf { keys, .. } => keys.len() == cap,
            Tree::Inner { seps, .. } => seps.len() == key_cap,
        },
    ensures tree_wf(t, h, cap, key_cap, false),
{
    match t {
        Tree::Leaf { keys, .. } => { assert(keys.len() >= (cap + 1) / 2); }
        Tree::Inner { seps, .. } => { assert(seps.len() >= key_cap / 2); }
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

/// The leftmost in-order leaf of an Inner node is the leftmost leaf of child 0:
/// `tree_leaf_ids(Inner{kids})[0] == tree_leaf_ids(kids[0])[0]` (child 0 must be
/// non-empty, which `tree_wf`/`forest_wf` guarantee). The fact `seek_first`'s
/// child-0 descent rests on, and a non-emptiness carry for the chain.
pub proof fn lemma_inner_first_leaf(t: Tree, h: nat, cap: nat, key_cap: nat)
    requires
        t is Inner,
        tree_wf(t, h, cap, key_cap, true),
        cap >= 1,
    ensures
        tree_leaf_ids(t).len() >= 1,
        tree_leaf_ids(t)[0] == tree_leaf_ids(t->Inner_kids[0])[0],
        tree_leaf_ids(t->Inner_kids[0]).len() >= 1,
{
    let kids = t->Inner_kids;
    // child 0 wf at h-1 (forest_wf cons) ⟹ its leaf-id seq is non-empty.
    lemma_forest_wf_cons(kids, (h - 1) as nat, cap, key_cap);
    lemma_tree_leaf_ids_nonempty(kids[0], (h - 1) as nat, cap, key_cap, false);
    lemma_forest_leaf_ids_cons(kids);
    // forest_leaf_ids(kids) == tree_leaf_ids(kids[0]) ++ ...; head is kids[0]'s head.
    assert(tree_leaf_ids(t) == forest_leaf_ids(kids));
    assert(forest_leaf_ids(kids)[0] == tree_leaf_ids(kids[0])[0]);
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

/// A NON-root wf tree carries at least one key. Min-occupancy (clause 6) forces
/// a non-root leaf to `>= (cap+1)/2 >= 1` keys; a non-root internal recurses into
/// its (also non-root) head child. (Only non-root: an empty ROOT leaf has 0 keys.)
pub proof fn lemma_tree_keys_nonempty(t: Tree, h: nat, cap: nat, key_cap: nat)
    requires tree_wf(t, h, cap, key_cap, false), cap >= 1,
    ensures tree_keys(t).len() >= 1,
    decreases t,
{
    match t {
        Tree::Leaf { keys, .. } => {
            // non-root leaf: keys.len() >= (cap+1)/2 >= 1.
        }
        Tree::Inner { seps, kids, .. } => {
            // tree_keys(Inner) == forest_keys(kids); head child wf at h-1 non-root.
            lemma_forest_keys_cons(kids);
            lemma_forest_wf_cons(kids, (h - 1) as nat, cap, key_cap);
            lemma_tree_keys_nonempty(kids[0], (h - 1) as nat, cap, key_cap);
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
        // (weakening) combined separator-min requires REMOVED.
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
            // Cross-half ordering around the promoted median `cseps[imid]`: every
            // left-half key is `< cseps[imid]`, every right-half key `>= cseps[imid]`.
            // This is what the parent splice needs to slot (lt, promoted, rt) back
            // into the grandparent's children (it replaces the deleted separator-min
            // ensures `cseps[imid] == tree_keys(rt)[0]`).
            &&& keys_all_lt(lt, cseps[imid])
            &&& keys_all_ge(rt, cseps[imid])
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
    // (weakening) per-half separator-min proof REMOVED.

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

    // cross-half ordering around the promoted median cseps[imid]. Each left-half
    // key lives in some lkids[m] == ckids[m] (m <= imid), bounded < cseps[m] <=
    // cseps[imid]; each right-half key in ckids[imid+1+m], bounded >= cseps[imid+m]
    // >= cseps[imid]. Pure consequence of the combined cross-node ordering + the
    // sorted cseps (no separator-min needed).
    lemma_keys_all_lt_set(lt, cseps[imid]);
    assert forall|k: nat| tree_keys(lt).to_set().contains(k) implies k < cseps[imid] by {
        assert(forest_keys(lkids).contains(k));  // tree_keys(lt)==forest_keys(lkids)
        lemma_forest_keys_membership(lkids, k);
        let m = choose|m: int| 0 <= m < lkids.len() && tree_keys(lkids[m]).contains(k);
        assert(lkids[m] == ckids[m]);
        assert(keys_all_lt(ckids[m], cseps[m]));  // requires at i == m (m <= imid < cseps.len())
        lemma_keys_all_lt_set(ckids[m], cseps[m]);
        assert(tree_keys(ckids[m]).to_set().contains(k));
        assert(k < cseps[m]);
        if m < imid { assert(cseps[m] < cseps[imid]); }  // strictly_sorted(cseps)
    }
    lemma_keys_all_ge_set(rt, cseps[imid]);
    assert forall|k: nat| tree_keys(rt).to_set().contains(k) implies cseps[imid] <= k by {
        assert(forest_keys(rkids).contains(k));  // tree_keys(rt)==forest_keys(rkids)
        lemma_forest_keys_membership(rkids, k);
        let m = choose|m: int| 0 <= m < rkids.len() && tree_keys(rkids[m]).contains(k);
        assert(rkids[m] == ckids[imid + 1 + m]);
        assert(keys_all_ge(ckids[imid + 1 + m], cseps[imid + m]));  // requires at j == imid+1+m
        lemma_keys_all_ge_set(ckids[imid + 1 + m], cseps[imid + m]);
        assert(tree_keys(ckids[imid + 1 + m]).to_set().contains(k));
        assert(cseps[imid + m] <= k);
        if m > 0 { assert(cseps[imid] < cseps[imid + m]); }  // strictly_sorted(cseps)
    }
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

/// The combined-arrangement ingredients shared by BOTH split cases (child-split
/// absorb when the parent had room, and parent-split when it was full). After a
/// child `cp` splits into `(ncl, ncr)` separated by `sep`, the combined node
/// `Inner{gid, gseps.insert(cp,sep), gkids.update(cp,ncl).insert(cp+1,ncr)}` has:
/// strictly-sorted separators, a wf child forest at `h-1`, cross-node ordering,
/// and in-order keys = parent's ∪ {key}. This is occupancy-INDEPENDENT (it does
/// not constrain `nseps.len()` vs `key_cap`); the absorb case adds `< key_cap`,
/// the parent-split case feeds it to `lemma_internal_split_tree_wf` with
/// `== key_cap + 1`.
pub proof fn lemma_child_split_combined_wf(
    gid: nat,
    gseps: Seq<nat>,
    gkids: Seq<Tree>,
    cp: int,
    ncl: Tree,
    ncr: Tree,
    sep: nat,
    key: nat,
    h: nat,
    cap: nat,
    key_cap: nat,
)
    requires
        h >= 1,
        0 <= cp < gkids.len(),
        // root-form (weakest) input: this lemma reads only structural facts of
        // `cur` (sortedness, forest_wf, cross-node ordering), NEVER its occupancy,
        // so the is_root=true form suffices and both callers can relax into it.
        tree_wf(Tree::Inner { id: gid, seps: gseps, kids: gkids }, h, cap, key_cap, true),
        tree_wf(ncl, (h - 1) as nat, cap, key_cap, false),
        tree_wf(ncr, (h - 1) as nat, cap, key_cap, false),
        keys_all_lt(ncl, sep),
        keys_all_ge(ncr, sep),
        tree_keys(ncl).len() >= 1,
        tree_keys(ncr).len() >= 1,
        // (second weakening) the `sep ∈ (ncl+ncr)` membership is GONE: it was only
        // ever used to bound `sep < gseps[cp]`, which we now derive from the median
        // ordering + model + descent (see the sortedness sub-proof). Carrying it was
        // an over-strong residual of the first weakening — at a PARENT split the
        // promoted separator is an original `gseps[j]`, whose membership we deleted
        // with the separator-min invariant, so it was also UNPROVABLE there.
        (tree_keys(ncl) + tree_keys(ncr)).to_set()
            == tree_keys(gkids[cp]).to_set().insert(key),
        (forall|j: int| 0 <= j < cp ==> gseps[j] <= key),
        (forall|j: int| cp <= j < gseps.len() ==> key < gseps[j]),
    ensures
        ({
            let cseps = gseps.insert(cp, sep);
            let ckids = gkids.update(cp, ncl).insert(cp + 1, ncr);
            &&& cseps.len() == gseps.len() + 1
            &&& ckids.len() == cseps.len() + 1
            &&& strictly_sorted(cseps)
            &&& forest_wf(ckids, (h - 1) as nat, cap, key_cap)
            &&& (forall|i: int| 0 <= i < cseps.len() ==> keys_all_lt(#[trigger] ckids[i], cseps[i]))
            &&& (forall|i: int| 0 < i < ckids.len() ==> keys_all_ge(#[trigger] ckids[i], cseps[i - 1]))
            // (weakening) combined separator-min ensures REMOVED.
            &&& forest_keys(ckids).to_set() == tree_keys(Tree::Inner { id: gid, seps: gseps, kids: gkids }).to_set().insert(key)
        }),
{
    let cur = Tree::Inner { id: gid, seps: gseps, kids: gkids };
    let nseps = gseps.insert(cp, sep);
    let nkids = gkids.update(cp, ncl).insert(cp + 1, ncr);

    assert(nseps.len() == gseps.len() + 1);
    assert(nkids.len() == gkids.len() + 1);
    assert(nkids.len() == nseps.len() + 1);

    assert forall|i: int| 0 <= i < nkids.len() implies #[trigger] nkids[i] == (
        if i < cp { gkids[i] } else if i == cp { ncl } else if i == cp + 1 { ncr } else { gkids[i - 1] }
    ) by {}
    assert forall|j: int| 0 <= j < nseps.len() implies #[trigger] nseps[j] == (
        if j < cp { gseps[j] } else if j == cp { sep } else { gseps[j - 1] }
    ) by {}

    // (1) sortedness of nseps.
    assert(cp < gseps.len() ==> keys_all_lt(gkids[cp], gseps[cp]));
    assert(cp > 0 ==> keys_all_ge(gkids[cp], gseps[cp - 1]));
    // Bound `sep` strictly between the surrounding separators WITHOUT using any
    // membership of `sep` itself: the median ordering pins `sep` between the two
    // halves' boundary keys (`ncl[0] < sep <= ncr[0]` via the index form of
    // keys_all_lt/ge), and the model places those boundary keys inside the old
    // child (or at `key`), which the descent + cur's cross-node wf bound by
    // gseps[cp-1] / gseps[cp]. (This is why the `sep ∈ (ncl+ncr)` precondition is
    // NOT load-bearing — see the second-weakening fixpoint note; the genuinely
    // needed facts are the median ordering, the model, and non-emptiness.)
    assert(cp < gseps.len() ==> sep < gseps[cp]) by {
        if cp < gseps.len() {
            lemma_keys_all_lt_set(gkids[cp], gseps[cp]);   // child keys < gseps[cp] (set form)
            let m1 = tree_keys(ncr)[0];
            assert(sep <= m1);                              // keys_all_ge(ncr, sep) at index 0
            assert((tree_keys(ncl) + tree_keys(ncr))[tree_keys(ncl).len() as int] == m1);
            assert((tree_keys(ncl) + tree_keys(ncr)).to_set().contains(m1));
            assert(tree_keys(gkids[cp]).to_set().contains(m1) || m1 == key);
            if tree_keys(gkids[cp]).to_set().contains(m1) { assert(m1 < gseps[cp]); }
            else { assert(m1 == key); assert(key < gseps[cp]); }  // descent at j == cp
        }
    }
    assert(cp > 0 ==> gseps[cp - 1] < sep) by {
        if cp > 0 {
            lemma_keys_all_ge_set(gkids[cp], gseps[cp - 1]);  // child keys >= gseps[cp-1] (set form)
            let m0 = tree_keys(ncl)[0];
            assert(m0 < sep);                                  // keys_all_lt(ncl, sep) at index 0
            assert((tree_keys(ncl) + tree_keys(ncr))[0] == m0);
            assert((tree_keys(ncl) + tree_keys(ncr)).to_set().contains(m0));
            assert(tree_keys(gkids[cp]).to_set().contains(m0) || m0 == key);
            if tree_keys(gkids[cp]).to_set().contains(m0) { assert(gseps[cp - 1] <= m0); }
            else { assert(m0 == key); assert(gseps[cp - 1] <= key); }  // descent at j == cp-1
        }
    }
    assert(strictly_sorted(nseps)) by {
        assert forall|i: int, j: int| 0 <= i < j < nseps.len() implies #[trigger] nseps[i] < #[trigger] nseps[j] by {
            if j < cp { assert(nseps[i] == gseps[i] && nseps[j] == gseps[j]); }
            else if i < cp && j == cp {
                assert(nseps[i] == gseps[i] && nseps[j] == sep);
                if i < cp - 1 { assert(gseps[i] < gseps[cp - 1]); }
            }
            else if i < cp && j == cp + 1 { assert(nseps[i] == gseps[i] && nseps[j] == gseps[cp]); }
            else if i < cp && j > cp + 1 { assert(nseps[i] == gseps[i] && nseps[j] == gseps[j - 1]); }
            else if i == cp && j == cp + 1 { assert(nseps[i] == sep && nseps[j] == gseps[cp]); }
            else if i == cp && j > cp + 1 { assert(nseps[i] == sep && nseps[j] == gseps[j - 1]); assert(gseps[cp] <= gseps[j - 1]); }
            else { assert(nseps[i] == gseps[i - 1] && nseps[j] == gseps[j - 1]); }
        }
    }

    // (2) children forest wf.
    assert(forest_wf(gkids, (h - 1) as nat, cap, key_cap));
    let left = gkids.subrange(0, cp);
    let right = gkids.subrange(cp + 1, gkids.len() as int);
    lemma_forest_wf_subrange(gkids, (h - 1) as nat, cap, key_cap, 0, cp);
    lemma_forest_wf_subrange(gkids, (h - 1) as nat, cap, key_cap, cp + 1, gkids.len() as int);
    assert(forest_wf(seq![ncl, ncr], (h - 1) as nat, cap, key_cap)) by {
        lemma_forest_wf_cons(seq![ncl, ncr], (h - 1) as nat, cap, key_cap);
        assert(seq![ncl, ncr].drop_first() =~= seq![ncr]);
        lemma_forest_wf_cons(seq![ncr], (h - 1) as nat, cap, key_cap);
        assert(seq![ncr].drop_first() =~= Seq::<Tree>::empty());
    }
    assert(nkids =~= left + seq![ncl, ncr] + right);
    lemma_forest_wf_concat(left, seq![ncl, ncr], (h - 1) as nat, cap, key_cap);
    lemma_forest_wf_concat(left + seq![ncl, ncr], right, (h - 1) as nat, cap, key_cap);
    assert(forest_wf(nkids, (h - 1) as nat, cap, key_cap));

    // (3) cross-node ordering.
    assert forall|i: int| 0 <= i < nseps.len() implies keys_all_lt(#[trigger] nkids[i], nseps[i]) by {
        if i < cp { assert(nkids[i] == gkids[i] && nseps[i] == gseps[i]); }
        else if i == cp { assert(nkids[i] == ncl && nseps[i] == sep); }
        else if i == cp + 1 {
            assert(nkids[i] == ncr && nseps[i] == gseps[cp]);
            lemma_keys_all_lt_set(gkids[cp], gseps[cp]);
            lemma_keys_all_lt_set(ncr, gseps[cp]);
            assert forall|k: nat| tree_keys(ncr).to_set().contains(k) implies k < gseps[cp] by {
                assert((tree_keys(ncl) + tree_keys(ncr)).to_set().contains(k)) by {
                    lemma_seq_concat_to_set(tree_keys(ncl), tree_keys(ncr));
                }
                if tree_keys(gkids[cp]).to_set().contains(k) { } else { assert(k == key); }
            }
        }
        else { assert(nkids[i] == gkids[i - 1] && nseps[i] == gseps[i - 1]); }
    }
    assert forall|i: int| 0 < i < nkids.len() implies keys_all_ge(#[trigger] nkids[i], nseps[i - 1]) by {
        if i < cp { assert(nkids[i] == gkids[i] && nseps[i - 1] == gseps[i - 1]); }
        else if i == cp {
            assert(nkids[i] == ncl && nseps[i - 1] == gseps[cp - 1]);
            lemma_keys_all_ge_set(gkids[cp], gseps[cp - 1]);
            lemma_keys_all_ge_set(ncl, gseps[cp - 1]);
            assert forall|k: nat| tree_keys(ncl).to_set().contains(k) implies gseps[cp - 1] <= k by {
                assert((tree_keys(ncl) + tree_keys(ncr)).to_set().contains(k)) by {
                    lemma_seq_concat_to_set(tree_keys(ncl), tree_keys(ncr));
                }
                if tree_keys(gkids[cp]).to_set().contains(k) { } else { assert(k == key); }
            }
        }
        else if i == cp + 1 { assert(nkids[i] == ncr && nseps[i - 1] == sep); }
        else { assert(nkids[i] == gkids[i - 1] && nseps[i - 1] == gseps[i - 2]); }
    }

    // (weakening) combined separator-min proof block REMOVED.

    // (4) model recombination.
    let middle_new = tree_keys(ncl) + tree_keys(ncr);
    lemma_forest_keys_concat(left + seq![ncl, ncr], right);
    lemma_forest_keys_concat(left, seq![ncl, ncr]);
    assert(forest_keys(seq![ncl, ncr]) == middle_new) by {
        lemma_forest_keys_cons(seq![ncl, ncr]);
        assert(seq![ncl, ncr].drop_first() =~= seq![ncr]);
        lemma_forest_keys_cons(seq![ncr]);
        assert(seq![ncr].drop_first() =~= Seq::<Tree>::empty());
    }
    assert(forest_keys(nkids) == forest_keys(left) + middle_new + forest_keys(right)) by {
        assert(nkids =~= left + seq![ncl, ncr] + right);
    }
    lemma_forest_keys_split(gkids, cp);
    lemma_forest_keys_split(gkids.subrange(cp, gkids.len() as int), 1);
    assert(gkids.subrange(cp, gkids.len() as int).subrange(0, 1) =~= seq![gkids[cp]]);
    assert(gkids.subrange(cp, gkids.len() as int).subrange(1, gkids.subrange(cp, gkids.len() as int).len() as int)
        =~= right);
    lemma_forest_keys_cons(seq![gkids[cp]]);
    assert(seq![gkids[cp]].drop_first() =~= Seq::<Tree>::empty());
    assert(forest_keys(seq![gkids[cp]]) == tree_keys(gkids[cp]));
    assert(tree_keys(cur) == forest_keys(left) + tree_keys(gkids[cp]) + forest_keys(right));
    assert(middle_new.to_set() == tree_keys(gkids[cp]).to_set().insert(key));
    lemma_child_split_model_set(forest_keys(left), tree_keys(gkids[cp]), middle_new,
        forest_keys(right), key);
}

/// Structural reconstruction for the child-split ABSORB case: child `cp` of a wf
/// internal node split into `(ncl, ncr)` separated by `sep`, and the parent had
/// room. The new node `Inner{gid, gseps.insert(cp, sep), gkids.update(cp,
/// ncl).insert(cp+1, ncr)}` is `tree_wf` at the same height `h`, and its in-order
/// keys are the original parent's plus `key`. Pure ghost (no arena); the arena
/// `binds`/leaf-link/disjoint plumbing is layered on top in `bplus.rs`.
///
/// The splice is `gkids[0..cp] ++ [ncl, ncr] ++ gkids[cp+1..]` and the seps are
/// `gseps[0..cp] ++ [sep] ++ gseps[cp..]`; every `tree_wf` clause maps back to
/// the original parent's, with the split point handled by the supplied ordering
/// (`ncl < sep <= ncr`) and the descent routing (`gseps[cp-1] <= key < gseps[cp]`).
pub proof fn lemma_child_split_absorb_tree_wf(
    gid: nat,
    gseps: Seq<nat>,
    gkids: Seq<Tree>,
    cp: int,
    ncl: Tree,
    ncr: Tree,
    sep: nat,
    key: nat,
    h: nat,
    cap: nat,
    key_cap: nat,
    is_root: bool,
)
    requires
        h >= 1,
        0 <= cp < gkids.len(),
        // the original parent is wf at the caller's root-ness AND had room. The
        // rebuilt `nt` GAINS a separator, so when is_root==false its occupancy
        // (gseps.len()+1 >= key_cap/2) follows from cur's; when true it is dropped.
        tree_wf(Tree::Inner { id: gid, seps: gseps, kids: gkids }, h, cap, key_cap, is_root),
        gseps.len() < key_cap,
        // the two halves are wf at h-1 with the median ordering around `sep`.
        tree_wf(ncl, (h - 1) as nat, cap, key_cap, false),
        tree_wf(ncr, (h - 1) as nat, cap, key_cap, false),
        keys_all_lt(ncl, sep),
        keys_all_ge(ncr, sep),
        // both halves non-empty (a split's two pieces each carry >= 1 key); needed
        // for STRICT sortedness of the new separator list around `sep`.
        tree_keys(ncl).len() >= 1,
        tree_keys(ncr).len() >= 1,
        // (second weakening) `sep ∈ (ncl+ncr)` membership REMOVED — not consumed
        // (see lemma_child_split_combined_wf's sortedness sub-proof).
        // model: the two halves' keys are the old child's keys plus `key`.
        (tree_keys(ncl) + tree_keys(ncr)).to_set()
            == tree_keys(gkids[cp]).to_set().insert(key),
        // descent routing: `key` landed in child cp (bounded by the seps around cp).
        (forall|j: int| 0 <= j < cp ==> gseps[j] <= key),
        (forall|j: int| cp <= j < gseps.len() ==> key < gseps[j]),
    ensures
        ({
            let nseps = gseps.insert(cp, sep);
            let nkids = gkids.update(cp, ncl).insert(cp + 1, ncr);
            let nt = Tree::Inner { id: gid, seps: nseps, kids: nkids };
            &&& tree_wf(nt, h, cap, key_cap, is_root)
            &&& tree_keys(nt).to_set() == tree_keys(Tree::Inner { id: gid, seps: gseps, kids: gkids }).to_set().insert(key)
        }),
{
    let cur = Tree::Inner { id: gid, seps: gseps, kids: gkids };
    let nseps = gseps.insert(cp, sep);
    let nkids = gkids.update(cp, ncl).insert(cp + 1, ncr);
    let nt = Tree::Inner { id: gid, seps: nseps, kids: nkids };
    // combined_wf takes the root-form (weakest) input; relax cur into it.
    if !is_root { lemma_tree_wf_relax_root(cur, h, cap, key_cap); }
    // the combined-arrangement ingredients (sorted seps, forest_wf, cross-node
    // ordering, model) from the shared lemma.
    lemma_child_split_combined_wf(gid, gseps, gkids, cp, ncl, ncr, sep, key, h, cap, key_cap);
    assert(nseps.len() == gseps.len() + 1);
    assert(nseps.len() <= key_cap);  // gseps.len() < key_cap ⟹ +1 <= key_cap
    // heights: forest wf at h-1 ⟹ tree_wf(nt, h).
    lemma_forest_wf_max_height(nkids, (h - 1) as nat, cap, key_cap);
    // occupancy of nt at the caller's is_root: nseps.len() == gseps.len()+1.
    // When is_root==false, cur (non-root) gave gseps.len() >= key_cap/2, so
    // nseps.len() > key_cap/2 holds; when true, dropped.
    if !is_root { assert(gseps.len() >= key_cap / 2); }
    assert(tree_wf(nt, h, cap, key_cap, is_root));
    // model: tree_keys(nt) == forest_keys(nkids).
    assert(tree_keys(nt) == forest_keys(nkids));
}

/// Structural reconstruction for the PARENT-SPLIT case: child `cp` split into
/// `(ncl, ncr)` AND the parent was FULL (`gseps.len() == key_cap`). The combined
/// arrangement `(cseps, ckids)` has `cseps.len() == key_cap + 1`; splitting at
/// `imid == key_cap/2` gives a left half `lt`, a promoted separator `cseps[imid]`,
/// and a right half `rt`, both `tree_wf` at height `h`, with combined keys =
/// parent's ∪ {key}. Composes `lemma_child_split_combined_wf` (the combined
/// ingredients) with `lemma_internal_split_tree_wf` (the median split).
pub proof fn lemma_parent_split_tree_wf(
    gid: nat,
    rid: nat,
    gseps: Seq<nat>,
    gkids: Seq<Tree>,
    cp: int,
    ncl: Tree,
    ncr: Tree,
    sep: nat,
    key: nat,
    imid: int,
    h: nat,
    cap: nat,
    key_cap: nat,
)
    requires
        h >= 1,
        cap >= 1,
        key_cap >= 1,
        0 <= cp < gkids.len(),
        // parent was FULL.
        gseps.len() == key_cap,
        imid == key_cap / 2,
        tree_wf(Tree::Inner { id: gid, seps: gseps, kids: gkids }, h, cap, key_cap, false),
        tree_wf(ncl, (h - 1) as nat, cap, key_cap, false),
        tree_wf(ncr, (h - 1) as nat, cap, key_cap, false),
        keys_all_lt(ncl, sep),
        keys_all_ge(ncr, sep),
        tree_keys(ncl).len() >= 1,
        tree_keys(ncr).len() >= 1,
        // (second weakening) `sep ∈ (ncl+ncr)` membership REMOVED — see
        // lemma_child_split_combined_wf. (Was unprovable here anyway: the promoted
        // separator is an original gseps[j], not sep.)
        (tree_keys(ncl) + tree_keys(ncr)).to_set()
            == tree_keys(gkids[cp]).to_set().insert(key),
        (forall|j: int| 0 <= j < cp ==> gseps[j] <= key),
        (forall|j: int| cp <= j < gseps.len() ==> key < gseps[j]),
    ensures
        ({
            let cseps = gseps.insert(cp, sep);
            let ckids = gkids.update(cp, ncl).insert(cp + 1, ncr);
            let lt = Tree::Inner { id: gid, seps: cseps.subrange(0, imid), kids: ckids.subrange(0, imid + 1) };
            let rt = Tree::Inner { id: rid, seps: cseps.subrange(imid + 1, cseps.len() as int), kids: ckids.subrange(imid + 1, ckids.len() as int) };
            &&& tree_wf(lt, h, cap, key_cap, false)
            &&& tree_wf(rt, h, cap, key_cap, false)
            &&& (tree_keys(lt) + tree_keys(rt)).to_set()
                    == tree_keys(Tree::Inner { id: gid, seps: gseps, kids: gkids }).to_set().insert(key)
            // cross-half ordering around the promoted median `cseps[imid]` — the
            // routing arrangement the parent splice needs (replaces separator-min).
            &&& keys_all_lt(lt, cseps[imid])
            &&& keys_all_ge(rt, cseps[imid])
        }),
{
    let cseps = gseps.insert(cp, sep);
    let ckids = gkids.update(cp, ncl).insert(cp + 1, ncr);
    // combined ingredients from the shared lemma.
    lemma_child_split_combined_wf(gid, gseps, gkids, cp, ncl, ncr, sep, key, h, cap, key_cap);
    assert(cseps.len() == key_cap + 1);
    assert(ckids.len() == cseps.len() + 1);
    // the median split of the combined arrangement.
    lemma_internal_split_tree_wf(gid, rid, cseps, ckids, imid, h, cap, key_cap);
    let lt = Tree::Inner { id: gid, seps: cseps.subrange(0, imid), kids: ckids.subrange(0, imid + 1) };
    let rt = Tree::Inner { id: rid, seps: cseps.subrange(imid + 1, cseps.len() as int), kids: ckids.subrange(imid + 1, ckids.len() as int) };
    assert(tree_keys(lt) + tree_keys(rt) == forest_keys(ckids));  // lemma_internal_split_tree_wf
    assert((tree_keys(lt) + tree_keys(rt)).to_set() == forest_keys(ckids).to_set());
    // (weakening) lemma_parent_split_promoted call REMOVED.
}


/// `(a + b).to_set().contains(b[i])` for a valid index `i` into `b`.
pub proof fn lemma_seq_concat_contains_right(a: Seq<nat>, b: Seq<nat>, i: int)
    requires 0 <= i < b.len(),
    ensures (a + b).to_set().contains(b[i]),
{
    assert((a + b)[a.len() + i] == b[i]);
    assert((a + b).to_set().contains((a + b)[a.len() + i]));
}

/// `(a + b).to_set() == a.to_set().union(b.to_set())`.
proof fn lemma_seq_concat_to_set(a: Seq<nat>, b: Seq<nat>)
    ensures (a + b).to_set() == a.to_set().union(b.to_set()),
{
    assert((a + b).to_set() =~= a.to_set().union(b.to_set())) by {
        assert forall|k: nat| (a + b).to_set().contains(k) <==> a.to_set().union(b.to_set()).contains(k) by {
            if (a + b).to_set().contains(k) {
                let idx = choose|idx: int| 0 <= idx < (a + b).len() && (a + b)[idx] == k;
                if idx < a.len() { assert(a[idx] == k); } else { assert(b[idx - a.len()] == k); }
            }
            if a.to_set().contains(k) { let idx = choose|idx: int| 0 <= idx < a.len() && a[idx] == k; assert((a + b)[idx] == k); }
            if b.to_set().contains(k) { let idx = choose|idx: int| 0 <= idx < b.len() && b[idx] == k; assert((a + b)[a.len() + idx] == k); }
        }
    }
}

/// Set-level model recombination for the child-split absorb: if the middle piece
/// grows from `mid_old` to `mid_new` with `mid_new.to_set() == mid_old.to_set() ∪
/// {key}`, then `(L + mid_new + R).to_set() == (L + mid_old + R).to_set() ∪ {key}`.
proof fn lemma_child_split_model_set(l: Seq<nat>, mid_old: Seq<nat>, mid_new: Seq<nat>, r: Seq<nat>, key: nat)
    requires mid_new.to_set() == mid_old.to_set().insert(key),
    ensures (l + mid_new + r).to_set() == (l + mid_old + r).to_set().insert(key),
{
    lemma_seq_concat_to_set(l + mid_new, r);
    lemma_seq_concat_to_set(l, mid_new);
    lemma_seq_concat_to_set(l + mid_old, r);
    lemma_seq_concat_to_set(l, mid_old);
    assert((l + mid_new + r).to_set() =~= (l + mid_old + r).to_set().insert(key));
}

/// Footprint (`tree_ids`) reasoning for the child-split splice, pure ghost. With
/// a freshness `bound` separating old ids (`< bound`) from new ones (`>= bound`),
/// the spliced parent `nt` satisfies `tree_disjoint`, retains all of `cur`'s ids,
/// adds only fresh ids, and keeps the same leftmost leaf. Used by the arena-level
/// `reconstruct_child_split_*` wrappers.
pub proof fn lemma_child_split_absorb_ids(
    gid: nat, gseps: Seq<nat>, gkids: Seq<Tree>, cp: int, ncl: Tree, ncr: Tree, sep: nat, bound: nat,
)
    requires
        0 <= cp < gkids.len(),
        // cur is disjoint and all its ids are < bound.
        tree_disjoint(Tree::Inner { id: gid, seps: gseps, kids: gkids }),
        (forall|id: nat| #[trigger] tree_ids(Tree::Inner { id: gid, seps: gseps, kids: gkids }).contains(id) ==> id < bound),
        // the two halves: disjoint, tree_disjoint, footprints = old child ∪ fresh.
        tree_disjoint(ncl),
        tree_disjoint(ncr),
        tree_ids(ncl).disjoint(tree_ids(ncr)),
        // the old child's ids are retained across the two halves (a split
        // distributes them, never drops one): gkids[cp] ⊆ ncl ∪ ncr.
        (forall|id: nat| tree_ids(gkids[cp]).contains(id)
            ==> tree_ids(ncl).contains(id) || tree_ids(ncr).contains(id)),
        (forall|id: nat| tree_ids(ncl).contains(id) ==> tree_ids(gkids[cp]).contains(id) || id >= bound),
        (forall|id: nat| tree_ids(ncr).contains(id) ==> tree_ids(gkids[cp]).contains(id) || id >= bound),
        // leftmost leaf of ncl == leftmost leaf of the old child (split adds right).
        tree_leaf_ids(ncl).len() >= 1,
        tree_leaf_ids(gkids[cp]).len() >= 1,
        tree_leaf_ids(ncl)[0] == tree_leaf_ids(gkids[cp])[0],
        (forall|i: int| 0 <= i < gkids.len() ==> #[trigger] tree_leaf_ids(gkids[i]).len() >= 1),
    ensures
        ({
            let nseps = gseps.insert(cp, sep);
            let nkids = gkids.update(cp, ncl).insert(cp + 1, ncr);
            let nt = Tree::Inner { id: gid, seps: nseps, kids: nkids };
            &&& tree_disjoint(nt)
            &&& tree_ids(Tree::Inner { id: gid, seps: gseps, kids: gkids }).subset_of(tree_ids(nt))
            &&& (forall|id: nat| tree_ids(nt).contains(id)
                    ==> tree_ids(Tree::Inner { id: gid, seps: gseps, kids: gkids }).contains(id) || id >= bound)
            &&& tree_leaf_ids(nt).len() >= 1
            &&& tree_leaf_ids(nt)[0] == tree_leaf_ids(Tree::Inner { id: gid, seps: gseps, kids: gkids })[0]
        }),
{
    let cur = Tree::Inner { id: gid, seps: gseps, kids: gkids };
    let nseps = gseps.insert(cp, sep);
    let nkids = gkids.update(cp, ncl).insert(cp + 1, ncr);
    let nt = Tree::Inner { id: gid, seps: nseps, kids: nkids };
    assert(nkids =~= gkids.subrange(0, cp) + seq![ncl, ncr] + gkids.subrange(cp + 1, gkids.len() as int));
    // index map.
    assert forall|i: int| 0 <= i < nkids.len() implies #[trigger] nkids[i] == (
        if i < cp { gkids[i] } else if i == cp { ncl } else if i == cp + 1 { ncr } else { gkids[i - 1] }
    ) by {}

    // --- forest_ids(nkids) ⊇ forest_ids(gkids), and new ids fresh. ---
    assert forall|id: nat| #[trigger] forest_ids(gkids).contains(id) implies forest_ids(nkids).contains(id) by {
        lemma_forest_id_in_some_child(gkids, id);
        let m = choose|m: int| 0 <= m < gkids.len() && tree_ids(gkids[m]).contains(id);
        if m < cp { lemma_forest_id_in_forest(nkids, m, id); }
        else if m == cp {
            // old child id lands in ncl (slot cp) or ncr (slot cp+1).
            if tree_ids(ncl).contains(id) { lemma_forest_id_in_forest(nkids, cp, id); }
            else { assert(tree_ids(ncr).contains(id)); lemma_forest_id_in_forest(nkids, cp + 1, id); }
        }
        else { lemma_forest_id_in_forest(nkids, m + 1, id); assert(nkids[m + 1] == gkids[m]); }
    }
    assert forall|id: nat| #[trigger] forest_ids(nkids).contains(id)
        implies forest_ids(gkids).contains(id) || id >= bound by {
        lemma_forest_id_in_some_child(nkids, id);
        let m = choose|m: int| 0 <= m < nkids.len() && tree_ids(nkids[m]).contains(id);
        if m < cp { lemma_forest_id_in_forest(gkids, m, id); }
        else if m == cp { if tree_ids(gkids[cp]).contains(id) { lemma_forest_id_in_forest(gkids, cp, id); } }
        else if m == cp + 1 { if tree_ids(gkids[cp]).contains(id) { lemma_forest_id_in_forest(gkids, cp, id); } }
        else { assert(nkids[m] == gkids[m - 1]); lemma_forest_id_in_forest(gkids, m - 1, id); }
    }
    // tree_ids(cur) = {gid} ∪ forest_ids(gkids), tree_ids(nt) = {gid} ∪ forest_ids(nkids).
    assert(tree_ids(cur) =~= set![gid].union(forest_ids(gkids)));
    assert(tree_ids(nt) =~= set![gid].union(forest_ids(nkids)));
    assert(tree_ids(cur).subset_of(tree_ids(nt)));
    assert forall|id: nat| tree_ids(nt).contains(id) implies tree_ids(cur).contains(id) || id >= bound by {
        if id == gid { assert(tree_ids(cur).contains(gid)); }
    }

    // --- tree_disjoint(nt): gid ∉ forest_ids(nkids), forest_disjoint, pairwise. ---
    // gid ∈ tree_ids(cur) (it's cur's root), so gid < bound.
    assert(tree_ids(cur).contains(gid));
    assert(gid < bound);
    assert(!forest_ids(gkids).contains(gid));  // tree_disjoint(cur)
    assert(!forest_ids(nkids).contains(gid)) by {
        if forest_ids(nkids).contains(gid) {
            // gid ∈ forest_ids(nkids) ⟹ gid ∈ forest_ids(gkids) (gid < bound, so not fresh).
            assert(forest_ids(gkids).contains(gid) || gid >= bound);
        }
    }
    // every old forest id < bound (project the cur-level bound through forest_ids ⊆ tree_ids).
    assert forall|id: nat| #[trigger] forest_ids(gkids).contains(id) implies id < bound by {
        assert(tree_ids(cur).contains(id));  // forest_ids(gkids) ⊆ tree_ids(cur)
    }
    // pairwise disjointness of cur's children (tree_disjoint(cur) clause).
    assert forall|a: int, b: int| 0 <= a < b < gkids.len() implies
        (#[trigger] tree_ids(gkids[a])).disjoint(#[trigger] tree_ids(gkids[b])) by {}
    // pairwise disjointness of nkids.
    assert forall|i: int, j: int| 0 <= i < j < nkids.len() implies
        (#[trigger] tree_ids(nkids[i])).disjoint(#[trigger] tree_ids(nkids[j])) by {
        lemma_child_split_pair_disjoint(gkids, cp, ncl, ncr, bound, i, j);
    }
    // each child tree_disjoint.
    assert forall|m: int| 0 <= m < nkids.len() implies tree_disjoint(#[trigger] nkids[m]) by {
        if m < cp { lemma_forest_disjoint_at(gkids, m); }
        else if m == cp { } else if m == cp + 1 { }
        else { lemma_forest_disjoint_at(gkids, m - 1); }
    }
    lemma_forest_disjoint_from_pairwise(nkids);
    assert(tree_disjoint(nt));

    // --- first leaf preserved: nt's leftmost == cur's leftmost. ---
    assert(tree_leaf_ids(nt) == forest_leaf_ids(nkids));
    assert(tree_leaf_ids(cur) == forest_leaf_ids(gkids));
    lemma_forest_leaf_ids_cons(nkids);
    lemma_forest_leaf_ids_cons(gkids);
    // nkids[0] == gkids[0] when cp > 0; == ncl when cp == 0 (and ncl[0]==gkids[0][0]).
    if cp == 0 {
        assert(nkids[0] == ncl);
        assert(tree_leaf_ids(ncl)[0] == tree_leaf_ids(gkids[0])[0]);
    } else {
        assert(nkids[0] == gkids[0]);
    }
    assert(tree_leaf_ids(nkids[0]).len() >= 1);
    assert(forest_leaf_ids(nkids)[0] == tree_leaf_ids(nkids[0])[0]);
    assert(forest_leaf_ids(gkids)[0] == tree_leaf_ids(gkids[0])[0]);
}

/// One pair (i, j) of the child-split splice has disjoint footprints. Old/old
/// from `cur`'s pairwise; pairs touching ncl/ncr use the freshness `bound` and
/// `ncl ⊥ ncr`.
pub proof fn lemma_child_split_pair_disjoint(
    gkids: Seq<Tree>, cp: int, ncl: Tree, ncr: Tree, bound: nat, i: int, j: int,
)
    requires
        0 <= cp < gkids.len(),
        0 <= i < j < gkids.update(cp, ncl).insert(cp + 1, ncr).len(),
        (forall|a: int, b: int| 0 <= a < b < gkids.len() ==>
            (#[trigger] tree_ids(gkids[a])).disjoint(#[trigger] tree_ids(gkids[b]))),
        (forall|id: nat| #[trigger] forest_ids(gkids).contains(id) ==> id < bound),
        tree_ids(ncl).disjoint(tree_ids(ncr)),
        (forall|id: nat| tree_ids(ncl).contains(id) ==> tree_ids(gkids[cp]).contains(id) || id >= bound),
        (forall|id: nat| tree_ids(ncr).contains(id) ==> tree_ids(gkids[cp]).contains(id) || id >= bound),
    ensures
        ({
            let nkids = gkids.update(cp, ncl).insert(cp + 1, ncr);
            tree_ids(nkids[i]).disjoint(tree_ids(nkids[j]))
        }),
{
    let nkids = gkids.update(cp, ncl).insert(cp + 1, ncr);
    assert forall|i2: int| 0 <= i2 < nkids.len() implies #[trigger] nkids[i2] == (
        if i2 < cp { gkids[i2] } else if i2 == cp { ncl } else if i2 == cp + 1 { ncr } else { gkids[i2 - 1] }
    ) by {}
    // old-child index for slot s (mapping ncl/ncr back to child cp).
    let oi = if i < cp { i } else if i <= cp + 1 { cp } else { i - 1 };
    let oj = if j < cp { j } else if j <= cp + 1 { cp } else { j - 1 };
    // oi, oj are valid old-child indices, and oi != oj unless {i,j} == {cp, cp+1}.
    assert(0 <= oi < gkids.len() && 0 <= oj < gkids.len());
    assert(nkids[i] == ncl || nkids[i] == ncr || nkids[i] == gkids[oi]);
    assert(nkids[j] == ncl || nkids[j] == ncr || nkids[j] == gkids[oj]);
    assert forall|id: nat| tree_ids(nkids[i]).contains(id) && tree_ids(nkids[j]).contains(id) implies false by {
        if (i == cp && j == cp + 1) {
            // both ncl/ncr: ncl ⊥ ncr directly.
            assert(nkids[i] == ncl && nkids[j] == ncr);
        } else {
            // {i,j} != {cp,cp+1}, so oi != oj. Reduce each side to its OLD child:
            //  - if the slot is gkids[o], id ∈ gkids[o] already;
            //  - if the slot is ncl/ncr, id ∈ child cp (== gkids[cp] == gkids[o]) OR id is
            //    fresh (>= bound). A fresh id can't be in gkids[oj] (old, < bound), and if
            //    BOTH slots were ncl/ncr we'd be in the {cp,cp+1} case — excluded. So at
            //    least one side is an old child, forcing id < bound, hence both sides land
            //    in their old child gkids[oi]/gkids[oj], which are disjoint.
            assert(oi != oj);
            // id in gkids[oi]:
            if nkids[i] == ncl { assert(tree_ids(gkids[cp]).contains(id) || id >= bound); }
            else if nkids[i] == ncr { assert(tree_ids(gkids[cp]).contains(id) || id >= bound); }
            else { assert(tree_ids(gkids[oi]).contains(id)); }
            if nkids[j] == ncl { assert(tree_ids(gkids[cp]).contains(id) || id >= bound); }
            else if nkids[j] == ncr { assert(tree_ids(gkids[cp]).contains(id) || id >= bound); }
            else { assert(tree_ids(gkids[oj]).contains(id)); }
            // if id >= bound (fresh): it can't be in any OLD child (old ids < bound). At
            // least one of slot i / slot j is an old child gkids[o] (else both ncl/ncr ⟹
            // {cp,cp+1}); contradiction. So id < bound.
            if id >= bound {
                if nkids[i] == gkids[oi] { lemma_forest_id_in_forest(gkids, oi, id); }
                else if nkids[j] == gkids[oj] { lemma_forest_id_in_forest(gkids, oj, id); }
                else {
                    // both ncl/ncr but not the {cp,cp+1} pair ⟹ impossible (only slots
                    // cp, cp+1 are ncl/ncr).
                    assert((i == cp || i == cp + 1) && (j == cp + 1 || j == cp));
                }
            }
            // now id < bound: both sides reduce to their old child.
            assert(tree_ids(gkids[oi]).contains(id));
            assert(tree_ids(gkids[oj]).contains(id));
            if oi < oj { assert(tree_ids(gkids[oi]).disjoint(tree_ids(gkids[oj]))); }
            else { assert(tree_ids(gkids[oj]).disjoint(tree_ids(gkids[oi]))); }
        }
    }
}

/// `forest_disjoint` from "each child tree_disjoint + pairwise disjoint footprints".
pub proof fn lemma_forest_disjoint_from_pairwise(kids: Seq<Tree>)
    requires
        (forall|m: int| 0 <= m < kids.len() ==> tree_disjoint(#[trigger] kids[m])),
        (forall|i: int, j: int| 0 <= i < j < kids.len() ==>
            (#[trigger] tree_ids(kids[i])).disjoint(#[trigger] tree_ids(kids[j]))),
    ensures forest_disjoint(kids),
    decreases kids,
{
    if kids.len() == 0 {
    } else {
        let df = kids.drop_first();
        lemma_forest_disjoint_cons(kids);
        assert(tree_disjoint(kids[0]));  // m == 0
        assert forall|m: int| 0 <= m < df.len() implies tree_disjoint(#[trigger] df[m]) by {
            assert(df[m] == kids[m + 1]);
        }
        assert forall|i: int, j: int| 0 <= i < j < df.len() implies
            (#[trigger] tree_ids(df[i])).disjoint(#[trigger] tree_ids(df[j])) by {
            assert(df[i] == kids[i + 1]); assert(df[j] == kids[j + 1]);
        }
        lemma_forest_disjoint_from_pairwise(df);
    }
}

/// `tree_disjoint(half)` + footprint subset/freshness for one half of a parent
/// split: `half = Inner{hid, cseps[off..off+slen], ckids[off..off+slen+1]}`. The
/// half's children are a contiguous subrange of the combined `ckids` (which is
/// `forest_disjoint` + pairwise, with all ids `< bound` or fresh `>= bound`), so
/// they stay pairwise disjoint and `tree_disjoint`; the half's root `hid` is not
/// among them (`hid ∉ forest_ids(ckids)`).
pub proof fn lemma_parent_split_half_ids(
    ckids: Seq<Tree>, hid: nat, off: int, slen: int, bound: nat,
)
    requires
        0 <= off,
        0 <= slen,
        off + slen + 1 <= ckids.len(),
        forest_disjoint(ckids),
        (forall|i: int, j: int| 0 <= i < j < ckids.len() ==>
            (#[trigger] tree_ids(ckids[i])).disjoint(#[trigger] tree_ids(ckids[j]))),
        !forest_ids(ckids).contains(hid),
    ensures
        ({
            let hkids = ckids.subrange(off, off + slen + 1);
            let half = Tree::Inner { id: hid, seps: Seq::<nat>::empty(), kids: hkids };
            tree_disjoint(half)
        }),
{
    assert(off <= off + slen + 1 <= ckids.len());
    let hkids = ckids.subrange(off, off + slen + 1);
    assert(hkids.len() == slen + 1);
    // subrange indexing: hkids[k] == ckids[off+k] for k in range (vstd axiom).
    assert forall|k: int| 0 <= k < hkids.len() implies #[trigger] hkids[k] == ckids[off + k] by {
        assert(hkids[k] == ckids.subrange(off, off + slen + 1)[k]);
    }
    // each child tree_disjoint (subrange of a forest_disjoint forest).
    assert forall|m: int| 0 <= m < hkids.len() implies tree_disjoint(#[trigger] hkids[m]) by {
        lemma_forest_disjoint_at(ckids, off + m);
    }
    // pairwise (subrange of pairwise).
    assert forall|i: int, j: int| 0 <= i < j < hkids.len() implies
        (#[trigger] tree_ids(hkids[i])).disjoint(#[trigger] tree_ids(hkids[j])) by {}
    lemma_forest_disjoint_from_pairwise(hkids);
    // hid ∉ forest_ids(hkids): hkids ids ⊆ forest_ids(ckids), which excludes hid.
    assert(!forest_ids(hkids).contains(hid)) by {
        if forest_ids(hkids).contains(hid) {
            lemma_forest_id_in_some_child(hkids, hid);
            let m = choose|m: int| 0 <= m < hkids.len() && tree_ids(hkids[m]).contains(hid);
            lemma_forest_id_in_forest(ckids, off + m, hid);  // hkids[m] == ckids[off+m]
        }
    }
}

/// Footprint of the two parent-split halves vs the original `cur`. With `lt =
/// Inner{gid, _, lkids}`, `rt = Inner{rid, _, rkids}`, `lkids + rkids == ckids`
/// (the combined children), and `gid`/`rid` the half roots: the union of the
/// halves' footprints is `{gid, rid} ∪ forest_ids(ckids)`, which retains all of
/// `cur`'s ids and adds only fresh ones (`>= bound`); and `lt`'s leftmost leaf is
/// `cur`'s (lt's first child is ckids[0], whose leftmost leaf is cur's via the
/// combined first-leaf fact). Pure ghost over `tree_ids`/`forest_ids`.
pub proof fn lemma_parent_split_footprint(
    cur: Tree, gid: nat, rid: nat, gkids: Seq<Tree>,
    lt: Tree, rt: Tree, lkids: Seq<Tree>, rkids: Seq<Tree>, ckids: Seq<Tree>, bound: nat,
)
    requires
        cur is Inner,
        cur->Inner_id == gid,
        cur->Inner_kids == gkids,
        lt == (Tree::Inner { id: gid, seps: lt->Inner_seps, kids: lkids }),
        rt == (Tree::Inner { id: rid, seps: rt->Inner_seps, kids: rkids }),
        lkids + rkids == ckids,
        lkids.len() >= 1,
        forest_ids(gkids).subset_of(forest_ids(ckids)),
        (forall|id: nat| #[trigger] forest_ids(ckids).contains(id)
            ==> forest_ids(gkids).contains(id) || id >= bound),
        gid < bound,
        rid >= bound,
        tree_leaf_ids(lkids[0]).len() >= 1,
        tree_leaf_ids(lkids[0])[0] == tree_leaf_ids(cur)[0],
        tree_leaf_ids(cur).len() >= 1,
    ensures
        (forall|id: nat| tree_ids(lt).contains(id) ==> tree_ids(cur).contains(id) || id >= bound),
        (forall|id: nat| tree_ids(rt).contains(id) ==> tree_ids(cur).contains(id) || id >= bound),
        (forall|id: nat| tree_ids(cur).contains(id) ==> tree_ids(lt).contains(id) || tree_ids(rt).contains(id)),
        tree_leaf_ids(lt).len() >= 1,
        tree_leaf_ids(lt)[0] == tree_leaf_ids(cur)[0],
{
    assert(tree_ids(lt) =~= set![gid].union(forest_ids(lkids)));
    assert(tree_ids(rt) =~= set![rid].union(forest_ids(rkids)));
    assert(tree_ids(cur) =~= set![gid].union(forest_ids(gkids)));
    lemma_forest_ids_concat(lkids, rkids);
    assert(forest_ids(ckids) =~= forest_ids(lkids).union(forest_ids(rkids)));
    assert forall|id: nat| tree_ids(lt).contains(id) implies tree_ids(cur).contains(id) || id >= bound by {
        if id == gid { } else {
            assert(forest_ids(lkids).contains(id));
            assert(forest_ids(ckids).contains(id));
        }
    }
    assert forall|id: nat| tree_ids(rt).contains(id) implies tree_ids(cur).contains(id) || id >= bound by {
        if id == rid { } else {
            assert(forest_ids(rkids).contains(id));
            assert(forest_ids(ckids).contains(id));
        }
    }
    assert forall|id: nat| tree_ids(cur).contains(id) implies tree_ids(lt).contains(id) || tree_ids(rt).contains(id) by {
        if id == gid { } else {
            assert(forest_ids(gkids).contains(id));
            assert(forest_ids(ckids).contains(id));
        }
    }
    lemma_forest_leaf_ids_cons(lkids);
    assert(tree_leaf_ids(lt) == forest_leaf_ids(lkids));
    assert(tree_leaf_ids(lt)[0] == tree_leaf_ids(lkids[0])[0]);
}

/// `tree_ids(lt).disjoint(tree_ids(rt))` for the two parent-split halves. With
/// `lkids = ckids[0..m]`, `rkids = ckids[m..]` (so `lkids + rkids == ckids`),
/// `forest_disjoint(ckids)` + pairwise-disjoint children give
/// `forest_ids(lkids) ⊥ forest_ids(rkids)`; the two distinct roots `gid` (< bound)
/// and `rid` (>= bound) are outside both child-id sets, so the whole footprints
/// are disjoint. Pure ghost over `tree_ids`/`forest_ids`.
pub proof fn lemma_parent_split_disjoint(
    gid: nat, rid: nat, ckids: Seq<Tree>, lt: Tree, rt: Tree,
    lkids: Seq<Tree>, rkids: Seq<Tree>, bound: nat,
)
    requires
        lt == (Tree::Inner { id: gid, seps: lt->Inner_seps, kids: lkids }),
        rt == (Tree::Inner { id: rid, seps: rt->Inner_seps, kids: rkids }),
        lkids + rkids == ckids,
        (forall|i: int, j: int| 0 <= i < j < ckids.len() ==>
            (#[trigger] tree_ids(ckids[i])).disjoint(#[trigger] tree_ids(ckids[j]))),
        // the two roots are distinct and outside every child's footprint: gid is an
        // OLD id (< bound) absent from ckids; rid is FRESH (>= bound) and ckids' ids
        // are all old (< bound) or == rid is excluded by being the brand-new slot.
        (forall|id: nat| #[trigger] forest_ids(ckids).contains(id) ==> id < bound),
        gid < bound,
        rid >= bound,
        !forest_ids(ckids).contains(gid),
    ensures
        tree_ids(lt).disjoint(tree_ids(rt)),
{
    lemma_forest_ids_concat(lkids, rkids);
    assert(forest_ids(ckids) =~= forest_ids(lkids).union(forest_ids(rkids)));
    assert(tree_ids(lt) =~= set![gid].union(forest_ids(lkids)));
    assert(tree_ids(rt) =~= set![rid].union(forest_ids(rkids)));
    // forest_ids(lkids) ⊥ forest_ids(rkids): a shared id would sit in lkids[i] and
    // rkids[j] == ckids[i] and ckids[lkids.len()+j], two distinct ckids indices.
    assert forall|id: nat| forest_ids(lkids).contains(id) implies !forest_ids(rkids).contains(id) by {
        if forest_ids(rkids).contains(id) {
            lemma_forest_id_in_some_child(lkids, id);
            lemma_forest_id_in_some_child(rkids, id);
            let i = choose|i: int| 0 <= i < lkids.len() && tree_ids(lkids[i]).contains(id);
            let j = choose|j: int| 0 <= j < rkids.len() && tree_ids(rkids[j]).contains(id);
            assert(ckids[i] == lkids[i]);                      // lkids == ckids[0..m]
            assert(ckids[lkids.len() + j] == rkids[j]);        // rkids == ckids[m..]
            assert(tree_ids(ckids[i]).contains(id));
            assert(tree_ids(ckids[lkids.len() + j]).contains(id));
            // i < lkids.len() <= lkids.len()+j, so they are distinct ckids indices.
            assert(tree_ids(ckids[i]).disjoint(tree_ids(ckids[lkids.len() + j])));
        }
    }
    assert forall|id: nat| tree_ids(lt).contains(id) implies !tree_ids(rt).contains(id) by {
        if id == gid {
            // gid < bound, and rt's ids are rid (>= bound) or forest_ids(rkids) ⊆
            // forest_ids(ckids) (< bound but != gid since gid ∉ forest_ids(ckids)).
            if id == rid { } else if forest_ids(rkids).contains(id) {
                assert(forest_ids(ckids).contains(id));  // gid ∉ forest_ids(ckids): contradiction
            }
        } else {
            assert(forest_ids(lkids).contains(id));
            if id == rid {
                assert(forest_ids(ckids).contains(id));  // id < bound, but rid >= bound
            } else {
                assert(!forest_ids(rkids).contains(id));  // disjoint child-id sets
            }
        }
    }
    assert(tree_ids(lt).disjoint(tree_ids(rt)));
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
