// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent B+tree set, generic over key width and node geometry,
//! matching production's `BPlusTreeSet<K, L, S, TRACK>`.
//!
//! The executable structure is a node arena plus a root id; it *represents* a
//! ghost recursive [`Tree`](crate::bplus_tree) whose structural invariants
//! ([`tree_wf`](crate::bplus_tree::tree_wf)) are the textbook B+tree properties.
//! `wf` ties the two together with a flat per-node binding ([`binds`]); the
//! abstract model is the ghost tree's in-order keys
//! ([`tree_keys`](crate::bplus_tree::tree_keys)). This is the
//! arena / dynamic-frames method of
//! [Ch 9](../design/09-arena-aliasing-dynamic-frames.md); see the
//! [wf-invariant analysis](../../doc/future/bplus-wf-invariant-analysis.md).
//!
//! Generic parameters mirror production exactly:
//!   - `K: DenseId` — the key type (31- or 63-bit dense id);
//!   - `L: NodeLayout<Word = K::Index>` — node geometry (one of the six packed
//!     layouts), so keys are stored as `K::Index` words;
//!   - `S: SearchKind` — the in-node search (binary search);
//!   - `const TRACK` — semi-persistence on/off.
//!
//! The arena is an `InlineStore`-backed `Vec` (production's `VecI`): the node is
//! [`Tagged`], its semi-persistence capture bit stolen into the packed repr, so
//! `mark`/`restore` compose for free.
//!
//! Milestone status (this commit = M2a): the generic struct, the ghost-tree
//! binding, `wf`, `model`, and `new`/`is_empty`/`len` on the single-leaf base
//! case. `contains` (M2b), `insert` (M3), split/propagation (M4–M5) follow.
//! Disjointness of subtree id-sets (the dynamic-frames separation clause) is
//! introduced when multi-node trees first appear (M3); on the single leaf it is
//! vacuous.

use vstd::prelude::*;

use crate::bplus_layout::NodeLayout;
use crate::bplus_search::SearchKind;
use crate::bplus_tree::Tree;
use crate::index_like::IndexLike;
use crate::inline_store::InlineStore;
use crate::opt::DenseId;
use crate::tagged::Tagged;
use crate::vec::{ShrinkPolicy, Vec as SpVec, VecToken};

verus! {

// ===== LAYER 1: model + read-only (wf, spec vocabulary, new/contains/len) =====


/// The arena binding: the executable arena `arena` realizes the ghost tree `t`.
/// Recurses on the ghost tree (the validated idiom); the per-node clauses are a
/// flat read of `arena[id]`. For each ghost node at `id`: `id` is in range, the
/// arena node's leaf-ness and key/separator words match the ghost keys (under
/// `as_nat`), and (for an internal node) the executable child indices equal the
/// ghost children's root ids.
pub open spec fn binds<L: NodeLayout>(arena: Seq<L::Node>, t: Tree) -> bool
    decreases t
{
    match t {
        Tree::Leaf { id, keys } => {
            &&& id < arena.len()
            &&& L::is_leaf_spec(arena[id as int])
            &&& L::count_spec(arena[id as int]) == keys.len()
            &&& (forall|i: int| 0 <= i < keys.len() ==>
                    (#[trigger] L::keys_view(arena[id as int])[i]).as_nat() == keys[i])
        }
        Tree::Inner { id, seps, kids } => {
            &&& id < arena.len()
            &&& !L::is_leaf_spec(arena[id as int])
            &&& L::count_spec(arena[id as int]) == seps.len()
            &&& (forall|i: int| 0 <= i < seps.len() ==>
                    (#[trigger] L::keys_view(arena[id as int])[i]).as_nat() == seps[i])
            &&& (forall|i: int| 0 <= i < kids.len() ==>
                    L::child_view(arena[id as int], i) == crate::bplus_tree::tree_root_id(#[trigger] kids[i]))
            &&& forest_binds_l::<L>(arena, kids)
        }
    }
}

/// Forest companion of [`binds`] (every child subtree binds).
pub open spec fn forest_binds_l<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>) -> bool
    decreases kids
{
    if kids.len() == 0 {
        true
    } else {
        binds::<L>(arena, kids[0]) && forest_binds_l::<L>(arena, kids.drop_first())
    }
}

/// The NIL leaf-link sentinel (`max_nat - 1`), the `u32::MAX`/`usize::MAX` value
/// `new_leaf` writes. Terminates the leaf-link chain; provably distinct from
/// every real arena id because `Vec::push` keeps `len < max_nat - 1`.
pub open spec fn nil_link<L: NodeLayout>() -> nat {
    (<L::ArenaIdx as IndexLike>::max_nat() - 1) as nat
}

/// The seek target index: the number of model keys strictly below `t`. For a
/// strictly-sorted model this is the position of the first key `>= t` (leapfrog's
/// `seek` semantics: land on the least element not below the target). Defined as
/// a count so it is monotone and total even when `t` is absent.
pub open spec fn seek_target_idx(model: Seq<nat>, t: nat) -> int
    decreases model.len()
{
    if model.len() == 0 {
        0
    } else if model[0] < t {
        1 + seek_target_idx(model.drop_first(), t)
    } else {
        // strictly-sorted ⟹ once a key is >= t, all later keys are too.
        0
    }
}

/// Every model value is a genuine `K`-image: `< K::id_bound()`. The refinement
/// the `K -> K::Index` storage coercion drops (the stored `Index` word type is
/// wider than the id's valid range), re-asserted at the model. Insert preserves
/// it for free — it only ever adds `key.id_nat()`, bounded by
/// `lemma_id_nat_bounded` — and it makes the cursor's `from_usize` read exact.
pub open spec fn model_bounded<K: DenseId>(model: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < model.len() ==> #[trigger] model[i] < K::id_bound()
}

/// Subtree-relative leaf-link consistency: within `t`'s in-order leaf sequence
/// `lids`, each leaf links to the next, and the *last* leaf links to `succ` (the
/// subtree's global successor — the first leaf of whatever follows `t`, or NIL
/// if `t` is the whole tree). This is the form the recursion needs: a subtree's
/// last leaf points *out* of the subtree, so the predicate must be parameterized
/// by the successor rather than hard-coding NIL.
pub open spec fn leaf_links_to<L: NodeLayout>(arena: Seq<L::Node>, t: Tree, succ: nat) -> bool {
    let lids = crate::bplus_tree::tree_leaf_ids(t);
    forall|p: int| 0 <= p < lids.len() ==>
        #[trigger] L::link_view(arena[lids[p] as int]) == (
            if p + 1 < lids.len() { lids[p + 1] } else { succ }
        )
}

/// Leaf-link consistency (clause 5) for the whole tree: the chain ends at NIL.
/// The `wf`-level instance of [`leaf_links_to`] with `succ == nil_link`. Bound to
/// the tree (single source of truth), so the sorted cursor's walk is sound by
/// `tree_wf`'s cross-node ordering, not by an independent assumption.
pub open spec fn leaf_links_ok<L: NodeLayout>(arena: Seq<L::Node>, t: Tree) -> bool {
    leaf_links_to::<L>(arena, t, nil_link::<L>())
}

/// Compositional leaf-links over a forest: child `i`'s chain ends at child
/// `i+1`'s first leaf (or `succ` for the last child). The decomposition of an
/// internal node's `leaf_links_to` into its children's — what lets the recursion
/// re-assemble the parent's chain from the (updated) child chains.
pub open spec fn forest_links_to<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>, succ: nat) -> bool
    decreases kids
{
    if kids.len() == 0 {
        true
    } else {
        let s0 = if kids.len() > 1 {
            crate::bplus_tree::tree_leaf_ids(kids[1])[0]
        } else {
            succ
        };
        &&& leaf_links_to::<L>(arena, kids[0], s0)
        &&& forest_links_to::<L>(arena, kids.drop_first(), succ)
    }
}

/// The semi-persistent B+tree set. `nodes` is the `InlineStore`-backed arena,
/// `root` the root's arena index, `nkeys` the cached key count, and `tree` the
/// ghost recursive model `wf`/`model` are stated over.
pub struct BPlusTreeSet<K, L, S, const TRACK: bool>
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
{
    pub nodes: SpVec<L::Node, L::ArenaIdx, InlineStore<L::Node, L::ArenaIdx>, TRACK>,
    /// Arena index of the root node.
    pub root: L::ArenaIdx,
    /// Number of keys (cached; equals `model().len()`). Mirrors production's
    /// header `nkeys`.
    pub nkeys: usize,
    /// Ghost recursive model.
    pub tree: Ghost<Tree>,
    pub _k: core::marker::PhantomData<K>,
    pub _s: core::marker::PhantomData<S>,
}

/// Forest companion of [`lemma_inner_binds_child`]: project `forest_binds_l` to
/// one child (the arena binds each child subtree). Mirrors `lemma_forest_wf_at`.
pub proof fn lemma_forest_binds_at<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>, m: int)
    requires
        forest_binds_l::<L>(arena, kids),
        0 <= m < kids.len(),
    ensures
        binds::<L>(arena, kids[m]),
    decreases kids,
{
    if m == 0 {
    } else {
        let df = kids.drop_first();
        assert(df[m - 1] == kids[m]);
        lemma_forest_binds_at::<L>(arena, df, m - 1);
    }
}

/// Descent binding step (arena side). From `binds` at an internal subtree, the
/// arena binds child `cp` and the executable `child_view(node, cp)` equals that
/// child's root id, so a descent following `child(node, cp)` lands at the arena
/// node that binds `kids[cp]`.
pub proof fn lemma_inner_binds_child<L: NodeLayout>(
    arena: Seq<L::Node>,
    id: nat,
    seps: Seq<nat>,
    kids: Seq<Tree>,
    cp: int,
)
    requires
        binds::<L>(arena, Tree::Inner { id, seps, kids }),
        0 <= cp < kids.len(),
    ensures
        binds::<L>(arena, kids[cp]),
        L::child_view(arena[id as int], cp) == crate::bplus_tree::tree_root_id(kids[cp]),
{
    lemma_forest_binds_at::<L>(arena, kids, cp);
}

/// Internal-node binding facts: the arena node at an internal subtree's root is
/// non-leaf, its `count` is the separator count, its key view projects to the
/// separators, and (with `tree_wf`'s strict sortedness) that view is `sorted_le`
/// — the precondition the descent's separator scan needs.
pub proof fn lemma_inner_facts<L: NodeLayout>(
    arena: Seq<L::Node>,
    id: nat,
    seps: Seq<nat>,
    kids: Seq<Tree>,
    h: nat,
)
    requires
        binds::<L>(arena, Tree::Inner { id, seps, kids }),
        crate::bplus_tree::tree_wf(Tree::Inner { id, seps, kids }, h, L::leaf_cap_spec(), L::key_cap_spec(), true),
    ensures
        id < arena.len(),
        !L::is_leaf_spec(arena[id as int]),
        L::node_wf(arena[id as int]),
        L::count_spec(arena[id as int]) == seps.len(),
        L::keys_view(arena[id as int]).len() == seps.len(),
        forall|i: int| 0 <= i < seps.len() ==>
            (#[trigger] L::keys_view(arena[id as int])[i]).as_nat() == seps[i],
        crate::bplus_search::sorted_le(L::keys_view(arena[id as int])),
{
    let node = arena[id as int];
    // binds Inner arm: !is_leaf, count == seps.len, per-sep projection.
    assert(L::count_spec(node) == seps.len());
    // node_wf from tree_wf (seps.len() <= key_cap) via the iff.
    L::lemma_node_wf_iff(node);
    L::lemma_keys_view_len(node);
    // sorted_le(keys_view): keys_view[i].as_nat == seps[i] and seps strictly sorted.
    assert(crate::bplus_tree::strictly_sorted(seps));
    assert forall|i: int, j: int| 0 <= i <= j < L::keys_view(node).len() implies
        (#[trigger] L::keys_view(node)[i].as_nat()) <= (#[trigger] L::keys_view(node)[j].as_nat()) by {
        // keys_view[i].as_nat == seps[i]; strictly_sorted gives seps[i] <= seps[j] for i <= j.
        assert(L::keys_view(node)[i].as_nat() == seps[i]);
        assert(L::keys_view(node)[j].as_nat() == seps[j]);
        if i < j {
            assert(seps[i] < seps[j]);
        }
    }
}

/// Leaf binding facts for an arbitrary bound leaf subtree (the descent's
/// landing node), the leaf analogue of [`lemma_inner_facts`]: the arena node is
/// a leaf, node-well-formed, its count is the key count, and its key view
/// projects to the ghost keys. (`tree_wf`'s leaf arm gives `node_wf` via the
/// iff.)
pub proof fn lemma_binds_leaf_facts<L: NodeLayout>(
    arena: Seq<L::Node>,
    id: nat,
    keys: Seq<nat>,
    h: nat,
)
    requires
        binds::<L>(arena, Tree::Leaf { id, keys }),
        crate::bplus_tree::tree_wf(Tree::Leaf { id, keys }, h, L::leaf_cap_spec(), L::key_cap_spec(), true),
    ensures
        id < arena.len(),
        L::is_leaf_spec(arena[id as int]),
        L::node_wf(arena[id as int]),
        L::count_spec(arena[id as int]) == keys.len(),
        forall|i: int| 0 <= i < keys.len() ==>
            (#[trigger] L::keys_view(arena[id as int])[i]).as_nat() == keys[i],
{
    let node = arena[id as int];
    assert(L::count_spec(node) == keys.len());  // binds leaf arm
    L::lemma_node_wf_iff(node);  // keys.len() <= leaf_cap ⟹ node_wf
}

// ===========================================================================
// B2: the leaf-link chain yields the in-order model.
//
// `leaf_links_to` (a `wf` clause) already pins the chain's SHAPE: walking `link`
// from the leftmost leaf visits exactly `tree_leaf_ids(t)` in order, NIL-
// terminated. B2 is the MODEL half: reading each visited leaf's keys (in chain
// order) and concatenating them yields `tree_keys(t)` — the sorted model (B1).
// So a client walking the chain enumerates the set in ascending order with no
// gaps or repeats. This is the soundness foundation the cursor (B3) stands on.
// ===========================================================================

/// The key sequence read by walking a list of leaf arena ids `lids` in order:
/// each leaf contributes `keys_view(arena[lid])` projected to nats. Pure spec
/// over the arena; `chain_keys(arena, tree_leaf_ids(t))` is what a chain walk
/// from `t`'s leftmost leaf reads (the ids being the chain by `leaf_links_to`).
pub open spec fn chain_keys<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>) -> Seq<nat>
    decreases lids.len()
{
    if lids.len() == 0 {
        Seq::empty()
    } else {
        leaf_word_keys::<L>(arena, lids[0]) + chain_keys::<L>(arena, lids.drop_first())
    }
}

/// One leaf's stored keys (at arena id `lid`) projected to nats: `keys_view`
/// mapped through `as_nat`. The per-leaf piece `chain_keys` concatenates.
pub open spec fn leaf_word_keys<L: NodeLayout>(arena: Seq<L::Node>, lid: nat) -> Seq<nat> {
    Seq::new(L::keys_view(arena[lid as int]).len(), |i: int| L::keys_view(arena[lid as int])[i].as_nat())
}

// ===========================================================================
// B3 support: map a (leaf, position-in-leaf) pair to a flat model index.
//
// The cursor's `(node, pos)` is the executable realization of a model index.
// `chain_offset(t, m)` is the number of model keys in leaves BEFORE chain-leaf
// `m` (the model analogue of `leaf_id_offset`); `lemma_model_index_at` then says
// model index `chain_offset(t,m) + p` is exactly leaf `m`'s `p`-th key. With B2
// (chain reading == model), this is what lets `key()` return `model[gidx]`.
// ===========================================================================

/// Model keys contributed by chain-leaves `0..m` (the count before leaf `m`).
/// The `tree_keys` analogue of `leaf_id_offset`, over the same in-order leaves.
pub open spec fn chain_offset<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>, m: int) -> nat
    decreases m
{
    if m <= 0 {
        0
    } else {
        chain_offset::<L>(arena, lids, m - 1) + leaf_word_keys::<L>(arena, lids[m - 1]).len()
    }
}

impl<K, L, S, const TRACK: bool> BPlusTreeSet<K, L, S, TRACK>
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
{
    /// The arena's abstract node sequence.
    pub open spec fn arena(&self) -> Seq<L::Node> {
        self.nodes.view()
    }

    /// The abstract model: the ghost tree's in-order key sequence.
    pub open spec fn model(&self) -> Seq<nat> {
        crate::bplus_tree::tree_keys(self.tree@)
    }

    /// Well-formedness. The arena is a valid `Vec`; the ghost root id matches
    /// `root`; the arena realizes the ghost tree (`binds`); the ghost tree is a
    /// structurally valid B+tree (`tree_wf` at its height, as root); the cached
    /// `nkeys` equals the model length; and every model value is in `K::id_bound`.
    ///
    /// The last clause (`model_bounded`) is the REFINEMENT the `K -> K::Index`
    /// storage coercion erases: a key is stored as its `Index` word (`u32`/`u64`),
    /// a type strictly wider than the id's valid range (`2^31`/`2^63`), so the
    /// type can no longer witness "this came from a real `K`". Production leaves
    /// this implicit and enforces it with a runtime `assert!(raw <= MAX_RAW)` in
    /// `DenseId::new`; here we make it an explicit, proven invariant — insert only
    /// ever adds `key.id_nat()`, which `lemma_id_nat_bounded` bounds — so the
    /// cursor's `key()` reconstructs the exact `K` (and production's assert would
    /// never fire / our mask is always a no-op).
    ///
    /// (Disjointness of subtree id-sets — the dynamic-frames separation — is a
    /// conjunct added at M3 when multi-node trees first arise; vacuous here.)
    /// The structural half of `wf`, factored as a free-standing predicate over an
    /// EXPLICIT `(arena, root_nat, tree, nkeys)` rather than `self`. Everything in
    /// `wf` except the inner Vec's own `nodes.wf()`. Lets `restore` state its
    /// snapshot precondition (the snapshot arena + the ghost tree live at the mark
    /// form a valid B+tree) and re-establish `self.wf()` after rolling the arena
    /// back, without duplicating the eight clauses.
    pub open spec fn tree_state_wf(arena: Seq<L::Node>, root_nat: nat, tree: Tree, nkeys: nat) -> bool {
        &&& crate::bplus_tree::tree_root_id(tree) == root_nat
        &&& binds::<L>(arena, tree)
        &&& crate::bplus_tree::tree_wf(
                tree,
                crate::bplus_tree::tree_height(tree),
                L::leaf_cap_spec(),
                L::key_cap_spec(),
                true,
            )
        &&& leaf_links_ok::<L>(arena, tree)
        &&& crate::bplus_tree::tree_disjoint(tree)
        &&& nkeys == crate::bplus_tree::tree_keys(tree).len()
        &&& model_bounded::<K>(crate::bplus_tree::tree_keys(tree))
        &&& arena.len() == crate::bplus_tree::node_count(tree)
        &&& arena.len() < <L::ArenaIdx as IndexLike>::max_nat()
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.nodes.wf()
        &&& Self::tree_state_wf(self.arena(), self.root.as_nat(), self.tree@, self.nkeys as nat)
    }

    /// Subtree well-formedness, the recursion's local invariant: `arena` realizes
    /// the ghost subtree `t` as a structurally valid B+tree of height `h` (non-
    /// root), with its last leaf linking to `succ` and its ids disjoint. The
    /// whole-tree `wf` is essentially `subtree_wf(arena, tree@, height, NIL,
    /// true)` plus the arena-`Vec` and `nkeys` bookkeeping. `insert_rec` consumes
    /// `subtree_wf` for the child it descends into and re-establishes it for the
    /// (one or two) subtrees it returns.
    pub open spec fn subtree_wf(
        arena: Seq<L::Node>,
        t: Tree,
        h: nat,
        succ: nat,
        is_root: bool,
    ) -> bool {
        &&& binds::<L>(arena, t)
        &&& crate::bplus_tree::tree_wf(t, h, L::leaf_cap_spec(), L::key_cap_spec(), is_root)
        &&& leaf_links_to::<L>(arena, t, succ)
        &&& crate::bplus_tree::tree_disjoint(t)
    }

    pub fn new() -> (t: Self)
        ensures t.wf(), t.model() == Seq::<nat>::empty(),
    {
        let mut nodes = SpVec::<
            L::Node,
            L::ArenaIdx,
            InlineStore<L::Node, L::ArenaIdx>,
            TRACK,
        >::new();
        // root index = current length (0), captured before the push.
        let root = nodes.len();
        let leaf = L::new_leaf();
        proof {
            // root.as_nat() == 0 (len of the empty arena).
            assert(nodes.view().len() == 0);
            assert(root.as_nat() == 0);
            // push needs view().len() + 1 < ArenaIdx::max_nat(); here len == 0, and
            // the layout guarantees leaf_cap < max_nat (>= 1), so 0 + 1 < max_nat.
            L::lemma_arena_capacity();
            assert(L::leaf_cap_spec() < <L::ArenaIdx as IndexLike>::max_nat());
            assert(0 + 1 < <L::ArenaIdx as IndexLike>::max_nat());
        }
        nodes.push(leaf);

        let ghost gtree = Tree::Leaf { id: 0, keys: Seq::<nat>::empty() };
        let t = BPlusTreeSet {
            nodes,
            root,
            nkeys: 0,
            tree: Ghost(gtree),
            _k: core::marker::PhantomData,
            _s: core::marker::PhantomData,
        };
        proof {
            // After push onto the empty arena, arena() == [leaf].
            assert(t.arena().len() == 1);
            assert(t.arena()[0] == leaf);
            // binds(arena, Leaf{0, []}): id 0 in range, leaf, count 0, keys empty.
            assert(L::is_leaf_spec(t.arena()[0]));
            assert(L::count_spec(t.arena()[0]) == 0);
            assert(crate::bplus_tree::tree_keys(t.tree@) =~= Seq::<nat>::empty());
            // crate::bplus_tree::tree_wf(Leaf{0,[]}, 0, cap, key_cap, true): h==0, len 0 <= cap, sorted.
            assert(crate::bplus_tree::tree_height(t.tree@) == 0);
            assert(t.model() =~= Seq::<nat>::empty());
        }
        t
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.model().len() == 0),
    {
        // nkeys is the cached model length (wf clause), valid for any tree shape.
        self.nkeys == 0
    }

    pub fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.model().len(),
    {
        self.nkeys
    }

    /// Membership. Decides `key ∈ model`, by a root-to-leaf descent.
    ///
    /// At each internal node the descent follows child `cp = find_gt(seps,
    /// key)`; `tree_wf`'s cross-node ordering (`lemma_descent_step`) makes that
    /// the unique child whose key space could hold `key`, so membership in the
    /// whole tree reduces to membership in that subtree. The descent carries a
    /// ghost subtree `cur` the current arena node binds, with the loop invariant
    /// `tree_contains(self.tree@, key) <==> tree_contains(cur, key)`, decreasing
    /// on `tree_height(cur)`. At the leaf it scans for the key
    /// (`lemma_leaf_search_membership` justifies the final equality test). No
    /// leaf-root precondition: this is the M4 generalization of M2b.
    pub fn contains(&self, key: K) -> (b: bool)
        requires self.wf(),
        ensures b == self.model().contains(key.id_nat()),
    {
        let kw: L::Word = key.to_index();  // word with as_nat == key.id_nat()
        let ghost k = key.id_nat();

        let mut idx = self.root;
        let ghost cur = self.tree@;

        // Descent: walk internal nodes following the find_gt child; at a leaf,
        // scan and return. The membership invariant ties the whole tree's
        // membership to the current subtree's.
        loop
            invariant
                self.wf(),
                kw.as_nat() == k,
                k == key.id_nat(),
                idx.as_nat() == crate::bplus_tree::tree_root_id(cur),
                binds::<L>(self.arena(), cur),
                crate::bplus_tree::tree_wf(
                    cur, crate::bplus_tree::tree_height(cur),
                    L::leaf_cap_spec(), L::key_cap_spec(), true),
                crate::bplus_tree::tree_contains(self.tree@, k)
                    <==> crate::bplus_tree::tree_contains(cur, k),
            decreases crate::bplus_tree::tree_height(cur),
        {
            let node = self.nodes.get(idx);
            proof { assert(self.arena()[idx.as_nat() as int] == node); }

            if L::is_leaf(&node) {
                // Leaf: scan its keys, return membership.
                let ghost gkeys = crate::bplus_tree::tree_keys(cur);
                proof {
                    match cur {
                        Tree::Leaf { id, keys } => {
                            assert(gkeys == keys);
                            lemma_binds_leaf_facts::<L>(self.arena(),
                                idx.as_nat(), keys, crate::bplus_tree::tree_height(cur));
                        }
                        Tree::Inner { .. } => { assert(false); }
                    }
                }
                let n = L::count(&node);
                proof { assert(gkeys.len() == n as nat); assert(L::node_wf(node)); }

                let mut i: usize = 0;
                while i < n
                    invariant
                        0 <= i <= n,
                        n as nat == L::count_spec(node),
                        node == self.arena()[idx.as_nat() as int],
                        L::node_wf(node),
                        L::is_leaf_spec(node),
                        gkeys.len() == n as nat,
                        kw.as_nat() == k,
                        k == key.id_nat(),
                        gkeys == crate::bplus_tree::tree_keys(cur),
                        forall|j: int| 0 <= j < gkeys.len() ==>
                            (#[trigger] L::keys_view(node)[j]).as_nat() == gkeys[j],
                        forall|j: int| 0 <= j < i ==> gkeys[j] != k,
                        crate::bplus_tree::tree_contains(self.tree@, k)
                            <==> crate::bplus_tree::tree_contains(cur, k),
                        self.model() == crate::bplus_tree::tree_keys(self.tree@),
                    decreases n - i,
                {
                    let ki: L::Word = L::key(&node, i);
                    let le1 = ki.le(kw);
                    let le2 = kw.le(ki);
                    proof {
                        <L::Word as IndexLike>::lemma_order_is_as_nat(ki, kw);
                        <L::Word as IndexLike>::lemma_order_is_as_nat(kw, ki);
                        assert(ki == L::keys_view(node)[i as int]);
                        assert(ki.as_nat() == gkeys[i as int]);
                    }
                    if le1 && le2 {
                        proof {
                            assert(gkeys[i as int] == k);
                            assert(crate::bplus_tree::tree_contains(cur, k));
                            // bridge to the model: model == tree_keys(self.tree@) and
                            // tree_contains(self.tree@,k) == that.contains(k).
                            assert(crate::bplus_tree::tree_contains(self.tree@, k));
                            // tree_contains(t,k) == tree_keys(t).contains(k) == model.contains(k).
                            assert(crate::bplus_tree::tree_contains(self.tree@, k)
                                == crate::bplus_tree::tree_keys(self.tree@).contains(k));
                            assert(crate::bplus_tree::tree_keys(self.tree@).contains(k));
                            assert(self.model() == crate::bplus_tree::tree_keys(self.tree@));
                            assert(self.model().contains(k));
                            assert(k == key.id_nat());
                            assert(self.model().contains(key.id_nat()));
                        }
                        return true;
                    }
                    proof { assert(gkeys[i as int] != k); }
                    i = i + 1;
                }
                proof {
                    assert(forall|j: int| 0 <= j < gkeys.len() ==> gkeys[j] != k);
                    assert(!gkeys.contains(k));
                    assert(!crate::bplus_tree::tree_contains(cur, k));
                    assert(!crate::bplus_tree::tree_contains(self.tree@, k));
                    assert(!self.model().contains(key.id_nat()));
                }
                return false;
            }

            // Internal node: scan separators for cp = find_gt(seps, key).
            let ghost gseps = match cur {
                Tree::Inner { seps, .. } => seps,
                Tree::Leaf { .. } => Seq::<nat>::empty(),
            };
            let ghost gkids = match cur {
                Tree::Inner { kids, .. } => kids,
                Tree::Leaf { .. } => Seq::<Tree>::empty(),
            };
            let ghost gid = crate::bplus_tree::tree_root_id(cur);
            let ghost gh = crate::bplus_tree::tree_height(cur);
            proof {
                // cur is Inner (arena node is not a leaf, binds is consistent).
                match cur {
                    Tree::Inner { id, seps, kids } => {
                        assert(id == gid && seps == gseps && kids == gkids);
                    }
                    Tree::Leaf { id, .. } => { assert(false); }
                }
                lemma_inner_facts::<L>(self.arena(), gid, gseps, gkids, gh);
            }
            let n = L::count(&node);
            proof {
                assert(node == self.arena()[idx.as_nat() as int]);
                assert(n as nat == gseps.len());
                assert(n as nat == L::count_spec(node));
            }

            let mut cp: usize = 0;
            let mut stop = false;
            while !stop && cp < n
                invariant
                    0 <= cp <= n,
                    n as nat == gseps.len(),
                    n as nat == L::count_spec(node),
                    node == self.arena()[idx.as_nat() as int],
                    L::node_wf(node),
                    !L::is_leaf_spec(node),
                    kw.as_nat() == k,
                    forall|i: int| 0 <= i < gseps.len() ==>
                        (#[trigger] L::keys_view(node)[i]).as_nat() == gseps[i],
                    forall|j: int| 0 <= j < cp ==> gseps[j] <= k,
                    stop ==> (cp < n && k < gseps[cp as int]),
                decreases (if stop { 0int } else { (n - cp) as int + 1 }),
            {
                let ki: L::Word = L::key(&node, cp);
                let le = ki.le(kw);  // seps[cp] <= key ?
                proof {
                    <L::Word as IndexLike>::lemma_order_is_as_nat(ki, kw);
                    assert(ki == L::keys_view(node)[cp as int]);
                    assert(ki.as_nat() == gseps[cp as int]);
                }
                if le {
                    proof { assert(gseps[cp as int] <= k); }
                    cp = cp + 1;
                } else {
                    proof { assert(k < gseps[cp as int]); }
                    stop = true;
                }
            }
            // Establish the find_gt characterization: [0..cp) <= k, [cp..) > k.
            proof {
                assert(crate::bplus_tree::strictly_sorted(gseps));
                assert forall|i: int| cp <= i < gseps.len() implies k < gseps[i] by {
                    if stop {
                        // k < gseps[cp] <= gseps[i] by strict sortedness (cp <= i).
                        if cp < i { assert(gseps[cp as int] < gseps[i]); }
                    }
                    // if !stop then cp == n == gseps.len(), range empty.
                }
                crate::bplus_tree::lemma_descent_step(gid, gseps, gkids, k, cp as int,
                    gh, L::leaf_cap_spec(), L::key_cap_spec(), true);
                lemma_inner_binds_child::<L>(self.arena(), gid, gseps, gkids, cp as int);
                // child wf at h-1 (non-root), relaxed to root; its height is h-1.
                crate::bplus_tree::lemma_forest_wf_at(gkids, (gh - 1) as nat,
                    L::leaf_cap_spec(), L::key_cap_spec(), cp as int);
                crate::bplus_tree::lemma_tree_wf_relax_root(gkids[cp as int],
                    (gh - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec());
                crate::bplus_tree::lemma_tree_wf_height(gkids[cp as int],
                    (gh - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), true);
            }

            let child = L::child(&node, cp);
            proof {
                assert(child.as_nat() == L::child_view(node, cp as int));
            }
            idx = child;
            proof { cur = gkids[cp as int]; }
        }
    }
}

} // verus!
