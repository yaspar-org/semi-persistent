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
pub open(crate) spec fn binds<L: NodeLayout>(arena: Seq<L::Node>, t: Tree) -> bool
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
pub open(crate) spec fn forest_binds_l<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>) -> bool
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
pub open(crate) spec fn nil_link<L: NodeLayout>() -> nat {
    (<L::ArenaIdx as IndexLike>::max_nat() - 1) as nat
}

/// The seek target index: the number of model keys strictly below `t`. For a
/// strictly-sorted model this is the position of the first key `>= t` (leapfrog's
/// `seek` semantics: land on the least element not below the target). Defined as
/// a count so it is monotone and total even when `t` is absent.
pub open(crate) spec fn seek_target_idx(model: Seq<nat>, t: nat) -> int
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
pub open(crate) spec fn model_bounded<K: DenseId>(model: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < model.len() ==> #[trigger] model[i] < K::id_bound()
}

/// Subtree-relative leaf-link consistency: within `t`'s in-order leaf sequence
/// `lids`, each leaf links to the next, and the *last* leaf links to `succ` (the
/// subtree's global successor — the first leaf of whatever follows `t`, or NIL
/// if `t` is the whole tree). This is the form the recursion needs: a subtree's
/// last leaf points *out* of the subtree, so the predicate must be parameterized
/// by the successor rather than hard-coding NIL.
pub open(crate) spec fn leaf_links_to<L: NodeLayout>(arena: Seq<L::Node>, t: Tree, succ: nat) -> bool {
    let lids = crate::bplus_tree::tree_leaf_ids(t);
    forall|p: int| 0 <= p < lids.len() ==>
        #[trigger] L::link_view(arena[lids[p] as int]) == (
            if p + 1 < lids.len() { lids[p + 1] } else { succ }
        )
}

/// The chain condition over a BARE leaf-id sequence: `lids[p]`'s slot links to
/// `lids[p + 1]`, and the last links to `succ`. [`leaf_links_to`] is exactly this
/// at `lids == tree_leaf_ids(t)`.
///
/// Naming it separately is what makes the bulk loader's levels free: EVERY level
/// of a tree has the same in-order leaf sequence, and the links live in leaf
/// slots that the internal levels never touch, so one chain fact serves all of
/// them (see [`lemma_forest_links_from_chain`]). Threading the recursive
/// `forest_links_to` up level by level would instead need each level's
/// successor-of-the-last-group before that group exists.
pub open(crate) spec fn chain_links_to<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>, succ: nat) -> bool {
    forall|p: int| 0 <= p < lids.len() ==>
        #[trigger] L::link_view(arena[lids[p] as int]) == (
            if p + 1 < lids.len() { lids[p + 1] } else { succ }
        )
}

/// Leaf-link consistency (clause 5) for the whole tree: the chain ends at NIL.
/// The `wf`-level instance of [`leaf_links_to`] with `succ == nil_link`. Bound to
/// the tree (single source of truth), so the sorted cursor's walk is sound by
/// `tree_wf`'s cross-node ordering, not by an independent assumption.
pub open(crate) spec fn leaf_links_ok<L: NodeLayout>(arena: Seq<L::Node>, t: Tree) -> bool {
    leaf_links_to::<L>(arena, t, nil_link::<L>())
}

/// Compositional leaf-links over a forest: child `i`'s chain ends at child
/// `i+1`'s first leaf (or `succ` for the last child). The decomposition of an
/// internal node's `leaf_links_to` into its children's — what lets the recursion
/// re-assemble the parent's chain from the (updated) child chains.
pub open(crate) spec fn forest_links_to<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>, succ: nat) -> bool
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
pub struct BPlusTreeSet<K, L = crate::bplus_layout::Layout64U32, S = crate::bplus_search::BinarySearch, const TRACK: bool = true>
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
{
    pub(crate) nodes: SpVec<L::Node, L::ArenaIdx, InlineStore<L::Node, L::ArenaIdx>, TRACK>,
    /// Arena index of the root node.
    pub(crate) root: L::ArenaIdx,
    /// Number of keys (cached; equals `model().len()`). Mirrors production's
    /// header `nkeys`.
    pub(crate) nkeys: usize,
    /// Ghost recursive model.
    pub(crate) tree: Ghost<Tree>,
    /// Arena index of the rightmost leaf, mirroring production's header
    /// `last_leaf`. Enables the O(1) append fast path: when the new key extends
    /// this leaf and it has room, `insert` writes one slot and returns, skipping
    /// the root-to-leaf descent entirely. `wf` pins it to the ghost tree's
    /// rightmost leaf (`last_leaf_ok`), so the fast path needs no runtime check
    /// that the cache is honest.
    pub(crate) last_leaf: L::ArenaIdx,
    /// Exec header archive (plan Phase 7): `(root.as_usize(), nkeys, last_leaf)`
    /// at each mark, parallel to the arena vec's snapshot stack. `restore`
    /// recovers the header from HERE — not from the token — so forged token
    /// header fields are inert, and no caller-supplied ghost tree is needed.
    /// (Production keeps the header in a meta `VecP` slot rolled back by the
    /// vec protocol; this is the same idea with a plain stack.)
    pub(crate) header_archive: std::vec::Vec<(usize, usize, usize)>,
    /// Ghost tree archive (plan Phase 7), parallel to `header_archive`.
    pub(crate) tree_snapshots: Ghost<Seq<Tree>>,
    pub(crate) _k: core::marker::PhantomData<K>,
    pub(crate) _s: core::marker::PhantomData<S>,
}

/// Forest companion of [`lemma_inner_binds_child`]: project `forest_binds_l` to
/// one child (the arena binds each child subtree). Mirrors `lemma_forest_wf_at`.
pub(crate) proof fn lemma_forest_binds_at<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>, m: int)
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
pub(crate) proof fn lemma_inner_binds_child<L: NodeLayout>(
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
pub(crate) proof fn lemma_inner_facts<L: NodeLayout>(
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
pub(crate) proof fn lemma_binds_leaf_facts<L: NodeLayout>(
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
pub open(crate) spec fn chain_keys<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>) -> Seq<nat>
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
pub open(crate) spec fn leaf_word_keys<L: NodeLayout>(arena: Seq<L::Node>, lid: nat) -> Seq<nat> {
    Seq::new(L::keys_view(arena[lid as int]).len(), |i: int| L::keys_view(arena[lid as int])[i].as_nat())
}

/// The same projection applied to a NODE rather than an arena slot. What the
/// batched append's loop invariant needs: it grows a *local* `L::Node` across
/// many iterations, so it must state its key view in nats (`Seq<nat>`, the model
/// currency) without going through an arena index. `leaf_word_keys(arena, lid) ==
/// node_word_keys(arena[lid])` by definition, which is how the two connect at
/// the single `set_index`.
pub open(crate) spec fn node_word_keys<L: NodeLayout>(n: L::Node) -> Seq<nat> {
    Seq::new(L::keys_view(n).len(), |i: int| L::keys_view(n)[i].as_nat())
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
pub open(crate) spec fn chain_offset<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>, m: int) -> nat
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
    pub open(crate) spec fn arena(&self) -> Seq<L::Node> {
        self.nodes.view()
    }

    /// The abstract model: the ghost tree's in-order key sequence.
    pub open(crate) spec fn model(&self) -> Seq<nat> {
        crate::bplus_tree::tree_keys(self.tree@)
    }

    // Spec twins (privacy closeout): all fields are `pub(crate)`, so public
    // contracts phrase the tree's coordinates through these.

    /// The ghost tree.
    pub open(crate) spec fn tree_spec(&self) -> Tree {
        self.tree@
    }

    /// The exec root arena index.
    pub open(crate) spec fn root_spec(&self) -> L::ArenaIdx {
        self.root
    }

    /// The cached key count.
    pub open(crate) spec fn nkeys_spec(&self) -> nat {
        self.nkeys as nat
    }

    /// Arena frame-stack depth.
    pub open(crate) spec fn arena_depth_spec(&self) -> nat {
        self.nodes.depth_spec()
    }

    /// Arena lifetime restore count.
    pub open(crate) spec fn arena_fork_count_spec(&self) -> nat {
        self.nodes.fork_count_spec()
    }

    /// Arena snapshot stack.
    pub open(crate) spec fn arena_snapshots_view(&self) -> Seq<Seq<L::Node>> {
        self.nodes.snapshots_view()
    }

    /// Ghost-tree snapshot stack (Phase 7 archive).
    pub open(crate) spec fn tree_snapshots_spec(&self) -> Seq<Tree> {
        self.tree_snapshots@
    }

    /// Token validity, delegated to the arena component.
    pub open(crate) spec fn is_token_valid_spec(&self, token: BPlusToken) -> bool {
        self.nodes.is_token_valid_spec(token.nodes)
    }

    /// "Restorable now", delegated to the arena component.
    pub open(crate) spec fn is_restorable_spec(&self, token: BPlusToken) -> bool {
        self.nodes.is_restorable_spec(token.nodes)
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
    pub open(crate) spec fn tree_state_wf(arena: Seq<L::Node>, root_nat: nat, tree: Tree, nkeys: nat) -> bool {
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

    /// `last_leaf` honestly caches the ghost tree's rightmost leaf. Making this a
    /// `wf` clause (rather than checking at runtime) is what lets the fast path
    /// trust the field: `lemma_last_leaf_id` then identifies it with the last
    /// entry of the in-order leaf chain, which is the node `tree_append_last`
    /// writes to.
    pub open(crate) spec fn last_leaf_ok(&self) -> bool {
        self.last_leaf.as_nat() == crate::bplus_tree::last_leaf_id(self.tree@)
    }

    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.nodes.wf()
        &&& Self::tree_state_wf(self.arena(), self.root.as_nat(), self.tree@, self.nkeys as nat)
        &&& self.last_leaf_ok()
        // Phase 7 archive agreement (opaque, keyed on the arena snapshot
        // stack — see circular_list's wf comment for the matching-loop
        // rationale): each archived (header, ghost tree) pair describes its
        // archived arena snapshot.
        &&& tree_archive_agrees::<K, L, S, TRACK>(
                self.header_archive@, self.tree_snapshots@, self.nodes.snapshots_view())
    }

    /// Subtree well-formedness, the recursion's local invariant: `arena` realizes
    /// the ghost subtree `t` as a structurally valid B+tree of height `h` (non-
    /// root), with its last leaf linking to `succ` and its ids disjoint. The
    /// whole-tree `wf` is essentially `subtree_wf(arena, tree@, height, NIL,
    /// true)` plus the arena-`Vec` and `nkeys` bookkeeping. `insert_rec` consumes
    /// `subtree_wf` for the child it descends into and re-establishes it for the
    /// (one or two) subtrees it returns.
    pub open(crate) spec fn subtree_wf(
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
            // the single root leaf IS the rightmost leaf (no nil case to handle:
            // the empty tree still has one, empty, leaf at index 0).
            last_leaf: root,
            tree: Ghost(gtree),
            header_archive: std::vec::Vec::new(),
            tree_snapshots: Ghost(Seq::empty()),
            _k: core::marker::PhantomData,
            _s: core::marker::PhantomData,
        };
        proof {
            reveal(tree_archive_agrees);
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

    /// How many more `restore`s this tree can accept before the arena's
    /// fork-history branch counter saturates `u32` (saturating at 0). Delegates
    /// to the inner arena `Vec`, whose fork history governs token validity.
    pub fn restores_remaining(&self) -> (r: usize)
        requires self.wf(),
        ensures
            self.arena_fork_count_spec() < u32::MAX ==>
                r as nat == (u32::MAX - self.arena_fork_count_spec()) as nat,
            self.arena_fork_count_spec() >= u32::MAX ==> r == 0,
    {
        self.nodes.restores_remaining()
    }

    /// Exec `ArenaIdx` for an in-range `usize`. `try_from_usize` succeeds exactly
    /// when `v < max_nat`, which every caller here proves; the `None` arm is
    /// therefore dead and routed through the runtime guard rather than a panic.
    #[inline(always)]
    fn arena_idx_from(v: usize) -> (i: L::ArenaIdx)
        requires (v as nat) < <L::ArenaIdx as IndexLike>::max_nat(),
        ensures i.as_nat() == v as nat,
    {
        match <L::ArenaIdx as IndexLike>::try_from_usize(v) {
            Some(i) => i,
            None => {
                // Dead for a verified caller (`requires` rules it out); the guard
                // traps an unverified one, matching `restore`'s protocol.
                proof { assert(false); }
                crate::guard::check_precondition(
                    false,
                    "BPlusTreeSet: arena index out of range",
                );
                <L::ArenaIdx as IndexLike>::min()
            }
        }
    }

    /// The NIL leaf-link sentinel as an exec index (`max_nat - 1`, matching
    /// [`nil_link`]). Obtained from `new_leaf`, whose contract already pins its
    /// link to NIL, so no new trusted primitive is needed for it.
    #[inline(always)]
    fn nil_arena_idx() -> (i: L::ArenaIdx)
        ensures i.as_nat() == nil_link::<L>(),
    {
        let probe = L::new_leaf();
        L::link(&probe)
    }

    /// The number of groups a balanced partition of `n` items into groups of at
    /// most `cap` uses: `ceil(n / cap)`. Split out so the exec side and the
    /// proof obligation (`lemma_balanced_group_min`) name the same quantity.
    #[inline(always)]
    fn bulk_groups(n: usize, cap: usize) -> (m: usize)
        requires n >= 1, cap >= 1,
        ensures
            m >= 1,
            cap * (m - 1) < n,
            n <= cap * m,
            m <= n,
    {
        // `div_ceil` spelled as quotient-plus-remainder-bit rather than
        // `(n + cap - 1) / cap`: the latter needs `n + cap <= usize::MAX`, which
        // no layout law provides (`leaf_cap` is bounded by the ARENA index range,
        // not by `usize`), and the driver would have nowhere to get it from.
        let q = n / cap;
        let r = n % cap;
        proof {
            // `q * cap + r == n` with `r < cap`, so `q <= n` and (when `r > 0`)
            // `q < n` -- which is what makes `q + 1` below overflow-free.
            assert(cap * q + r == n) by (nonlinear_arith)
                requires q == n / cap, r == n % cap, cap >= 1;
            assert(r < cap) by (nonlinear_arith) requires r == n % cap, cap >= 1;
            assert(q <= n) by (nonlinear_arith) requires cap * q + r == n, cap >= 1, r >= 0;
            if r > 0 {
                assert(q < n) by (nonlinear_arith) requires cap * q + r == n, cap >= 1, r > 0;
            }
        }
        let m = if r == 0 { q } else { q + 1 };
        proof {
            // Both bounds, in each arm:
            //   r == 0: n == cap * q, so `n <= cap * m` is equality and
            //           `cap * (m - 1) == n - cap < n`.
            //   r > 0:  n == cap * q + r <= cap * (q + 1) since `r <= cap`, and
            //           `cap * (m - 1) == n - r < n`.
            assert(cap * q + r == n);
            if r == 0 {
                assert(cap * (m - 1) == cap * q - cap) by (nonlinear_arith)
                    requires m == q, cap >= 1;
                // `cap * q == n >= 1` forces `q >= 1` (at `q == 0` the product is 0).
                assert(q >= 1) by (nonlinear_arith)
                    requires cap * q + r == n, r == 0, n >= 1, cap >= 1;
            } else {
                assert(cap * m == cap * q + cap) by (nonlinear_arith) requires m == q + 1;
                assert(cap * (m - 1) == cap * q) by (nonlinear_arith) requires m == q + 1;
                assert(m <= n) by (nonlinear_arith) requires m == q + 1, q < n;
            }
        }
        m
    }

    /// Fill one fresh leaf with `keys[at .. at + take]`, in order. The bulk
    /// loader's per-leaf primitive: ONE local node, `take` slot writes, no arena
    /// traffic — the caller pushes the finished node once.
    ///
    /// `link` becomes the finished leaf's forward chain pointer (the next leaf's
    /// arena id, or NIL for the last), so the chain is built in this single pass.
    ///
    /// Each `leaf_insert_at` targets position `count`, i.e. the current end, so it
    /// is a push and never shifts. Priced against production's per-leaf
    /// `copy_from_slice`, this loop is 0.28-0.60 ns/key while production's whole
    /// `from_sorted` costs 0.73 ns/key — production pays a per-key `key_to_word`
    /// conversion pass into a scratch `Vec` before its memcpy, and this fuses the
    /// conversion into the fill, so no bulk-copy primitive is needed to match it.
    fn bulk_fill_leaf(keys: &[K], at: usize, take: usize, link: L::ArenaIdx) -> (node: L::Node)
        requires
            take <= L::leaf_cap_spec(),
            at + take <= keys@.len(),
            keys@.len() <= usize::MAX,
        ensures
            L::is_leaf_spec(node),
            L::node_wf(node),
            L::count_spec(node) == take,
            L::link_view(node) == link.as_nat(),
            node_word_keys::<L>(node)
                == Seq::new(take as nat, |i: int| keys@[at + i].id_nat()),
            // `model_bounded`'s per-key obligation, collected here because
            // `lemma_id_nat_bounded` needs the exec key, which only exists in
            // this loop (the same reason `fast_append` collects it inline).
            forall|i: int| 0 <= i < take ==> #[trigger] keys@[at + i].id_nat() < K::id_bound(),
    {
        let mut node = L::new_leaf();
        proof {
            L::lemma_keys_view_len(node);
            assert(node_word_keys::<L>(node) =~= Seq::new(0nat, |i: int| keys@[at + i].id_nat()));
        }
        let mut j: usize = 0;
        while j < take
            invariant
                take <= L::leaf_cap_spec(),
                at + take <= keys@.len(),
                keys@.len() <= usize::MAX,
                0 <= j <= take,
                L::is_leaf_spec(node),
                L::node_wf(node),
                L::count_spec(node) == j,
                L::link_view(node) == nil_link::<L>(),
                node_word_keys::<L>(node)
                    == Seq::new(j as nat, |i: int| keys@[at + i].id_nat()),
                forall|i: int| 0 <= i < j ==> #[trigger] keys@[at + i].id_nat() < K::id_bound(),
            decreases take - j,
        {
            // `slice_get`, not `keys[at + j]`: the index bound is the loop
            // invariant's (`at + take <= keys.len()`, `j < take`), so the emitted
            // `cmp/jae panic` was dead code in the loader's innermost loop.
            let k: K = crate::bplus_layout::slice_get(keys, at + j);
            proof { k.lemma_id_nat_bounded(); }
            let kw: L::Word = k.to_index();
            let ghost pre = node_word_keys::<L>(node);
            let ghost pre_view = L::keys_view(node);
            proof { L::lemma_keys_view_len(node); }
            // `leaf_push`, not `leaf_insert_at(.., j, ..)`: position == count here,
            // so the shift is empty — but only the specialized signature lets LLVM
            // see that and drop `arr_shift_up`'s length dispatch. See `leaf_push`.
            L::leaf_push(&mut node, kw);
            proof {
                L::lemma_keys_view_len(node);
                let want = Seq::new((j + 1) as nat, |i: int| keys@[at + i].id_nat());
                assert(L::keys_view(node) == pre_view.push(kw));
                assert(pre_view.push(kw) == pre_view.insert(j as int, kw));
                assert(node_word_keys::<L>(node) =~= want) by {
                    let got = node_word_keys::<L>(node);
                    assert(got.len() == j + 1);
                    assert forall|i: int| 0 <= i < got.len() implies got[i] == want[i] by {
                        if i < j as int {
                            // insert at the end leaves every earlier slot put.
                            assert(L::keys_view(node)[i] == pre_view[i]);
                            assert(got[i] == pre[i]);
                        } else {
                            assert(L::keys_view(node)[i] == kw);
                        }
                    }
                }
            }
            j = j + 1;
        }
        // The chain, written HERE rather than in a second pass: the loader knows
        // each leaf's successor id before it fills the leaf (a level's ids are
        // contiguous), so production's separate link pass — one extra whole-node
        // read plus write per leaf — is unnecessary.
        L::set_link(&mut node, link);
        node
    }

    /// The bulk loader's ARENA BUDGET, proved before any push: building `n` keys
    /// bottom-up allocates at most `2 * ceil(n / cap) + 1` nodes, which fits the
    /// arena index type.
    ///
    /// The argument is the same one `lemma_arena_never_overflows` makes for the
    /// insert path, run forwards instead of backwards: the input is strictly
    /// sorted and every key is `< id_bound`, so `n <= id_bound == max_nat / 2`;
    /// the leaf level holds `ceil(n / cap) <= n / 7 + 1` nodes (the occupancy
    /// floor `(cap+1)/2 >= 7` from M6, and the balanced partition meets it); and
    /// each level above is at most half the one below, so the levels sum to under
    /// twice the leaf level.
    ///
    /// Needed BEFORE the build because `SpVec::push` and `arena_idx_from` demand
    /// in-range indices as preconditions — there is no "grow and check" path.
    pub(crate) proof fn lemma_bulk_arena_budget(keys: Seq<K>, n: nat, cap: nat, m: nat)
        requires
            K::is_bit_stealing(),
            n == keys.len(),
            n >= 1,
            cap == L::leaf_cap_spec(),
            cap * (m - 1) < n,
            n <= cap * m,
            m >= 1,
            forall|i: int, j: int| 0 <= i < j < keys.len()
                ==> (#[trigger] keys[i]).id_nat() < (#[trigger] keys[j]).id_nat(),
            forall|i: int| 0 <= i < keys.len() ==> #[trigger] keys[i].id_nat() < K::id_bound(),
        ensures
            2 * m + 3 < <L::ArenaIdx as IndexLike>::max_nat(),
            // Also exported: the occupancy floor itself. The driver needs it to
            // keep its running level offsets inside a `usize` (the arena-index
            // budget above bounds them by `max_nat`, which for a `usize` arena is
            // `usize::MAX + 1` — one too many).
            m >= 2 ==> 7 * m <= n,
    {
        let mx = <L::ArenaIdx as IndexLike>::max_nat();
        let idb = K::id_bound();
        let lmin = (cap + 1) / 2;

        // `id_bound * 2 == ArenaIdx::max_nat` (the id steals a bit and `Word ==
        // K::Index` has the arena index's width), and the M6 geometry facts.
        K::lemma_id_bound_word_relation();
        L::lemma_word_arena_same_width();
        assert(idb * 2 == mx);
        L::lemma_capacity_headroom(idb);
        assert(lmin >= 7);
        assert(mx >= 16);

        // `n <= id_bound`: the input is strictly sorted with every key `< id_bound`,
        // so it is a subset of `[0, id_bound)` listed in order.
        let ids = Seq::new(n, |i: int| keys[i].id_nat());
        assert(crate::bplus_tree::strictly_sorted(ids));
        crate::bplus_tree::lemma_sorted_bounded_len(ids, idb);
        assert(n <= idb);

        // `m <= n / lmin + 1`: the balanced partition gives every group `>= lmin`
        // keys (`lemma_balanced_group_min` at `m >= 2`; `m == 1` is immediate), so
        // `lmin * m <= n + lmin`.
        if m >= 2 {
            crate::bplus_tree::lemma_balanced_group_min(n, cap, m);
            let q = n / m;
            assert(q >= lmin);
            assert(m * q <= n) by (nonlinear_arith) requires q == n / m, m >= 1, n >= 0;
            assert(m * lmin <= m * q) by (nonlinear_arith) requires q >= lmin, m >= 1;
            assert(m * lmin <= n);
            assert(7 * m <= m * lmin) by (nonlinear_arith) requires lmin >= 7, m >= 0;
            assert(7 * m <= n);
        } else {
            assert(m == 1);
            assert(7 * m == 7);
        }

        // `2 * m + 3 < mx`: from `7 * m <= max(n, 7)` and `2 * n <= 2 * idb == mx`.
        //   m >= 2:  2*m + 3 <= (2/7)*n + 3, and 2*n <= mx with mx >= 16.
        //   m == 1:  5 < 16 <= mx.
        if m >= 2 {
            assert(7 * m <= n);
            assert(n <= idb);
            assert(7 * m <= idb);
            // 2*m + 3 < idb*2 == mx: from 7m <= idb, 14m <= 2*idb == mx, and
            // 2m + 3 < 14m whenever m >= 1 (12m > 3).
            assert(14 * m <= 2 * idb) by (nonlinear_arith) requires 7 * m <= idb;
            assert(14 * m <= mx);
            assert(2 * m + 3 < 14 * m) by (nonlinear_arith) requires m >= 2;
        } else {
            assert(2 * m + 3 == 5);
        }
    }

    /// Build one internal node over the CONTIGUOUS child run
    /// `[lo + ci, lo + ci + take)`, with separators taken from `firsts`.
    ///
    /// `firsts[q]` is child `q`'s smallest key, recorded by the level below. That
    /// is the whole reason this needs no tree descent: production's `from_sorted`
    /// calls `first_key_word` per separator, which walks child-0 pointers down to
    /// a leaf (O(height) node reads each); carrying one word per node makes it a
    /// single array read. Separator `i` is child `i + 1`'s first key — the
    /// [`crate::bplus_tree::bulk_seps`] convention, which is what makes both of
    /// `tree_wf`'s cross-node ordering clauses fall out of adjacent-pairwise
    /// ordering with no search.
    fn bulk_fill_internal(
        lo: usize,
        ci: usize,
        take: usize,
        firsts: &[L::Word],
    ) -> (node: L::Node)
        requires
            2 <= take <= L::key_cap_spec() + 1,
            ci + take <= firsts@.len(),
            // every child id is representable (the caller's arena headroom).
            ((lo + ci + take) as nat) <= <L::ArenaIdx as IndexLike>::max_nat(),
            lo + ci + take <= usize::MAX,
        ensures
            !L::is_leaf_spec(node),
            L::node_wf(node),
            L::count_spec(node) == take - 1,
            L::keys_view(node) == Seq::new((take - 1) as nat, |i: int| firsts@[ci + 1 + i]),
            forall|i: int| 0 <= i < take ==>
                #[trigger] L::child_view(node, i) == (lo + ci + i) as nat,
    {
        proof { L::lemma_arena_capacity(); }
        let c0 = Self::arena_idx_from(lo + ci);
        let c1 = Self::arena_idx_from(lo + ci + 1);
        let mut node = L::new_internal2(firsts[ci + 1], c0, c1);
        proof {
            assert(L::keys_view(node) =~= Seq::new(1nat, |i: int| firsts@[ci + 1 + i]));
        }
        let mut k: usize = 2;
        while k < take
            invariant
                2 <= take <= L::key_cap_spec() + 1,
                2 <= k <= take,
                ci + take <= firsts@.len(),
                ((lo + ci + take) as nat) <= <L::ArenaIdx as IndexLike>::max_nat(),
                lo + ci + take <= usize::MAX,
                !L::is_leaf_spec(node),
                L::node_wf(node),
                L::count_spec(node) == k - 1,
                L::keys_view(node) == Seq::new((k - 1) as nat, |i: int| firsts@[ci + 1 + i]),
                forall|i: int| 0 <= i < k ==>
                    #[trigger] L::child_view(node, i) == (lo + ci + i) as nat,
            decreases take - k,
        {
            let ghost pre_keys = L::keys_view(node);
            let ghost pre_child = node;
            // pos == count: an append, never a shift. `count < key_cap` because
            // `k <= key_cap` (from `k < take <= key_cap + 1`).
            L::internal_key_insert(&mut node, k - 1, firsts[ci + k]);
            proof {
                let want = Seq::new(k as nat, |i: int| firsts@[ci + 1 + i]);
                assert(L::keys_view(node) == pre_keys.insert((k - 1) as int, firsts@[ci + k]));
                assert(L::keys_view(node) =~= want) by {
                    assert forall|i: int| #![trigger want[i]] 0 <= i < k implies
                        L::keys_view(node)[i] == want[i] by {
                        if i < k - 1 { assert(L::keys_view(node)[i] == pre_keys[i]); }
                    }
                }
            }
            let ck = Self::arena_idx_from(lo + ci + k);
            L::set_internal_child(&mut node, k, ck);
            proof {
                assert forall|i: int| 0 <= i < k + 1 implies
                    #[trigger] L::child_view(node, i) == (lo + ci + i) as nat by {
                    if i < k as int {
                        // `internal_key_insert` and `set_internal_child` at `k`
                        // both leave every other child slot alone.
                        assert(L::child_view(node, i) == L::child_view(pre_child, i));
                    }
                }
            }
            k = k + 1;
        }
        node
    }

    /// ONE INTERNAL LEVEL of the bulk load: group the `c` children living at
    /// arena indices `[lo, lo + c)` into `im` balanced runs and push one parent
    /// per run. Returns the parents' first-key words (for the level above) and the
    /// ghost forest.
    ///
    /// The children are the arena's TAIL (`arena.len() == lo + c`), so the parents
    /// land at `[lo + c, lo + c + im)` — contiguous again, which is what lets the
    /// next level up address ITS children by a base offset. Production instead
    /// carries a `Vec<ArenaIdx>` per level.
    ///
    /// `firsts[q]` is child `q`'s smallest key, so a separator is one array read
    /// rather than production's `first_key_word` descent to a leftmost leaf.
    ///
    /// `is_root` selects the occupancy regime: the topmost level is a single node
    /// exempt from the minimum (`tree_wf`'s root case), every other level has
    /// `im >= 2` parents that must each meet it — which the balanced partition
    /// delivers, since `take >= (child_cap + 1) / 2` gives
    /// `take - 1 >= key_cap / 2` exactly.
    // The per-iteration ghost work (group wf, binds, footprint, regrouping,
    // ordering) is a lot of quantified reasoning for one loop body; a raised
    // rlimit is cheaper than splitting it into a lemma that would have to
    // re-take fifteen hypotheses. spinoff isolates the query: at 200 without
    // it, the group loop's query passes or exceeds the limit depending on
    // unrelated context elsewhere in the module.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(300)]
    fn bulk_build_level(
        &mut self,
        lo: usize,
        c: usize,
        im: usize,
        firsts: &[L::Word],
        Ghost(ckids): Ghost<Seq<Tree>>,
        Ghost(h): Ghost<nat>,
        Ghost(is_root): Ghost<bool>,
    ) -> (r: (std::vec::Vec<L::Word>, Ghost<Seq<Tree>>))
        requires
            old(self).nodes.wf(),
            // the children are the arena's tail.
            old(self).arena().len() == lo + c,
            c >= 2,
            // layout geometry (M6): a real internal node holds >= 2 separators,
            // and the capacities fit a `usize`. The caller has both from
            // `L::lemma_capacity_headroom`.
            L::key_cap_spec() >= 2,
            L::key_cap_spec() < usize::MAX,
            L::leaf_cap_spec() >= 1,
            // `is_root` <=> this is the last level (one node, occupancy-exempt).
            if is_root { im == 1 } else { im >= 2 },
            (L::key_cap_spec() + 1) * (im - 1) < c,
            c <= (L::key_cap_spec() + 1) * im,
            // arena headroom for this level's pushes.
            lo + c + im + 1 < <L::ArenaIdx as IndexLike>::max_nat(),
            lo + c + im <= usize::MAX,
            ckids.len() == c,
            firsts@.len() == c,
            // the level below's recorded minima, and its contiguous ids.
            forall|q: int| 0 <= q < c ==>
                (#[trigger] firsts@[q]).as_nat()
                    == crate::bplus_tree::tree_keys(ckids[q])[0],
            forall|q: int| 0 <= q < c ==>
                crate::bplus_tree::tree_root_id(#[trigger] ckids[q]) == (lo + q) as nat,
            forest_binds_l::<L>(old(self).arena(), ckids),
            crate::bplus_tree::forest_wf(ckids, h, L::leaf_cap_spec(), L::key_cap_spec()),
            crate::bplus_tree::forest_disjoint(ckids),
            forall|a: int, b: int| 0 <= a < b < c ==>
                (#[trigger] crate::bplus_tree::tree_ids(ckids[a]))
                    .disjoint(#[trigger] crate::bplus_tree::tree_ids(ckids[b])),
            forall|q: int, id: nat| 0 <= q < c
                && #[trigger] crate::bplus_tree::tree_ids(ckids[q]).contains(id)
                ==> id < lo + c,
            forall|q: int| 0 <= q < c - 1 ==>
                crate::bplus_tree::keys_all_below(#[trigger] ckids[q], ckids[q + 1]),
        ensures
            final(self).nodes.wf(),
            final(self).arena().len() == lo + c + im,
            final(self).nodes.snapshots_view() == old(self).nodes.snapshots_view(),
            // the level below is untouched (pushes only), so its chain and its
            // `binds` survive verbatim.
            forall|i: int| 0 <= i < lo + c ==> final(self).arena()[i] == old(self).arena()[i],
            r.1@.len() == im,
            r.0@.len() == im,
            forall|g: int| 0 <= g < im ==>
                (#[trigger] r.0@[g]).as_nat()
                    == crate::bplus_tree::tree_keys(r.1@[g])[0],
            forall|g: int| 0 <= g < im ==>
                crate::bplus_tree::tree_root_id(#[trigger] r.1@[g]) == (lo + c + g) as nat,
            forest_binds_l::<L>(final(self).arena(), r.1@),
            forall|g: int| 0 <= g < im ==>
                crate::bplus_tree::tree_wf(#[trigger] r.1@[g], (h + 1) as nat,
                    L::leaf_cap_spec(), L::key_cap_spec(), is_root),
            crate::bplus_tree::forest_disjoint(r.1@),
            forall|a: int, b: int| 0 <= a < b < im ==>
                (#[trigger] crate::bplus_tree::tree_ids(r.1@[a]))
                    .disjoint(#[trigger] crate::bplus_tree::tree_ids(r.1@[b])),
            forall|g: int, id: nat| 0 <= g < im
                && #[trigger] crate::bplus_tree::tree_ids(r.1@[g]).contains(id)
                ==> id < lo + c + im,
            // the level's views are the children's, regrouped.
            crate::bplus_tree::forest_keys(r.1@) == crate::bplus_tree::forest_keys(ckids),
            crate::bplus_tree::forest_leaf_ids(r.1@)
                == crate::bplus_tree::forest_leaf_ids(ckids),
            // each parent adds itself on top of its group.
            crate::bplus_tree::forest_node_count(r.1@)
                == crate::bplus_tree::forest_node_count(ckids) + im,
            forall|g: int| 0 <= g < im - 1 ==>
                crate::bplus_tree::keys_all_below(#[trigger] r.1@[g], r.1@[g + 1]),
    {
        let ghost cap = L::leaf_cap_spec();
        let ghost key_cap = L::key_cap_spec();
        let child_cap = L::key_cap() + 1;
        let base = c / im;
        let rem = c % im;
        proof {
            L::lemma_arena_capacity();
            assert(base * im + rem == c) by (nonlinear_arith)
                requires base == c / im, rem == c % im, im >= 1;
            assert(rem < im) by (nonlinear_arith) requires rem == c % im, im >= 1;
            assert(base <= child_cap) by (nonlinear_arith)
                requires base * im + rem == c, c <= child_cap * im, im >= 1, rem >= 0;
            if rem > 0 {
                assert(base < child_cap) by (nonlinear_arith)
                    requires base * im + rem == c, c <= child_cap * im, im >= 1, rem > 0;
            }
            if im >= 2 {
                // The occupancy floor, at THIS level's capacity (`child_cap`
                // children rather than `cap` keys).
                crate::bplus_tree::lemma_balanced_group_min(c as nat, child_cap as nat, im as nat);
                assert(base >= (child_cap + 1) / 2);
                // `(key_cap + 2) / 2 - 1 == key_cap / 2` for every integer
                // `key_cap`, so a group of `>= (child_cap+1)/2` children carries
                // `>= key_cap / 2` separators -- exactly `tree_wf`'s minimum.
                assert(child_cap == key_cap + 1);
                assert((key_cap + 2) / 2 == key_cap / 2 + 1) by (nonlinear_arith);
                assert(base - 1 >= key_cap / 2);
                assert(base >= 2);
            } else {
                // one parent over every child: `c >= 2` gives it two children.
                assert(im == 1);
                assert(base == c / 1) by (nonlinear_arith) requires base == c / im, im == 1;
                assert(base == c);
                assert(base >= 2);
            }
        }

        let mut out: std::vec::Vec<L::Word> = std::vec::Vec::new();
        let ghost mut parents: Seq<Tree> = Seq::empty();
        let ghost old_arena = self.arena();
        let ghost mut prev_ci: int = 0;
        let mut ci: usize = 0;
        let mut g: usize = 0;
        while g < im
            invariant
                self.nodes.wf(),
                self.nodes.snapshots_view() == old(self).nodes.snapshots_view(),
                self.arena().len() == lo + c + g,
                old_arena == old(self).arena(),
                old_arena.len() == lo + c,
                forall|i: int| #![trigger old_arena[i]] 0 <= i < lo + c ==> self.arena()[i] == old_arena[i],
                0 <= g <= im,
                cap == L::leaf_cap_spec(),
                key_cap == L::key_cap_spec(),
                child_cap == key_cap + 1,
                c >= 2,
                if is_root { im == 1 } else { im >= 2 },
                base == c / im,
                rem == c % im,
                base * im + rem == c,
                rem < im,
                base <= child_cap,
                rem > 0 ==> base < child_cap,
                base >= 2,
                im >= 2 ==> base - 1 >= key_cap / 2,
                cap >= 1,
                key_cap >= 2,
                key_cap < usize::MAX,
                lo + c + im + 1 < <L::ArenaIdx as IndexLike>::max_nat(),
                lo + c + im <= usize::MAX,
                ckids.len() == c,
                firsts@.len() == c,
                // `ci` is the number of children consumed by parents `[0, g)`.
                ci == base * g + (if g < rem { g as int } else { rem as int }),
                ci <= c,
                0 <= prev_ci <= ci,
                out@.len() == g,
                parents.len() == g,
                // the level below, carried unchanged.
                forall|q: int| 0 <= q < c ==>
                    (#[trigger] firsts@[q]).as_nat()
                        == crate::bplus_tree::tree_keys(ckids[q])[0],
                forall|q: int| 0 <= q < c ==>
                    crate::bplus_tree::tree_root_id(#[trigger] ckids[q]) == (lo + q) as nat,
                forest_binds_l::<L>(self.arena(), ckids),
                crate::bplus_tree::forest_wf(ckids, h, cap, key_cap),
                crate::bplus_tree::forest_disjoint(ckids),
                forall|a: int, b: int| 0 <= a < b < c ==>
                    (#[trigger] crate::bplus_tree::tree_ids(ckids[a]))
                        .disjoint(#[trigger] crate::bplus_tree::tree_ids(ckids[b])),
                forall|q: int, id: nat| 0 <= q < c
                    && #[trigger] crate::bplus_tree::tree_ids(ckids[q]).contains(id)
                    ==> id < lo + c,
                forall|q: int| 0 <= q < c - 1 ==>
                    crate::bplus_tree::keys_all_below(#[trigger] ckids[q], ckids[q + 1]),
                // parents built so far.
                forall|q: int| 0 <= q < g ==>
                    (#[trigger] out@[q]).as_nat()
                        == crate::bplus_tree::tree_keys(parents[q])[0],
                forall|q: int| 0 <= q < g ==>
                    crate::bplus_tree::tree_root_id(#[trigger] parents[q]) == (lo + c + q) as nat,
                forest_binds_l::<L>(self.arena(), parents),
                forall|q: int| 0 <= q < g ==>
                    crate::bplus_tree::tree_wf(#[trigger] parents[q], (h + 1) as nat,
                        cap, key_cap, is_root),
                crate::bplus_tree::forest_disjoint(parents),
                forall|a: int, b: int| 0 <= a < b < g ==>
                    (#[trigger] crate::bplus_tree::tree_ids(parents[a]))
                        .disjoint(#[trigger] crate::bplus_tree::tree_ids(parents[b])),
                forall|q: int| 0 <= q < g - 1 ==>
                    crate::bplus_tree::keys_all_below(#[trigger] parents[q], parents[q + 1]),
                forall|q: int, id: nat| 0 <= q < g
                    && #[trigger] crate::bplus_tree::tree_ids(parents[q]).contains(id)
                    ==> id < lo + c + g,
                // the regrouping identity: parents `[0, g)` cover children
                // `[0, ci)` exactly, in both additive views.
                crate::bplus_tree::forest_keys(parents)
                    == crate::bplus_tree::forest_keys(ckids.subrange(0, ci as int)),
                crate::bplus_tree::forest_leaf_ids(parents)
                    == crate::bplus_tree::forest_leaf_ids(ckids.subrange(0, ci as int)),
                crate::bplus_tree::forest_node_count(parents)
                    == crate::bplus_tree::forest_node_count(
                        ckids.subrange(0, ci as int)) + g,
                // Every parent built so far owns only its own id plus children
                // from the CONSUMED prefix `[0, ci)`. Disjointness against the
                // next parent then needs no per-pair reasoning: the next parent's
                // children come from `[ci, ..)`, and its id is fresh.
                forall|q: int, id: nat| 0 <= q < g
                    && #[trigger] crate::bplus_tree::tree_ids(parents[q]).contains(id)
                    ==> id == (lo + c + q) as nat
                        || crate::bplus_tree::forest_ids(
                            ckids.subrange(0, ci as int)).contains(id),
                // the most recent parent covers exactly `[prev_ci, ci)`, which is
                // what orders it against the next one.
                g > 0 ==> parents[g - 1] is Inner
                    && parents[g - 1]->Inner_kids
                        == ckids.subrange(prev_ci, ci as int),
            decreases im - g,
        {
            let take = if g < rem { base + 1 } else { base };
            proof {
                assert(take <= child_cap);
                assert(ci + take <= c) by (nonlinear_arith)
                    requires
                        ci == base * g + (if g < rem { g as int } else { rem as int }),
                        take == (if g < rem { base as int + 1 } else { base as int }),
                        base * im + rem == c,
                        0 <= g < im,
                        rem < im;
                assert(take >= 2);
            }
            let node = Self::bulk_fill_internal(lo, ci, take, firsts);
            let ghost group = ckids.subrange(ci as int, (ci + take) as int);
            let ghost pid = (lo + c + g) as nat;
            let ghost parent = Tree::Inner {
                id: pid,
                seps: crate::bplus_tree::bulk_seps(group),
                kids: group,
            };
            let ghost prev_arena = self.arena();
            let ghost old_parents = parents;
            proof { assert(self.arena().len() + 1 < <L::ArenaIdx as IndexLike>::max_nat()); }
            self.nodes.push(node);
            out.push(firsts[ci]);
            proof {
                parents = old_parents.push(parent);
                assert(self.arena() =~= prev_arena.push(node));
                assert(self.arena()[pid as int] == node);
                assert(forall|i: int| #![trigger prev_arena[i]] 0 <= i < prev_arena.len()
                    ==> self.arena()[i] == prev_arena[i]);

                // ---- the group, read off the child level ----
                assert(group.len() == take);
                assert forall|q: int| 0 <= q < take implies group[q] == ckids[ci + q] by {}
                crate::bplus_tree::lemma_forest_wf_subrange(ckids, h, cap, key_cap,
                    ci as int, (ci + take) as int);
                crate::bplus_tree::lemma_forest_disjoint_subrange(ckids,
                    ci as int, (ci + take) as int);
                assert forall|q: int| 0 <= q < group.len() - 1 implies
                    crate::bplus_tree::keys_all_below(#[trigger] group[q], group[q + 1]) by {
                    assert(group[q] == ckids[ci + q]);
                    assert(group[q + 1] == ckids[ci + q + 1]);
                    assert(crate::bplus_tree::keys_all_below(ckids[ci + q], ckids[ci + q + 1]));
                }
                assert forall|a: int, b: int| 0 <= a < b < group.len() implies
                    (#[trigger] crate::bplus_tree::tree_ids(group[a]))
                        .disjoint(#[trigger] crate::bplus_tree::tree_ids(group[b])) by {
                    assert(group[a] == ckids[ci + a]);
                    assert(group[b] == ckids[ci + b]);
                    assert(crate::bplus_tree::tree_ids(ckids[ci + a])
                        .disjoint(crate::bplus_tree::tree_ids(ckids[ci + b])));
                }

                // ---- the parent is wf, with the right views ----
                // `is_root` <=> `im == 1` <=> this group is every child, so the
                // occupancy hypothesis matches `tree_wf`'s root exemption.
                assert(2 <= group.len() <= key_cap + 1);
                assert(is_root || group.len() - 1 >= key_cap / 2);
                crate::bplus_tree::lemma_bulk_group_wf(group, pid, h, cap, key_cap, is_root);
                assert(crate::bplus_tree::tree_keys(parent)
                    == crate::bplus_tree::forest_keys(group));
                assert(crate::bplus_tree::tree_leaf_ids(parent)
                    == crate::bplus_tree::forest_leaf_ids(group));

                // ---- binds: separators and children read off `bulk_fill_internal`
                let seps = crate::bplus_tree::bulk_seps(group);
                assert forall|q: int| 0 <= q < group.len() implies
                    crate::bplus_tree::tree_keys(#[trigger] group[q]).len() >= 1 by {
                    crate::bplus_tree::lemma_forest_wf_at(group, h, cap, key_cap, q);
                    crate::bplus_tree::lemma_tree_keys_nonempty(group[q], h, cap, key_cap);
                }
                assert forall|i: int| 0 <= i < seps.len() implies
                    (#[trigger] L::keys_view(node)[i]).as_nat() == seps[i] by {
                    assert(L::keys_view(node)[i] == firsts@[ci + 1 + i]);
                    assert(seps[i] == crate::bplus_tree::tree_keys(group[i + 1])[0]);
                    assert(group[i + 1] == ckids[ci + 1 + i]);
                }
                assert forall|i: int| 0 <= i < group.len() implies
                    L::child_view(node, i)
                        == crate::bplus_tree::tree_root_id(#[trigger] group[i]) by {
                    assert(group[i] == ckids[ci + i]);
                }
                lemma_forest_binds_frame_push::<L>(prev_arena, self.arena(), ckids, node);
                lemma_forest_binds_frame_push::<L>(prev_arena, self.arena(), old_parents, node);
                lemma_forest_binds_subrange::<L>(self.arena(), ckids,
                    ci as int, (ci + take) as int);
                assert(binds::<L>(self.arena(), parent));
                lemma_forest_binds_push::<L>(self.arena(), old_parents, parent);

                // ---- footprint: the parent's own id is fresh (above every child
                // id AND every earlier parent id), so it is `tree_disjoint` and
                // disjoint from its predecessors.
                crate::bplus_tree::lemma_forest_ids_bound(group, (lo + c) as nat);
                assert(!crate::bplus_tree::forest_ids(group).contains(pid));
                assert(crate::bplus_tree::tree_disjoint(parent));
                assert forall|id: nat| crate::bplus_tree::tree_ids(parent).contains(id)
                    implies id < lo + c + g + 1 by {
                    if id != pid {
                        assert(crate::bplus_tree::forest_ids(group).contains(id));
                    }
                }
                // Parent `q`'s footprint (invariant) is its own id `lo + c + q`
                // plus children from `[0, ci)`; this parent's is `pid` (distinct,
                // since `q < g`) plus children from `[ci, ci + take)` (disjoint
                // range). No per-pair descent needed.
                crate::bplus_tree::lemma_forest_ids_ranges_disjoint(ckids,
                    0, ci as int, ci as int, (ci + take) as int);
                assert forall|q: int| 0 <= q < g implies
                    (#[trigger] crate::bplus_tree::tree_ids(old_parents[q]))
                        .disjoint(crate::bplus_tree::tree_ids(parent)) by {
                    assert forall|id: nat| #![trigger crate::bplus_tree::tree_ids(parent).contains(id)]
                        crate::bplus_tree::tree_ids(old_parents[q]).contains(id)
                        implies !crate::bplus_tree::tree_ids(parent).contains(id) by {
                        if crate::bplus_tree::tree_ids(parent).contains(id) {
                            // `id` is in parent `q`: either its id or a consumed child.
                            if id == pid {
                                assert(id == (lo + c + q) as nat
                                    || crate::bplus_tree::forest_ids(
                                        ckids.subrange(0, ci as int)).contains(id));
                                crate::bplus_tree::lemma_forest_ids_bound(
                                    ckids.subrange(0, ci as int), (lo + c) as nat);
                            } else {
                                assert(crate::bplus_tree::forest_ids(group).contains(id));
                                assert(id < lo + c);
                            }
                        }
                    }
                }
                crate::bplus_tree::lemma_forest_disjoint_push_pairwise(old_parents, parent);

                // carry the footprint invariant to `g + 1` (the consumed prefix
                // widens to `[0, ci + take)`).
                crate::bplus_tree::lemma_forest_ids_subrange_subset(ckids,
                    0, ci as int, 0, (ci + take) as int);
                crate::bplus_tree::lemma_forest_ids_subrange_subset(ckids,
                    ci as int, (ci + take) as int, 0, (ci + take) as int);
                assert forall|q: int, id: nat| 0 <= q < g + 1
                    && #[trigger] crate::bplus_tree::tree_ids(parents[q]).contains(id)
                    implies id == (lo + c + q) as nat
                        || crate::bplus_tree::forest_ids(
                            ckids.subrange(0, (ci + take) as int)).contains(id) by {
                    if q < g {
                        assert(parents[q] == old_parents[q]);
                    } else {
                        assert(parents[q] == parent);
                    }
                }

                // ---- the additive views telescope ----
                crate::bplus_tree::lemma_forest_keys_push(old_parents, parent);
                crate::bplus_tree::lemma_forest_leaf_ids_push(old_parents, parent);
                crate::bplus_tree::lemma_forest_node_count_push(old_parents, parent);
                crate::bplus_tree::lemma_forest_views_prefix_split(ckids,
                    ci as int, (ci + take) as int);
                assert(crate::bplus_tree::forest_keys(parents)
                    == crate::bplus_tree::forest_keys(ckids.subrange(0, (ci + take) as int)));
                assert(crate::bplus_tree::forest_leaf_ids(parents)
                    == crate::bplus_tree::forest_leaf_ids(
                        ckids.subrange(0, (ci + take) as int)));

                // ---- first key: the group's first child's, already recorded ----
                crate::bplus_tree::lemma_forest_keys_first(group);
                assert(group[0] == ckids[ci as int]);
                assert(out@[g as int] == firsts@[ci as int]);
                assert(out@[g as int].as_nat()
                    == crate::bplus_tree::tree_keys(parent)[0]);

                // ---- ordering against the previous parent ----
                if g > 0 {
                    let pgroup = ckids.subrange(prev_ci, ci as int);
                    assert(old_parents[g - 1]->Inner_kids == pgroup);
                    assert(crate::bplus_tree::tree_keys(old_parents[g - 1])
                        == crate::bplus_tree::forest_keys(pgroup));
                    assert forall|a: int, b: int| 0 <= a < pgroup.len() && 0 <= b < group.len()
                        implies crate::bplus_tree::keys_all_below(#[trigger] pgroup[a],
                            #[trigger] group[b]) by {
                        assert(pgroup[a] == ckids[prev_ci + a]);
                        assert(group[b] == ckids[ci + b]);
                        crate::bplus_tree::lemma_forest_pairwise_lt(ckids, h, cap, key_cap,
                            prev_ci + a, ci + b);
                    }
                    crate::bplus_tree::lemma_forest_keys_all_below(pgroup, group);
                    assert(crate::bplus_tree::keys_all_below(old_parents[g - 1], parent));
                }
                prev_ci = ci as int;
                // `ci` telescopes: adding group `g`'s size gives group `g+1`'s
                // start, in both the oversized (`g < rem`) and plain arms.
                assert(ci + take == base * (g + 1)
                    + (if g + 1 < rem { (g + 1) as int } else { rem as int }))
                    by (nonlinear_arith)
                    requires
                        ci == base * g + (if g < rem { g as int } else { rem as int }),
                        take == (if g < rem { base as int + 1 } else { base as int }),
                        0 <= g < im,
                        rem < im;
            }
            ci = ci + take;
            g = g + 1;
        }
        proof {
            assert(base * im + rem == c);
            assert(ci == c);
            assert(ckids.subrange(0, c as int) =~= ckids);
        }
        (out, Ghost(parents))
    }

    /// THE LEAF LEVEL of the bulk load: partition `keys` into `m` balanced
    /// groups and push one filled leaf per group into a fresh (empty) arena, in
    /// order, linking each leaf to the next as it goes.
    ///
    /// Returns `m`, the number of leaves; because the arena starts empty and only
    /// this loop pushes, leaf `g` lives at arena index `g` — the level's ids are
    /// CONTIGUOUS, which is what lets the internal levels above address their
    /// children by a base offset instead of an index vector (production keeps a
    /// `Vec<ArenaIdx>` per level; this needs none).
    ///
    /// The ghost side accumulates the forest `Seq<Tree>` of `Tree::Leaf` nodes and
    /// its `forest_wf` / adjacent-ordering / binds / links obligations, which are
    /// exactly `lemma_bulk_group_wf`'s hypotheses one level up.
    ///
    /// The balanced partition (`m = ceil(n / cap)` groups of `n/m` or `n/m + 1`)
    /// is what makes every leaf meet `tree_wf`'s non-root minimum of `(cap+1)/2`
    /// keys — see `lemma_balanced_group_min`. Production's `chunks(LEAF_CAP)`
    /// cannot: its last chunk may hold a single key.
    ///
    /// rlimit matches `bulk_build_level`'s: the group loop passes at the
    /// default limit under the arm64 z3 4.16 build but exceeds it under the
    /// x86 build of the same z3 version (platform builds explore in different
    /// orders), so the limit is sized for the noisier of the two.
    #[verifier::rlimit(200)]
    fn bulk_build_leaves(
        &mut self,
        keys: &[K],
        m: usize,
        Ghost(cap): Ghost<nat>,
    ) -> (r: (std::vec::Vec<L::Word>, Ghost<Seq<Tree>>))
        requires
            old(self).nodes.wf(),
            old(self).nodes.view().len() == 0,
            keys@.len() >= 1,
            keys@.len() <= usize::MAX,
            cap == L::leaf_cap_spec(),
            cap >= 1,
            // >= 2 leaves. `m == 1` means the tree IS one leaf, which is the ROOT
            // and therefore exempt from min-occupancy; the caller builds that case
            // directly rather than threading `is_root` through this loop.
            m >= 2,
            cap * (m - 1) < keys@.len(),
            keys@.len() <= cap * m,
            // arena headroom for the whole build: leaves plus every internal
            // level above them (the caller proves this once, from M6).
            2 * m + 2 < <L::ArenaIdx as IndexLike>::max_nat(),
            forall|i: int, j: int| 0 <= i < j < keys@.len()
                ==> (#[trigger] keys@[i]).id_nat() < (#[trigger] keys@[j]).id_nat(),
        ensures
            final(self).nodes.wf(),
            final(self).nodes.view().len() == m,
            final(self).nodes.snapshots_view() == old(self).nodes.snapshots_view(),
            r.1@.len() == m,
            // ids are contiguous from 0 (a fresh arena, pushes only).
            forall|g: int| 0 <= g < m ==>
                crate::bplus_tree::tree_root_id(#[trigger] r.1@[g]) == g as nat,
            forest_binds_l::<L>(final(self).arena(), r.1@),
            crate::bplus_tree::forest_wf(r.1@, 0, cap, L::key_cap_spec()),
            crate::bplus_tree::forest_disjoint(r.1@),
            forall|a: int, b: int| 0 <= a < b < m ==>
                (#[trigger] crate::bplus_tree::tree_ids(r.1@[a]))
                    .disjoint(#[trigger] crate::bplus_tree::tree_ids(r.1@[b])),
            crate::bplus_tree::forest_keys(r.1@)
                == Seq::new(keys@.len(), |i: int| keys@[i].id_nat()),
            crate::bplus_tree::forest_leaf_ids(r.1@)
                == Seq::new(m as nat, |g: int| g as nat),
            // `wf`'s arena-length clause, one level at a time: a leaf is one node.
            crate::bplus_tree::forest_node_count(r.1@) == m,
            forall|g: int| 0 <= g < m ==> (#[trigger] r.1@[g]) is Leaf,
            // the chain: leaf g links to g+1, the last to NIL. Returned in BOTH
            // forms -- the recursive one for this level's `subtree_wf`, and the
            // flat one because every level above shares this same leaf sequence
            // and inherits the chain unchanged (see `chain_links_to`).
            forest_links_to::<L>(final(self).arena(), r.1@, nil_link::<L>()),
            chain_links_to::<L>(final(self).arena(),
                crate::bplus_tree::forest_leaf_ids(r.1@), nil_link::<L>()),
            // adjacent ordering, `lemma_bulk_group_wf`'s ordering hypothesis.
            forall|g: int| 0 <= g < m - 1 ==>
                crate::bplus_tree::keys_all_below(#[trigger] r.1@[g], r.1@[g + 1]),
            // Each leaf's SMALLEST key, for the level above -- recorded here
            // because this loop already knows which input slice each leaf holds.
            // Production instead recovers it later per separator, by descending
            // child-0 pointers to a leftmost leaf (`first_key_word`).
            r.0@.len() == m,
            forall|g: int| 0 <= g < m ==>
                (#[trigger] r.0@[g]).as_nat()
                    == crate::bplus_tree::tree_keys(r.1@[g])[0],
            // every model value is in range -- `model_bounded`, collected by
            // `bulk_fill_leaf` per key and lifted to the forest here.
            model_bounded::<K>(crate::bplus_tree::forest_keys(r.1@)),
    {
        let n = keys.len();
        let base = n / m;
        let rem = n % m;
        proof {
            // Every group holds `base` or `base + 1` keys. `base` already meets the
            // non-root minimum whenever there are >= 2 groups; with one group the
            // single leaf IS the root, which `tree_wf` exempts from the minimum.
            crate::bplus_tree::lemma_balanced_group_min(n as nat, cap, m as nat);
            assert(base * m + rem == n) by (nonlinear_arith)
                requires base == n / m, rem == n % m, m >= 1;
            assert(rem < m) by (nonlinear_arith) requires rem == n % m, m >= 1;
            // Capacity: `base <= cap`, and `base + 1 <= cap` only matters when some
            // group is oversized (`rem > 0`), which forces `base * m < n <= cap * m`
            // and hence `base < cap`.
            assert(base <= cap) by (nonlinear_arith)
                requires base * m + rem == n, n <= cap * m, m >= 1, rem >= 0;
            if rem > 0 {
                assert(base < cap) by (nonlinear_arith)
                    requires base * m + rem == n, n <= cap * m, m >= 1, rem > 0;
            }
        }

        let ghost mut ghost_kids: Seq<Tree> = Seq::empty();
        // Start of the group built by the PREVIOUS iteration, so the new leaf can
        // be ordered against its immediate predecessor.
        let ghost mut prev_at: int = 0;
        // Each leaf's smallest key, handed to the level above (see the `firsts`
        // clause of the ensures).
        let mut firsts: std::vec::Vec<L::Word> = std::vec::Vec::new();
        let mut at: usize = 0;
        let mut g: usize = 0;
        while g < m
            invariant
                self.nodes.wf(),
                self.nodes.snapshots_view() == old(self).nodes.snapshots_view(),
                self.nodes.view().len() == g,
                0 <= g <= m,
                m >= 2,
                cap == L::leaf_cap_spec(),
                cap >= 1,
                n == keys@.len(),
                n >= 1,
                n <= usize::MAX,
                base == n / m,
                rem == n % m,
                base * m + rem == n,
                rem < m,
                base <= cap,
                rem > 0 ==> base < cap,
                base >= (cap + 1) / 2,
                2 * m + 2 < <L::ArenaIdx as IndexLike>::max_nat(),
                // `at` is the number of keys consumed by groups `[0, g)`.
                at == base * g + (if g < rem { g as int } else { rem as int }),
                at <= n,
                0 <= prev_at <= at,
                ghost_kids.len() == g,
                forall|i: int, j: int| 0 <= i < j < keys@.len()
                    ==> (#[trigger] keys@[i]).id_nat() < (#[trigger] keys@[j]).id_nat(),
                // Each built leaf sits at its own arena index (contiguous ids).
                forall|q: int| 0 <= q < g ==>
                    (#[trigger] ghost_kids[q]) is Leaf
                        && crate::bplus_tree::tree_root_id(ghost_kids[q]) == q as nat,
                // Adjacent leaves are in key order. Follows from the input being
                // globally sorted plus each leaf holding a CONTIGUOUS slice of it:
                // `forest_keys(ghost_kids)` is the input prefix (below), so leaf
                // `q`'s keys and leaf `q+1`'s are ordered slices of one sorted seq.
                forall|q: int| 0 <= q < g - 1 ==>
                    crate::bplus_tree::keys_all_below(#[trigger] ghost_kids[q], ghost_kids[q + 1]),
                // The MOST RECENT leaf holds exactly the input slice
                // `[prev_at, at)`. Only the last one is needed: the pair
                // `(g - 1, g)` is the only new adjacency each iteration creates,
                // and every older pair is already carried above. Keeping one
                // slice fact rather than a `forall` over all `g` of them is what
                // keeps this loop inside the solver's budget.
                g > 0 ==> crate::bplus_tree::tree_keys(ghost_kids[g - 1])
                    == Seq::new((at - prev_at) as nat, |i: int| keys@[prev_at + i].id_nat()),
                forest_binds_l::<L>(self.arena(), ghost_kids),
                crate::bplus_tree::forest_wf(ghost_kids, 0, cap, L::key_cap_spec()),
                crate::bplus_tree::forest_keys(ghost_kids)
                    == Seq::new(at as nat, |i: int| keys@[i].id_nat()),
                crate::bplus_tree::forest_leaf_ids(ghost_kids)
                    == Seq::new(g as nat, |q: int| q as nat),
                crate::bplus_tree::forest_disjoint(ghost_kids),
                forall|a: int, b: int| 0 <= a < b < g ==>
                    (#[trigger] crate::bplus_tree::tree_ids(ghost_kids[a]))
                        .disjoint(#[trigger] crate::bplus_tree::tree_ids(ghost_kids[b])),
                // The chain, written at FILL time rather than in a second pass:
                // each leaf's successor id is known before the leaf exists (a
                // fresh arena gives contiguous ids), so leaf `q` already holds its
                // final link the moment it is pushed -- `q + 1`, or NIL at `m - 1`.
                // Production instead re-reads and rewrites every leaf afterwards.
                forall|q: int| 0 <= q < g ==>
                    #[trigger] L::link_view(self.arena()[q])
                        == (if q + 1 < m { (q + 1) as nat } else { nil_link::<L>() }),
                // the first-key carry, and the model bound, both accumulated
                // alongside the forest.
                firsts@.len() == g,
                forall|q: int| 0 <= q < g ==>
                    (#[trigger] firsts@[q]).as_nat()
                        == crate::bplus_tree::tree_keys(ghost_kids[q])[0],
                model_bounded::<K>(crate::bplus_tree::forest_keys(ghost_kids)),
            decreases m - g,
        {
            proof {
                // `base + 1` cannot overflow: `base == n / m` with `m >= 2`, so
                // `base <= n / 2 < n <= usize::MAX`.
                assert(base < n) by (nonlinear_arith) requires base == n / m, m >= 2, n >= 1;
            }
            let take = if g < rem { base + 1 } else { base };
            proof {
                assert(take <= cap);
                // group `g` ends at `at + take <= n`: the remaining `m - g` groups
                // each hold at least `base`, and the count telescopes.
                assert(at + take <= n) by (nonlinear_arith)
                    requires
                        at == base * g + (if g < rem { g as int } else { rem as int }),
                        take == (if g < rem { base as int + 1 } else { base as int }),
                        base * m + rem == n,
                        0 <= g < m,
                        rem < m;
            }
            // Successor id: the next leaf's index, or NIL at the last leaf. Both
            // are in range (the caller's arena-headroom precondition).
            let ghost mx = <L::ArenaIdx as IndexLike>::max_nat();
            let link: L::ArenaIdx = if g + 1 < m {
                proof {
                    assert(2 * m + 2 < mx);
                    assert(((g + 1) as nat) < mx);
                }
                Self::arena_idx_from(g + 1)
            } else {
                Self::nil_arena_idx()
            };
            let node = Self::bulk_fill_leaf(keys, at, take, link);
            let ghost old_arena = self.arena();
            let ghost old_kids = ghost_kids;
            let ghost old_firsts = firsts@;
            proof { assert(self.arena().len() + 1 < mx); }
            self.nodes.push(node);
            // `take >= 1` (the occupancy floor), so `keys[at]` is this leaf's
            // smallest key -- one array read, no descent.
            let fw: L::Word = keys[at].to_index();
            firsts.push(fw);
            let ghost gkeys = Seq::new(take as nat, |i: int| keys@[at + i].id_nat());
            let ghost leaf = Tree::Leaf { id: g as nat, keys: gkeys };
            proof {
                ghost_kids = old_kids.push(leaf);
                assert(self.arena() =~= old_arena.push(node));
                assert(self.arena()[g as int] == node);

                // ---- the new leaf itself ----
                // binds: id in range, leaf, count == keys.len(), words project.
                assert(L::keys_view(node).len() == take) by { L::lemma_keys_view_len(node); }
                assert(binds::<L>(self.arena(), leaf)) by {
                    assert forall|i: int| 0 <= i < gkeys.len() implies
                        (#[trigger] L::keys_view(self.arena()[g as int])[i]).as_nat() == gkeys[i] by {
                        assert(node_word_keys::<L>(node)[i] == gkeys[i]);
                    }
                }
                // tree_wf at height 0: within capacity, sorted, and (non-root)
                // above the occupancy minimum -- the balanced partition's payoff.
                assert(crate::bplus_tree::strictly_sorted(gkeys)) by {
                    assert forall|a: int, b: int| 0 <= a < b < gkeys.len() implies
                        gkeys[a] < gkeys[b] by {
                        assert(keys@[at + a].id_nat() < keys@[at + b].id_nat());
                    }
                }
                assert(take >= (cap + 1) / 2);
                assert(crate::bplus_tree::tree_wf(leaf, 0, cap, L::key_cap_spec(), false));
                assert(crate::bplus_tree::tree_disjoint(leaf));

                // ---- the first-key carry ----
                // The leaf's key seq is the input slice starting at `at`, and
                // `take >= 1`, so index 0 is `keys[at]` -- exactly the word just
                // pushed to `firsts`.
                assert(take >= 1);
                assert(firsts@ =~= old_firsts.push(fw));
                assert(crate::bplus_tree::tree_keys(leaf)[0] == keys@[at as int].id_nat());
                assert(fw.as_nat() == crate::bplus_tree::tree_keys(leaf)[0]);

                // ---- frame the previously built leaves across the push ----
                assert forall|q: int| 0 <= q < g implies
                    crate::bplus_tree::tree_ids(#[trigger] old_kids[q]) =~= set![q as nat] by {
                    assert(old_kids[q] is Leaf);
                    assert(crate::bplus_tree::tree_root_id(old_kids[q]) == q as nat);
                }
                lemma_forest_binds_frame_push::<L>(old_arena, self.arena(), old_kids, node);
                lemma_forest_binds_push::<L>(self.arena(), old_kids, leaf);

                // ---- extend each forest view by one ----
                crate::bplus_tree::lemma_forest_wf_push(old_kids, leaf, 0, cap, L::key_cap_spec());
                crate::bplus_tree::lemma_forest_keys_push(old_kids, leaf);
                crate::bplus_tree::lemma_forest_leaf_ids_push(old_kids, leaf);
                assert(crate::bplus_tree::forest_keys(ghost_kids)
                    =~= Seq::new((at + take) as nat, |i: int| keys@[i].id_nat()));
                assert(crate::bplus_tree::forest_leaf_ids(ghost_kids)
                    =~= Seq::new((g + 1) as nat, |q: int| q as nat));
                assert(crate::bplus_tree::tree_leaf_ids(leaf) =~= seq![g as nat]);

                // ---- the chain link, already final ----
                // `bulk_fill_leaf` wrote `link` into the node, and every earlier
                // slot is untouched by a `push`.
                assert(L::link_view(self.arena()[g as int])
                    == (if g + 1 < m { (g + 1) as nat } else { nil_link::<L>() }));
                assert forall|q: int| 0 <= q < g implies
                    #[trigger] L::link_view(self.arena()[q])
                        == (if q + 1 < m { (q + 1) as nat } else { nil_link::<L>() }) by {
                    assert(self.arena()[q] == old_arena[q]);
                }

                // ---- adjacent ordering against the immediate predecessor ----
                // Leaf `g - 1` holds `keys[prev_at .. at)` and leaf `g` holds
                // `keys[at .. at + take)`; the input is globally sorted, so every
                // index in the first slice is below every index in the second.
                if g > 0 {
                    let pkeys = crate::bplus_tree::tree_keys(old_kids[g - 1]);
                    assert(pkeys == Seq::new((at - prev_at) as nat,
                        |i: int| keys@[prev_at + i].id_nat()));
                    assert forall|a: int, b: int| 0 <= a < pkeys.len() && 0 <= b < gkeys.len()
                        implies (#[trigger] pkeys[a]) < (#[trigger] gkeys[b]) by {
                        assert(pkeys[a] == keys@[prev_at + a].id_nat());
                        assert(gkeys[b] == keys@[at + b].id_nat());
                        assert(prev_at + a < at + b);
                        assert(keys@[prev_at + a].id_nat() < keys@[at + b].id_nat());
                    }
                    assert(crate::bplus_tree::keys_all_below(old_kids[g - 1], leaf));
                }

                // ---- disjointness: the new leaf's id is `g`, fresh above every
                // previously built id (which are exactly `0 .. g`).
                assert(crate::bplus_tree::tree_ids(leaf) =~= set![g as nat]);
                crate::bplus_tree::lemma_forest_disjoint_push(old_kids, leaf, g as nat);

                // ---- model_bounded, extended by the new leaf's keys ----
                // `forest_keys` grew by exactly `gkeys` (the push lemma above), and
                // `bulk_fill_leaf` bounded each of those keys.
                assert(model_bounded::<K>(crate::bplus_tree::forest_keys(ghost_kids))) by {
                    let fk = crate::bplus_tree::forest_keys(ghost_kids);
                    let ofk = crate::bplus_tree::forest_keys(old_kids);
                    assert(fk == ofk + gkeys);
                    assert forall|i: int| 0 <= i < fk.len() implies
                        #[trigger] fk[i] < K::id_bound() by {
                        if i < ofk.len() {
                            assert(ofk[i] < K::id_bound());
                        } else {
                            assert(fk[i] == gkeys[i - ofk.len()]);
                            assert(keys@[at + (i - ofk.len())].id_nat() < K::id_bound());
                        }
                    }
                }
            }
            proof {
                // `at` telescopes: adding group `g`'s size gives group `g+1`'s
                // start, in both the oversized (`g < rem`) and plain arms.
                assert(at + take == base * (g + 1)
                    + (if g + 1 < rem { (g + 1) as int } else { rem as int }))
                    by (nonlinear_arith)
                    requires
                        at == base * g + (if g < rem { g as int } else { rem as int }),
                        take == (if g < rem { base as int + 1 } else { base as int }),
                        0 <= g < m,
                        rem < m;
            }
            proof { prev_at = at as int; }
            at = at + take;
            g = g + 1;
        }
        proof {
            // At exit every group is built and `at == n`, so `forest_keys` is the
            // whole input. The chain assembles from the per-index link facts: the
            // leaf level is a contiguous run of ids `0 .. m`, which is exactly
            // `lemma_forest_links_leaf_run`'s shape.
            assert(base * m + rem == n);
            lemma_forest_links_leaf_run::<L>(self.arena(), ghost_kids, 0, nil_link::<L>());
            // The flat form: `forest_leaf_ids` of this level IS `0 .. m`, and the
            // loop's per-index link facts are the chain condition on it verbatim.
            crate::bplus_tree::lemma_forest_node_count_leaves(ghost_kids);
            let lids = crate::bplus_tree::forest_leaf_ids(ghost_kids);
            assert(lids =~= Seq::new(m as nat, |g: int| g as nat));
            assert(chain_links_to::<L>(self.arena(), lids, nil_link::<L>())) by {
                assert forall|p: int| 0 <= p < lids.len() implies
                    #[trigger] L::link_view(self.arena()[lids[p] as int]) == (
                        if p + 1 < lids.len() { lids[p + 1] } else { nil_link::<L>() }
                    ) by {
                    assert(lids[p] == p as nat);
                    assert(L::link_view(self.arena()[p])
                        == (if p + 1 < m { (p + 1) as nat } else { nil_link::<L>() }));
                }
            }
            // Pairwise disjointness in the `tree_ids` form the level above needs:
            // leaf `q` owns exactly `{q}`, so distinct leaves are trivially
            // disjoint. (The `forest_disjoint` form is carried by the loop; this
            // is the indexed companion `bulk_build_level` requires.)
            assert forall|a: int, b: int| 0 <= a < b < m implies
                (#[trigger] crate::bplus_tree::tree_ids(ghost_kids[a]))
                    .disjoint(#[trigger] crate::bplus_tree::tree_ids(ghost_kids[b])) by {
                assert(ghost_kids[a] is Leaf && ghost_kids[b] is Leaf);
                assert(crate::bplus_tree::tree_ids(ghost_kids[a]) =~= set![a as nat]);
                assert(crate::bplus_tree::tree_ids(ghost_kids[b]) =~= set![b as nat]);
            }
        }
        (firsts, Ghost(ghost_kids))
    }

    /// A `Self` with an EMPTY arena: not `wf` (a real tree always has at least a
    /// root leaf), which is why it is private and unadvertised. The bulk loader
    /// needs it because both level builders take `&mut self`, and the whole point
    /// of the loader is to fill a fresh arena from nothing — `new`'s seeded root
    /// leaf would be an orphan node the arena-length clause could never account
    /// for. `bulk_load` is the only caller and re-establishes `wf` before
    /// returning.
    fn empty_arena() -> (t: Self)
        ensures
            t.nodes.wf(),
            t.nodes.view().len() == 0,
            t.nodes.snapshots_view().len() == 0,
            t.header_archive@.len() == 0,
            t.tree_snapshots@.len() == 0,
    {
        BPlusTreeSet {
            nodes: SpVec::<
                L::Node,
                L::ArenaIdx,
                InlineStore<L::Node, L::ArenaIdx>,
                TRACK,
            >::new(),
            root: <L::ArenaIdx as IndexLike>::min(),
            nkeys: 0,
            tree: Ghost(Tree::Leaf { id: 0, keys: Seq::empty() }),
            last_leaf: <L::ArenaIdx as IndexLike>::min(),
            header_archive: std::vec::Vec::new(),
            tree_snapshots: Ghost(Seq::empty()),
            _k: core::marker::PhantomData,
            _s: core::marker::PhantomData,
        }
    }

    /// THE BULK LOADER: build the whole tree bottom-up from strictly ascending
    /// keys, one pass per level, into a fresh arena.
    ///
    /// This is the shape production's `from_sorted` uses, with three differences,
    /// every one of which makes the verified version do strictly LESS work:
    ///
    /// 1. **No index vector per level.** A fresh push-only arena makes each
    ///    level's ids contiguous, so a level is addressed by a base offset
    ///    (`lo`). Production carries a `Vec<ArenaIdx>` per level and indexes
    ///    through it for every child reference.
    /// 2. **No separate link pass.** Each leaf's successor id is known before the
    ///    leaf is filled, so [`bulk_fill_leaf`] writes the chain pointer inline.
    ///    Production re-reads and rewrites every leaf afterwards — one extra
    ///    whole-node read plus write per leaf.
    /// 3. **No `first_key_word` descent.** Each level hands the level above one
    ///    word per node (its smallest key), so a separator is a single array
    ///    read. Production walks child-0 pointers down to a leaf per separator,
    ///    O(height) node reads each.
    ///
    /// It also uses a BALANCED partition (`ceil(n / cap)` groups of `n/m` or
    /// `n/m + 1`) where production uses `chunks(cap)`. That is not an
    /// optimization but a requirement: a chunked last group can hold a single
    /// key, which violates `tree_wf`'s non-root minimum of `(cap+1)/2`, and five
    /// lemmas downstream depend on that minimum. See
    /// [`crate::bplus_tree::lemma_balanced_group_min`].
    ///
    /// Measured on `onesite_bplus.rs` (n = 100k, Layout256, one call site, both
    /// build orders): **62.2µs against production's 72.9µs, −14.6%** — faster than
    /// production, because of (1)-(3). Use that harness and not `bulkload.rs`,
    /// whose fixed build order scored this same code at a flattering 1.0x while the
    /// truth was +29%; the two per-key codegen costs behind that +29% are described
    /// on [`crate::bplus_layout::slice_get`] and
    /// [`crate::bplus_layout::NodeLayout::leaf_push`].
    fn bulk_load(keys: &[K]) -> (t: Self)
        requires
            K::is_bit_stealing(),
            keys@.len() >= 1,
            keys@.len() < usize::MAX,
            forall|i: int, j: int| 0 <= i < j < keys@.len()
                ==> (#[trigger] keys@[i]).id_nat() < (#[trigger] keys@[j]).id_nat(),
        ensures
            t.wf(),
            t.model() == Seq::new(keys@.len(), |i: int| keys@[i].id_nat()),
    {
        let n = keys.len();
        let cap = L::leaf_cap();
        let key_cap = L::key_cap();
        let ghost idb = K::id_bound();
        let ghost mx = <L::ArenaIdx as IndexLike>::max_nat();
        let ghost gcap = L::leaf_cap_spec();
        let ghost gkc = L::key_cap_spec();
        proof {
            L::lemma_arena_capacity();
            L::lemma_geometry();
            // `key_cap < usize::MAX`, needed by `bulk_build_level` (which computes
            // `key_cap + 1`): `2 * key_cap <= data_len == leaf_cap`, and `leaf_cap`
            // is the exec `cap`, hence at most `usize::MAX`.
            assert(2 * L::key_cap_spec() <= cap as nat);
            assert(L::key_cap_spec() >= 1);
            assert(L::key_cap_spec() < usize::MAX as nat);
        }
        // Every key is inside its id bound (the arena-budget lemma's hypothesis).
        // ONE exec read suffices: `lemma_id_nat_bounded` needs a real `K`, and the
        // input is sorted, so bounding the LARGEST key bounds all of them.
        let top: K = keys[n - 1];
        proof {
            top.lemma_id_nat_bounded();
            assert forall|i: int| 0 <= i < keys@.len() implies
                #[trigger] keys@[i].id_nat() < idb by {
                if i < n - 1 {
                    assert(keys@[i].id_nat() < keys@[n - 1].id_nat());
                }
            }
        }
        let m = Self::bulk_groups(n, cap);
        proof {
            Self::lemma_bulk_arena_budget(keys@, n as nat, cap as nat, m as nat);
            // `key_cap >= 2` (so `child_cap >= 3`, which is what makes each level
            // at most half the one below). Same M6 chain the budget lemma runs.
            K::lemma_id_bound_word_relation();
            L::lemma_word_arena_same_width();
            L::lemma_capacity_headroom(idb);
            assert(gkc >= 2);
        }

        let mut t = Self::empty_arena();

        // ---- the m == 1 case: one leaf, which IS the root ----
        // `tree_wf` exempts the root from min-occupancy, so this case cannot go
        // through `bulk_build_leaves` (which proves the non-root minimum).
        if m == 1 {
            let link = Self::nil_arena_idx();
            proof { assert(n as nat <= cap as nat); }
            let node = Self::bulk_fill_leaf(keys, 0, n, link);
            proof { assert(0 + 1 < mx); }
            t.nodes.push(node);
            let ghost gkeys = Seq::new(n as nat, |i: int| keys@[i].id_nat());
            t.tree = Ghost(Tree::Leaf { id: 0, keys: gkeys });
            t.root = Self::arena_idx_from(0);
            t.last_leaf = t.root;
            t.nkeys = n;
            proof {
                reveal(tree_archive_agrees);
                assert(t.arena() =~= seq![node]);
                assert(L::keys_view(node).len() == n) by { L::lemma_keys_view_len(node); }
                assert(binds::<L>(t.arena(), t.tree@)) by {
                    assert forall|i: int| 0 <= i < gkeys.len() implies
                        (#[trigger] L::keys_view(t.arena()[0])[i]).as_nat() == gkeys[i] by {
                        assert(node_word_keys::<L>(node)[i] == gkeys[i]);
                    }
                }
                assert(crate::bplus_tree::strictly_sorted(gkeys)) by {
                    assert forall|a: int, b: int| 0 <= a < b < gkeys.len() implies
                        gkeys[a] < gkeys[b] by {
                        assert(keys@[a].id_nat() < keys@[b].id_nat());
                    }
                }
                assert(crate::bplus_tree::tree_height(t.tree@) == 0);
                assert(crate::bplus_tree::tree_keys(t.tree@) =~= gkeys);
                assert(crate::bplus_tree::tree_leaf_ids(t.tree@) =~= seq![0nat]);
                assert(crate::bplus_tree::node_count(t.tree@) == 1);
                assert(model_bounded::<K>(gkeys));
                assert(t.model() =~= gkeys);
            }
            return t;
        }

        // ---- the leaf level ----
        let r0 = t.bulk_build_leaves(keys, m, Ghost(cap as nat));
        let mut firsts: std::vec::Vec<L::Word> = r0.0;
        let ghost mut level: Seq<Tree> = r0.1@;
        let mut lo: usize = 0;
        let mut c = m;
        let ghost mut h: nat = 0;
        let child_cap = key_cap + 1;
        proof {
            // The whole build fits `2 * m` nodes (each level is at most half the
            // one below), and `2 * m <= n` from the occupancy floor `7 * m <= n`.
            // Both bounds are needed: the arena-index one for `push`, the `usize`
            // one because a `usize` arena's `max_nat` is `usize::MAX + 1`.
            assert(7 * m <= n);
            assert(2 * m <= n);
            assert(child_cap >= 3);
        }
        while c > 1
            invariant
                t.nodes.wf(),
                t.nodes.snapshots_view().len() == 0,
                t.arena().len() == lo + c,
                c >= 1,
                m >= 2,
                n == keys@.len(),
                cap == L::leaf_cap_spec(),
                key_cap == L::key_cap_spec(),
                gcap == L::leaf_cap_spec(),
                gkc == L::key_cap_spec(),
                // `mx` is a ghost VARIABLE, so the loop havocs it unless pinned
                // here -- without this the budget invariant below constrains an
                // arbitrary nat rather than the arena index bound.
                mx == <L::ArenaIdx as IndexLike>::max_nat(),
                child_cap == key_cap + 1,
                child_cap >= 3,
                key_cap >= 2,
                cap >= 1,
                key_cap < usize::MAX,
                2 * m + 3 < mx,
                2 * m <= n,
                n < usize::MAX,
                // Every level is at most half the one below, so `lo + 2*c` never
                // passes `2 * m`. This is the whole arena budget, carried in the
                // one form both `push` (via `max_nat`) and the exec `lo + c`
                // additions (via `usize`) need.
                lo + 2 * c <= 2 * m,
                // The leaf level (ids `0 .. m`) is always below the current
                // level's base, which is what frames the chain across a push.
                m <= lo + c,
                level.len() == c,
                firsts@.len() == c,
                forall|q: int| 0 <= q < c ==>
                    (#[trigger] firsts@[q]).as_nat()
                        == crate::bplus_tree::tree_keys(level[q])[0],
                forall|q: int| 0 <= q < c ==>
                    crate::bplus_tree::tree_root_id(#[trigger] level[q]) == (lo + q) as nat,
                forest_binds_l::<L>(t.arena(), level),
                // Below the top, every node of the level is a NON-root subtree, so
                // `forest_wf` (which is the non-root form pointwise) applies and is
                // what the next `bulk_build_level` consumes. At the top the single
                // remaining node IS the root, which `tree_wf` exempts from
                // min-occupancy -- a strictly weaker fact, and the only one
                // available, so the two cases are carried separately.
                c >= 2 ==> crate::bplus_tree::forest_wf(level, h, gcap, gkc),
                c == 1 ==> crate::bplus_tree::tree_wf(level[0], h, gcap, gkc, true),
                crate::bplus_tree::forest_disjoint(level),
                forall|a: int, b: int| 0 <= a < b < c ==>
                    (#[trigger] crate::bplus_tree::tree_ids(level[a]))
                        .disjoint(#[trigger] crate::bplus_tree::tree_ids(level[b])),
                forall|q: int, id: nat| 0 <= q < c
                    && #[trigger] crate::bplus_tree::tree_ids(level[q]).contains(id)
                    ==> id < lo + c,
                crate::bplus_tree::forest_keys(level)
                    == Seq::new(n as nat, |i: int| keys@[i].id_nat()),
                // The leaf chain, proved ONCE at the leaf level. Every level above
                // has the same in-order leaf sequence and never writes a leaf
                // slot, so it inherits this verbatim (see `chain_links_to`).
                crate::bplus_tree::forest_leaf_ids(level)
                    == Seq::new(m as nat, |g: int| g as nat),
                chain_links_to::<L>(t.arena(),
                    crate::bplus_tree::forest_leaf_ids(level), nil_link::<L>()),
                crate::bplus_tree::forest_node_count(level) == lo + c,
                forall|q: int| 0 <= q < c - 1 ==>
                    crate::bplus_tree::keys_all_below(#[trigger] level[q], level[q + 1]),
                model_bounded::<K>(crate::bplus_tree::forest_keys(level)),
            decreases c,
        {
            let im = Self::bulk_groups(c, child_cap);
            proof {
                // `2 * im <= c`: from `child_cap * (im - 1) < c` with
                // `child_cap >= 3` we get `3 * im <= c + 2`, and then `2 * im =
                // 3 * im - im <= c` for `im >= 2`; `im == 1` is `2 <= c`.
                assert(child_cap * (im - 1) < c);
                assert(3 * (im - 1) <= child_cap * (im - 1)) by (nonlinear_arith)
                    requires child_cap >= 3, im >= 1;
                assert(3 * im <= c + 2);
                if im >= 2 {
                    assert(2 * im <= c);
                } else {
                    assert(im == 1);
                    assert(2 * im <= c);
                }
                // Headroom for this level's `im` pushes, in both currencies: the
                // arena-index one (`max_nat`) for `push`, and the `usize` one for
                // the exec offset arithmetic (a `usize` arena's `max_nat` is
                // `usize::MAX + 1`, one too many to serve for both).
                assert(im >= 1);
                assert(lo + c + 2 * im <= 2 * m);
                assert(lo + c + im + 1 <= 2 * m);
                assert(2 * m + 3 < mx);
                assert(lo + c + im + 1 < mx);
                assert(lo + c + im <= n);
                assert(n < usize::MAX);
                assert(lo + c + im <= usize::MAX);
                assert(m <= lo + c);
            }
            let ghost old_level = level;
            let ghost old_arena = t.arena();
            proof {
                // every `bulk_build_level` precondition, named explicitly.
                assert(t.nodes.wf());
                assert(t.arena().len() == lo + c);
                assert(c >= 2);
                assert(gkc >= 2);
                assert(gkc < usize::MAX as nat);
                assert(gcap >= 1);
                assert(if (im == 1) { im == 1 } else { im >= 2 });
                assert((gkc + 1) * (im - 1) < c) by {
                    assert(child_cap as nat == gkc + 1);
                }
                assert(c <= (gkc + 1) * im) by {
                    assert(child_cap as nat == gkc + 1);
                }
                assert(lo + c + im + 1 < mx);
                assert(lo + c + im <= usize::MAX);
                assert(level.len() == c);
                assert(firsts@.len() == c);
            }
            let r = t.bulk_build_level(
                lo, c, im, &firsts, Ghost(level), Ghost(h), Ghost(im == 1));
            let ghost new_level = r.1@;
            firsts = r.0;
            proof {
                level = new_level;
                // The chain survives: it reads only leaf slots, all of which are
                // below `lo + c` (they are the leaf level, ids `0 .. m`), and
                // `bulk_build_level` only pushes.
                assert(crate::bplus_tree::forest_leaf_ids(level)
                    =~= Seq::new(m as nat, |g: int| g as nat));
                let lids = crate::bplus_tree::forest_leaf_ids(level);
                assert(chain_links_to::<L>(t.arena(), lids, nil_link::<L>())) by {
                    assert forall|q: int| 0 <= q < lids.len() implies
                        #[trigger] L::link_view(t.arena()[lids[q] as int]) == (
                            if q + 1 < lids.len() { lids[q + 1] } else { nil_link::<L>() }
                        ) by {
                        assert(lids[q] == q as nat);
                        assert(q < m);
                        assert(m <= lo + c);
                        assert(t.arena()[q] == old_arena[q]);
                        assert(L::link_view(old_arena[lids[q] as int]) == (
                            if q + 1 < lids.len() { lids[q + 1] } else { nil_link::<L>() }
                        ));
                    }
                }
                if im >= 2 {
                    assert(!(im == 1));
                    assert forall|q: int| 0 <= q < level.len() implies
                        crate::bplus_tree::tree_wf(#[trigger] level[q], (h + 1) as nat,
                            gcap, gkc, false) by {
                        assert(crate::bplus_tree::tree_wf(new_level[q], (h + 1) as nat,
                            gcap, gkc, im == 1));
                    }
                    crate::bplus_tree::lemma_forest_wf_from_pointwise(
                        level, (h + 1) as nat, gcap, gkc);
                } else {
                    // The TOP level: one node, and `bulk_build_level` proved it in
                    // the root regime (`is_root == (im == 1)`), which is exactly
                    // `tree_state_wf`'s form.
                    assert(im == 1);
                    assert(crate::bplus_tree::tree_wf(new_level[0], (h + 1) as nat,
                        gcap, gkc, true));
                }
            }
            lo = lo + c;
            c = im;
            proof { h = h + 1; }
        }

        // ---- assemble the tree ----
        // `c == 1`: the level is a single node, the root, at arena index `lo`.
        let root = Self::arena_idx_from(lo);
        proof {
            assert(lo < mx);
            let rt = level[0];
            lemma_forest_binds_at::<L>(t.arena(), level, 0);
            crate::bplus_tree::lemma_forest_disjoint_at(level, 0);
            crate::bplus_tree::lemma_forest_keys_cons(level);
            crate::bplus_tree::lemma_forest_leaf_ids_cons(level);
            assert(level.drop_first() =~= Seq::<Tree>::empty());
            assert(crate::bplus_tree::tree_keys(rt) =~= crate::bplus_tree::forest_keys(level));
            assert(crate::bplus_tree::tree_leaf_ids(rt)
                =~= crate::bplus_tree::forest_leaf_ids(level));
            assert(crate::bplus_tree::forest_node_count(level)
                == crate::bplus_tree::node_count(rt)
                    + crate::bplus_tree::forest_node_count(level.drop_first()));
            assert(crate::bplus_tree::forest_node_count(Seq::<Tree>::empty()) == 0);
            crate::bplus_tree::lemma_tree_wf_height(rt, h, gcap, gkc, true);
            crate::bplus_tree::lemma_last_leaf_id(rt, h, gcap, gkc, true);
        }
        t.root = root;
        t.nkeys = n;
        t.tree = Ghost(level[0]);
        // The rightmost leaf is the LAST entry of the leaf chain, which this
        // build makes `m - 1` (leaf ids are `0 .. m`, in order). `lemma_last_leaf_id`
        // above identifies that entry with `last_leaf_id(tree@)`, which is the
        // `last_leaf_ok` clause -- no descent, no search.
        proof {
            let lids = crate::bplus_tree::tree_leaf_ids(t.tree@);
            assert(lids.len() == m);
            assert(lids[m - 1] == (m - 1) as nat);
            assert(crate::bplus_tree::last_leaf_id(t.tree@) == (m - 1) as nat);
            assert(((m - 1) as nat) < mx);
        }
        t.last_leaf = Self::arena_idx_from(m - 1);
        // The mark/restore archives: this builds an arena from nothing and never
        // marks, so both are empty and parallel to the (also empty) arena snapshot
        // stack. Written rather than merely asserted, so neither level builder has
        // to carry a framing postcondition for a field it does not touch.
        t.header_archive = std::vec::Vec::new();
        t.tree_snapshots = Ghost(Seq::empty());
        proof {
            reveal(tree_archive_agrees);
            assert(t.arena().len() == lo + 1);
            assert(t.arena().len() == crate::bplus_tree::node_count(t.tree@));
            assert(t.arena().len() <= 2 * m);
            assert(t.model() =~= Seq::new(n as nat, |i: int| keys@[i].id_nat()));
        }
        t
    }

    /// Bulk-build from strictly ascending keys (production `from_sorted`
    /// surface). VERIFIED: total, `wf`, and the resulting model's key set is
    /// exactly the input's.
    ///
    /// A thin wrapper over [`bulk_load`], the bottom-up loader: one pass per
    /// level into a fresh arena, no per-key `insert` and therefore no split
    /// cycle. The two cases the loader does not cover are handled here — an empty
    /// input (which is `new`, a tree with one empty root leaf) and the model-set
    /// postconditions, which restate the loader's exact-sequence guarantee in the
    /// set form the callers use.
    ///
    /// **Why not the insert loop it replaced.** That version batched by leaf
    /// (a `fast_append_run` helper filled the whole rightmost leaf per arena
    /// write, since a per-key whole-node copy costs 20-25x an in-place slot
    /// write) and
    /// still measured 10.6x production at n = 100k: min-occupancy forces an
    /// `insert` at every leaf boundary, and each of those splits and propagates,
    /// which is ~60% of the run. The loader partitions the input up front instead,
    /// so no split ever happens — and it does strictly less work than production
    /// besides (see `bulk_load`'s doc: no per-level index vector, no separate link
    /// pass, no `first_key_word` descent).
    pub fn from_sorted(keys: &[K]) -> (t: Self)
        ensures
            t.wf(),
            t.model().len() == keys@.len(),
            forall|i: int| 0 <= i < keys@.len()
                ==> t.model().to_set().contains((#[trigger] keys@[i]).id_nat()),
            forall|v: nat| t.model().to_set().contains(v)
                ==> exists|i: int| 0 <= i < keys@.len() && (#[trigger] keys@[i]).id_nat() == v,
    {
        // Total-with-documented-panic: the three erased requires become
        // branches — the static key fact, the length ceiling, and the
        // ascending-distinct check (O(n) against the build's n log n), whose
        // loop invariant lifts adjacent comparisons to the global forall the
        // body's proofs consume.
        if !K::bit_stealing() {
            crate::guard::refuse("BPlusTreeSet::from_sorted: key type does not steal a bit");
        }
        if !(keys.len() < usize::MAX) {
            crate::guard::refuse("BPlusTreeSet::from_sorted: too many keys");
        }
        if keys.len() > 1 {
            let mut ci: usize = 1;
            while ci < keys.len()
                invariant
                    1 <= ci <= keys@.len(),
                    keys@.len() < usize::MAX,
                    forall|a: int, b: int| 0 <= a < b < ci
                        ==> (#[trigger] keys@[a]).id_nat() < (#[trigger] keys@[b]).id_nat(),
                decreases keys@.len() - ci,
            {
                if !(keys[ci - 1].to_usize() < keys[ci].to_usize()) {
                    crate::guard::refuse("BPlusTreeSet::from_sorted: keys not strictly ascending");
                }
                proof {
                    assert forall|a: int, b: int| 0 <= a < b < ci + 1
                        implies (#[trigger] keys@[a]).id_nat() < (#[trigger] keys@[b]).id_nat() by {
                        if b == ci as int && a < ci - 1 {
                            assert(keys@[a].id_nat() < keys@[ci - 1].id_nat());
                        }
                    }
                }
                ci += 1;
            }
        }
        if keys.len() == 0 {
            let t = Self::new();
            proof { assert(t.model() =~= Seq::<nat>::empty()); }
            return t;
        }
        let t = Self::bulk_load(keys);
        proof {
            // The loader returns the model as the input's id sequence VERBATIM, so
            // both set arms are index arithmetic.
            let ids = Seq::new(keys@.len(), |i: int| keys@[i].id_nat());
            assert(t.model() == ids);
            assert forall|i: int| 0 <= i < keys@.len() implies
                t.model().to_set().contains((#[trigger] keys@[i]).id_nat()) by {
                assert(t.model()[i] == keys@[i].id_nat());
            }
            assert forall|v: nat| t.model().to_set().contains(v) implies
                exists|i: int| 0 <= i < keys@.len() && (#[trigger] keys@[i]).id_nat() == v by {
                let b = choose|b: int| 0 <= b < t.model().len() && t.model()[b] == v;
                assert(keys@[b].id_nat() == v);
            }
        }
        t
    }

    /// A fresh cursor over this tree (production `tree.cursor()` parity;
    /// delegates to `BPlusCursor::new` — exhausted until `seek`/`seek_first`).
    pub fn cursor(&self) -> (c: BPlusCursor<'_, K, L, S, TRACK>)
        requires self.wf(),
        ensures c.tree_ref() == self, c.cursor_wf(), c.idx() == c.model().len(),
    {
        BPlusCursor::new(self)
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
            let node = self.nodes.get_index(idx);
            proof { assert(self.arena()[idx.as_nat() as int] == node); }

            if L::is_leaf(&node) {
                // Leaf: search it through `S`, then probe the boundary.
                // Production: `S::find_ge` at bplus.rs:796.
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
                proof {
                    assert(gkeys.len() == n as nat);
                    assert(L::node_wf(node));
                    lemma_tree_wf_sorted_seps_view::<L>(self.arena(), cur, idx.as_nat(), node);
                }
                let pos = self.leaf_find_ge(&node, kw);
                proof {
                    assert(pos as nat <= gkeys.len());
                    assert forall|j: int| 0 <= j < pos implies gkeys[j] < k by {
                        assert(L::keys_view(node)[j].as_nat() == gkeys[j]);
                    }
                    assert forall|j: int| pos <= j < n implies k <= gkeys[j] by {
                        assert(L::keys_view(node)[j].as_nat() == gkeys[j]);
                    }
                }

                // Present iff keys[pos] <= k as well (find_ge already gives >=).
                if pos < n {
                    let ki: L::Word = L::key(&node, pos);
                    let le = ki.le(kw);
                    proof {
                        <L::Word as IndexLike>::lemma_order_is_as_nat(ki, kw);
                        assert(ki == L::keys_view(node)[pos as int]);
                        assert(ki.as_nat() == gkeys[pos as int]);
                    }
                    if le {
                        proof {
                            assert(gkeys[pos as int] == k);
                            assert(crate::bplus_tree::tree_contains(cur, k));
                            // bridge to the model: model == tree_keys(self.tree@) and
                            // tree_contains(self.tree@,k) == that.contains(k).
                            assert(crate::bplus_tree::tree_contains(self.tree@, k));
                            assert(crate::bplus_tree::tree_keys(self.tree@).contains(k));
                            assert(self.model() == crate::bplus_tree::tree_keys(self.tree@));
                            assert(self.model().contains(key.id_nat()));
                        }
                        return true;
                    }
                }
                proof {
                    // absent: left of pos is < k; from pos on is > k (>= k with
                    // gkeys[pos] != k, lifted by strict sortedness).
                    assert(crate::bplus_tree::strictly_sorted(gkeys));
                    assert forall|j: int| 0 <= j < gkeys.len() implies gkeys[j] != k by {
                        if pos <= j && pos < j { assert(gkeys[pos as int] < gkeys[j]); }
                    }
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

            // cp = find_gt(seps, key), through `S`. Production: `S::find_gt`
            // at bplus.rs:800.
            proof { lemma_tree_wf_sorted_seps_view::<L>(self.arena(), cur, gid, node); }
            let cp = self.find_child(&node, kw);
            // The find_gt characterization on the ghost separators: [0..cp) <= k,
            // [cp..) > k — lifted from find_child's key-view postcondition.
            proof {
                assert(cp as nat <= gseps.len());
                assert forall|j: int| 0 <= j < cp implies gseps[j] <= k by {
                    assert(L::keys_view(node)[j].as_nat() == gseps[j]);
                }
                assert forall|i: int| cp <= i < gseps.len() implies k < gseps[i] by {
                    assert(L::keys_view(node)[i].as_nat() == gseps[i]);
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

// ===== LAYER 2: insert (+ M6 arena-never-overflows) and split/reconstruct machinery =====


/// `model_bounded` is preserved by inserting a bounded value at any position:
/// the insert-only model transition. `m.insert(pos, v)` stays bounded when `m`
/// is and `v < id_bound` (which `lemma_id_nat_bounded` gives for a real key).
pub(crate) proof fn lemma_model_bounded_insert<K: DenseId>(m: Seq<nat>, pos: int, v: nat)
    requires
        model_bounded::<K>(m),
        v < K::id_bound(),
        0 <= pos <= m.len(),
    ensures model_bounded::<K>(m.insert(pos, v)),
{
    let m2 = m.insert(pos, v);
    assert forall|i: int| 0 <= i < m2.len() implies #[trigger] m2[i] < K::id_bound() by {
        if i < pos { assert(m2[i] == m[i]); }
        else if i == pos { assert(m2[i] == v); }
        else { assert(m2[i] == m[i - 1]); }
    }
}

/// `model_bounded` for a model expressed as a `to_set` insertion: if the new
/// model SET is `old ∪ {v}` (the recursion's form), bounded carries when `old`
/// is and `v < id_bound`. Used by the split/general paths whose ensures speak of
/// the set, via the strictly-sorted seq-vs-set length bridge (B-side).
/// `push`'s effect on the element set. The fast path returns a `push`-shaped
/// model transition (it appends at the end); `insert`'s public contract states
/// the set-shaped one.
pub(crate) proof fn lemma_push_to_set(m: Seq<nat>, v: nat)
    ensures m.push(v).to_set() == m.to_set().insert(v),
{
    let p = m.push(v);
    assert forall|x: nat| #![trigger p.to_set().contains(x)] p.to_set().contains(x) implies m.to_set().insert(v).contains(x) by {
        let i = choose|i: int| 0 <= i < p.len() && p[i] == x;
        if i < m.len() {
            assert(m[i] == x);
        }
    }
    assert forall|x: nat| #![trigger p.to_set().contains(x)] m.to_set().insert(v).contains(x) implies p.to_set().contains(x) by {
        if x == v {
            assert(p[m.len() as int] == v);
        } else {
            let i = choose|i: int| 0 <= i < m.len() && m[i] == x;
            assert(p[i] == x);
        }
    }
    assert(p.to_set() =~= m.to_set().insert(v));
}

pub(crate) proof fn lemma_model_bounded_set<K: DenseId>(m: Seq<nat>, old: Seq<nat>, v: nat)
    requires
        model_bounded::<K>(old),
        v < K::id_bound(),
        m.to_set() == old.to_set().insert(v),
    ensures model_bounded::<K>(m),
{
    assert forall|i: int| 0 <= i < m.len() implies #[trigger] m[i] < K::id_bound() by {
        // m[i] is in m.to_set() == old.to_set() ∪ {v}; either old (bounded) or v.
        assert(m.to_set().contains(m[i]));
        if old.to_set().contains(m[i]) {
            let j = choose|j: int| 0 <= j < old.len() && old[j] == m[i];
        }
    }
}

/// `forest_links_to(kids)` composes to `leaf_links_to(Inner{.., kids})`: if every
/// child's chain threads to the next child's first leaf (and the last to `succ`),
/// the parent's whole-subtree chain holds. Each child must be non-empty
/// (`tree_leaf_ids(kids[i]).len() >= 1`), which `tree_wf` guarantees. Ported from
/// a standalone 7-lemma probe.
pub(crate) proof fn lemma_forest_links_compose<L: NodeLayout>(
    arena: Seq<L::Node>,
    id: nat,
    seps: Seq<nat>,
    kids: Seq<Tree>,
    succ: nat,
)
    requires
        forest_links_to::<L>(arena, kids, succ),
        forall|i: int| 0 <= i < kids.len() ==> #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1,
    ensures
        leaf_links_to::<L>(arena, Tree::Inner { id, seps, kids }, succ),
    decreases kids,
{
    let t = Tree::Inner { id, seps, kids };
    let l = crate::bplus_tree::tree_leaf_ids(t);
    assert(l == crate::bplus_tree::forest_leaf_ids(kids));
    if kids.len() == 0 {
        assert(l =~= Seq::<nat>::empty());
    } else {
        let df = kids.drop_first();
        let head = crate::bplus_tree::tree_leaf_ids(kids[0]);
        let tl = crate::bplus_tree::forest_leaf_ids(df);
        crate::bplus_tree::lemma_forest_leaf_ids_cons(kids);
        assert(l == head + tl);
        let s0 = if kids.len() > 1 { crate::bplus_tree::tree_leaf_ids(kids[1])[0] } else { succ };
        // recurse: leaf_links_to(Inner{.., df}, succ).
        let did = id;  // any id; the inner-node id is irrelevant to tree_leaf_ids.
        assert forall|i: int| 0 <= i < df.len() implies
            #[trigger] crate::bplus_tree::tree_leaf_ids(df[i]).len() >= 1 by {
            assert(df[i] == kids[i + 1]);
        }
        lemma_forest_links_compose::<L>(arena, did, seps, df, succ);
        let ld = crate::bplus_tree::tree_leaf_ids(Tree::Inner { id: did, seps, kids: df });
        assert(ld == tl);
        assert forall|p: int| 0 <= p < l.len() implies
            #[trigger] L::link_view(arena[l[p] as int]) == (if p + 1 < l.len() { l[p + 1] } else { succ }) by {
            if p < head.len() {
                assert(l[p] == head[p]);
                // leaf_links_to(kids[0], s0) at p.
                assert(L::link_view(arena[head[p] as int])
                    == (if p + 1 < head.len() { head[p + 1] } else { s0 }));
                if p + 1 < head.len() {
                    assert(l[p + 1] == head[p + 1]);
                } else {
                    // p == head.len()-1.
                    if df.len() > 0 {
                        assert(kids[1] == df[0]);
                        let hd0 = crate::bplus_tree::tree_leaf_ids(df[0]);
                        crate::bplus_tree::lemma_forest_leaf_ids_cons(df);
                        assert(tl == hd0 + crate::bplus_tree::forest_leaf_ids(df.drop_first()));
                        assert(hd0.len() >= 1);
                        assert(tl[0] == hd0[0]);
                        assert(s0 == hd0[0]);
                        assert(l[head.len() as int] == tl[0]);
                        assert(l[p + 1] == s0);
                    } else {
                        assert(l =~= head);
                        assert(s0 == succ);
                    }
                }
            } else {
                let q = p - head.len();
                assert(l[p] == tl[q]);
                // recursive leaf_links_to(Inner{.., df}, succ) at q (trigger ld[q]).
                assert(L::link_view(arena[ld[q] as int])
                    == (if q + 1 < ld.len() { ld[q + 1] } else { succ }));
                assert(L::link_view(arena[tl[q] as int])
                    == (if q + 1 < tl.len() { tl[q + 1] } else { succ }));
                if p + 1 < l.len() {
                    assert(l[p + 1] == tl[q + 1]);
                }
            }
        }
    }
}

/// Grow a fresh root over the two halves of a ROOT split (the M4b new-root move,
/// generalized from leaves to arbitrary subtrees). Given `nl`/`nr` both
/// `subtree_wf` at height `h` in the post-push arena `a2` (nl links to nr's first
/// leaf, nr links to NIL), the median ordering around `sep`, the combined model
/// `old ∪ {key}`, disjoint footprints, and the fresh root node `new_root` at
/// `nri` (binding `[lid, rid]`), the new tree `Inner{nri, [sep], [nl, nr]}` is a
/// whole-tree-`wf` B+tree of height `h+1` whose model is `old ∪ {key}`.
///
/// `a1` (pre-push) and `a2 == a1.push(new_root)` are two snapshots of the single
/// arena; nl/nr already bind in a1 (the recursion's result) and a tail push
/// preserves that.
pub(crate) proof fn lemma_insert_new_root<K, L, S, const TRACK: bool>(
    a1: Ghost<Seq<L::Node>>,
    a2: Ghost<Seq<L::Node>>,
    old_model: Ghost<Seq<nat>>,
    nl: Ghost<Tree>,
    nr: Ghost<Tree>,
    sep: L::Word,
    lid: Ghost<nat>,
    rid: L::ArenaIdx,
    nri: Ghost<nat>,
    new_root: Ghost<L::Node>,
    h: Ghost<nat>,
    key: K,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        // the two halves are wf (non-root) at height h in a1, chained nl -> nr -> NIL.
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(a1@, nl@, h@,
            crate::bplus_tree::tree_leaf_ids(nr@)[0], false),
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(a1@, nr@, h@, nil_link::<L>(), false),
        crate::bplus_tree::tree_root_id(nl@) == lid@,
        crate::bplus_tree::tree_root_id(nr@) == rid.as_nat(),
        crate::bplus_tree::tree_keys(nr@).len() >= 1,
        crate::bplus_tree::tree_leaf_ids(nr@).len() >= 1,
        // median ordering + model: nl < sep <= nr, combined == old ∪ {key}.
        crate::bplus_tree::keys_all_lt(nl@, sep.as_nat()),
        crate::bplus_tree::keys_all_ge(nr@, sep.as_nat()),
        (crate::bplus_tree::tree_keys(nl@) + crate::bplus_tree::tree_keys(nr@)).to_set()
            == old_model@.to_set().insert(key.id_nat()),
        // disjoint footprints (a split puts the halves in separate regions).
        crate::bplus_tree::tree_ids(nl@).disjoint(crate::bplus_tree::tree_ids(nr@)),
        // the fresh root: pushed at nri == a1.len(), a2 == a1.push(new_root).
        a2@ == a1@.push(new_root@),
        nri@ == a1@.len(),
        !L::is_leaf_spec(new_root@),
        L::node_wf(new_root@),
        L::count_spec(new_root@) == 1,
        L::keys_view(new_root@) == seq![sep],
        L::child_view(new_root@, 0) == lid@,
        L::child_view(new_root@, 1) == rid.as_nat(),
        // nl/nr's footprints are old slots (< a1.len()), so the fresh nri is outside.
        (forall|id: nat| crate::bplus_tree::tree_ids(nl@).contains(id) ==> id < a1@.len()),
        (forall|id: nat| crate::bplus_tree::tree_ids(nr@).contains(id) ==> id < a1@.len()),
        // old model is strictly sorted (it was tree_keys of a wf tree) — lets the
        // length bookkeeping go through the set cardinality.
        crate::bplus_tree::strictly_sorted(old_model@),
    ensures
        ({
            let nt = Tree::Inner { id: nri@, seps: seq![sep.as_nat()], kids: seq![nl@, nr@] };
            &&& BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(a2@, nt, (h@ + 1) as nat, nil_link::<L>(), true)
            &&& crate::bplus_tree::tree_root_id(nt) == nri@
            &&& crate::bplus_tree::tree_height(nt) == h@ + 1
            &&& crate::bplus_tree::tree_keys(nt).to_set() == old_model@.to_set().insert(key.id_nat())
            &&& crate::bplus_tree::tree_keys(nt).len() == old_model@.len() + (if old_model@.contains(key.id_nat()) { 0int } else { 1int })
        }),
{
    let nt = Tree::Inner { id: nri@, seps: seq![sep.as_nat()], kids: seq![nl@, nr@] };
    let kids = seq![nl@, nr@];
    let a1s = a1@; let a2s = a2@;
    L::lemma_arena_capacity();

    // nl/nr still bind / link in a2 (a1 -> a2 is a single tail push; nl/nr ids are
    // all < a1.len() == nri, so the new slot doesn't touch their footprints).
    assert(a2s == a1s.push(new_root@));
    assert(a1s.len() <= a2s.len());
    assert forall|id: nat| #![trigger a1s[id as int]] #![trigger a2s[id as int]] crate::bplus_tree::tree_ids(nl@).contains(id) implies a1s[id as int] == a2s[id as int] by {
        assert(id < a1s.len());            // precondition
        assert(a2s[id as int] == a1s[id as int]);  // push leaves old slots unchanged
    }
    assert forall|id: nat| #![trigger a1s[id as int]] #![trigger a2s[id as int]] crate::bplus_tree::tree_ids(nr@).contains(id) implies a1s[id as int] == a2s[id as int] by {
        assert(id < a1s.len());
        assert(a2s[id as int] == a1s[id as int]);
    }
    lemma_binds_frame::<L>(a1s, a2s, nl@);
    lemma_binds_frame::<L>(a1s, a2s, nr@);
    lemma_leaf_links_frame::<L>(a1s, a2s, nl@, crate::bplus_tree::tree_leaf_ids(nr@)[0]);
    lemma_leaf_links_frame::<L>(a1s, a2s, nr@, nil_link::<L>());

    // ---- binds(a2, nt). ----
    assert(binds::<L>(a2s, nl@));
    assert(binds::<L>(a2s, nr@));
    // forest_binds_l([nl, nr]) unfolds to binds(nl) && forest_binds_l([nr]) ==
    // binds(nl) && binds(nr) && forest_binds_l([]). Build it bottom-up.
    assert(forest_binds_l::<L>(a2s, Seq::<Tree>::empty()));
    assert(forest_binds_l::<L>(a2s, seq![nr@])) by {
        assert(seq![nr@][0] == nr@);
        assert(seq![nr@].drop_first() =~= Seq::<Tree>::empty());
    }
    assert(forest_binds_l::<L>(a2s, kids)) by {
        assert(kids[0] == nl@);
        assert(kids.drop_first() =~= seq![nr@]);
    }
    assert(nri@ < a2s.len());
    assert(a2s[nri@ as int] == new_root@);  // pushed at nri == a1.len()
    assert forall|i: int| 0 <= i < kids.len() implies
        L::child_view(new_root@, i) == crate::bplus_tree::tree_root_id(#[trigger] kids[i]) by {
        if i == 0 { assert(kids[0] == nl@); } else { assert(kids[1] == nr@); }
    }
    assert(binds::<L>(a2s, nt));

    // ---- tree_wf(nt, h+1, is_root=true). ----
    crate::bplus_tree::lemma_tree_wf_height(nl@, h@, L::leaf_cap_spec(), L::key_cap_spec(), false);
    crate::bplus_tree::lemma_tree_wf_height(nr@, h@, L::leaf_cap_spec(), L::key_cap_spec(), false);
    assert(crate::bplus_tree::tree_wf(nl@, h@, L::leaf_cap_spec(), L::key_cap_spec(), false));
    assert(crate::bplus_tree::tree_wf(nr@, h@, L::leaf_cap_spec(), L::key_cap_spec(), false));
    // forest_wf([nl, nr], h): both children wf at h.
    assert(crate::bplus_tree::forest_wf(kids, h@, L::leaf_cap_spec(), L::key_cap_spec())) by {
        crate::bplus_tree::lemma_forest_wf_cons(kids, h@, L::leaf_cap_spec(), L::key_cap_spec());
        assert(kids.drop_first() =~= seq![nr@]);
        crate::bplus_tree::lemma_forest_wf_cons(seq![nr@], h@, L::leaf_cap_spec(), L::key_cap_spec());
        assert(seq![nr@].drop_first() =~= Seq::<Tree>::empty());
    }
    // cross-node ordering: kids[0]==nl < seps[0]==sep, kids[1]==nr >= sep.
    assert forall|i: int| 0 <= i < 1int implies crate::bplus_tree::keys_all_lt(#[trigger] kids[i], seq![sep.as_nat()][i]) by {
        assert(kids[0] == nl@);
    }
    assert forall|i: int| 0 < i < 2int implies crate::bplus_tree::keys_all_ge(#[trigger] kids[i], seq![sep.as_nat()][i - 1]) by {
        assert(kids[1] == nr@);
    }
    // height: tree_height(nt) == 1 + max child height == 1 + h.
    crate::bplus_tree::lemma_forest_wf_max_height(kids, h@, L::leaf_cap_spec(), L::key_cap_spec());
    assert(crate::bplus_tree::tree_height(nt) == h@ + 1) by {
        crate::bplus_tree::lemma_forest_max_height_at(kids, 0);
    }
    assert(crate::bplus_tree::strictly_sorted(seq![sep.as_nat()]));
    assert(crate::bplus_tree::tree_wf(nt, (h@ + 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), true));

    // ---- leaf_links_ok(a2, nt): nl -> nr's first leaf, nr -> NIL; compose. ----
    assert forall|i: int| 0 <= i < kids.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1 by {
        if i == 0 {
            crate::bplus_tree::lemma_tree_leaf_ids_nonempty(nl@, h@, L::leaf_cap_spec(), L::key_cap_spec(), false);
        } else { assert(kids[1] == nr@); }
    }
    assert(forest_links_to::<L>(a2s, kids, nil_link::<L>())) by {
        // forest_links_to cons: nl -> kids[1]'s first leaf == nr[0], then nr -> NIL.
        assert(kids.drop_first() =~= seq![nr@]);
        assert(crate::bplus_tree::tree_leaf_ids(kids[1])[0] == crate::bplus_tree::tree_leaf_ids(nr@)[0]);
        lemma_forest_links_cons::<L>(a2s, seq![nr@], nil_link::<L>());
        assert(seq![nr@].drop_first() =~= Seq::<Tree>::empty());
    }
    lemma_forest_links_compose::<L>(a2s, nri@, seq![sep.as_nat()], kids, nil_link::<L>());
    assert(leaf_links_ok::<L>(a2s, nt));

    // ---- tree_disjoint(nt): nri ∉ {nl,nr footprints} (fresh), nl ⊥ nr. ----
    crate::bplus_tree::lemma_forest_ids_cons(kids);
    assert(kids.drop_first() =~= seq![nr@]);
    crate::bplus_tree::lemma_forest_ids_cons(seq![nr@]);
    assert(seq![nr@].drop_first() =~= Seq::<Tree>::empty());
    assert(crate::bplus_tree::forest_ids(kids) =~=
        crate::bplus_tree::tree_ids(nl@).union(crate::bplus_tree::tree_ids(nr@)));
    assert(!crate::bplus_tree::forest_ids(kids).contains(nri@)) by {
        // every nl/nr id is < a1.len() == nri.
    }
    assert(crate::bplus_tree::forest_disjoint(kids)) by {
        crate::bplus_tree::lemma_forest_disjoint_cons(kids);
        crate::bplus_tree::lemma_forest_disjoint_cons(seq![nr@]);
    }
    assert forall|i: int, j: int| 0 <= i < j < kids.len() implies
        (#[trigger] crate::bplus_tree::tree_ids(kids[i])).disjoint(#[trigger] crate::bplus_tree::tree_ids(kids[j])) by {
        assert(kids[0] == nl@ && kids[1] == nr@);
    }
    assert(crate::bplus_tree::tree_disjoint(nt));

    // ---- model: tree_keys(nt) == tree_keys(nl) + tree_keys(nr). ----
    crate::bplus_tree::lemma_forest_keys_cons(kids);
    assert(kids.drop_first() =~= seq![nr@]);
    crate::bplus_tree::lemma_forest_keys_cons(seq![nr@]);
    assert(seq![nr@].drop_first() =~= Seq::<Tree>::empty());
    assert(crate::bplus_tree::tree_keys(nt) == crate::bplus_tree::tree_keys(nl@) + crate::bplus_tree::tree_keys(nr@));
    assert(crate::bplus_tree::tree_keys(nt).to_set() == old_model@.to_set().insert(key.id_nat()));
    // length: tree_keys(nt) and old_model are both strictly sorted, so each length
    // equals its set's cardinality; |old.set ∪ {key}| == |old.set| + (key∈? 0:1).
    crate::bplus_tree::lemma_tree_wf_sorted(nt, (h@ + 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), true);
    crate::bplus_tree::lemma_strictly_sorted_len_eq_set(crate::bplus_tree::tree_keys(nt));
    crate::bplus_tree::lemma_strictly_sorted_len_eq_set(old_model@);
    assert(crate::bplus_tree::tree_keys(nt).to_set().len()
        == old_model@.to_set().len() + (if old_model@.to_set().contains(key.id_nat()) { 0int } else { 1int })) by {
        if old_model@.to_set().contains(key.id_nat()) {
            assert(old_model@.to_set().insert(key.id_nat()) =~= old_model@.to_set());
        }
    }
    assert(old_model@.to_set().contains(key.id_nat()) == old_model@.contains(key.id_nat()));
}

/// Every id in a bound tree's footprint is a real arena slot: `binds(arena, t)
/// && tree_ids(t).contains(id) ==> id < arena.len()`. The in-range clause, used
/// to frame the recursion (slots outside the subtree stay in range).
pub(crate) proof fn lemma_tree_id_in_range<L: NodeLayout>(arena: Seq<L::Node>, t: Tree, id: nat)
    requires binds::<L>(arena, t), crate::bplus_tree::tree_ids(t).contains(id),
    ensures id < arena.len(),
    decreases t,
{
    match t {
        Tree::Leaf { id: lid, .. } => { assert(id == lid); }
        Tree::Inner { id: iid, seps, kids } => {
            if id == iid {
            } else {
                crate::bplus_tree::lemma_forest_ids_cons(kids);
                assert(crate::bplus_tree::forest_ids(kids).contains(id));
                crate::bplus_tree::lemma_forest_id_in_some_child(kids, id);
                let m = choose|m: int| 0 <= m < kids.len()
                    && (#[trigger] crate::bplus_tree::tree_ids(kids[m])).contains(id);
                lemma_forest_binds_at::<L>(arena, kids, m);
                lemma_tree_id_in_range::<L>(arena, kids[m], id);
            }
        }
    }
}

/// `tree_ids(kids[cp]) ⊆ tree_ids(Inner{.., kids})`: a child footprint id is a
/// parent footprint id. So an id *outside* the parent footprint is outside every
/// child's — the frame containment the recursion needs.
pub(crate) proof fn lemma_child_ids_subset_tree<L: NodeLayout>(t: Tree, cp: int, id: nat)
    requires
        t is Inner,
        0 <= cp < t->Inner_kids.len(),
        crate::bplus_tree::tree_ids(t->Inner_kids[cp]).contains(id),
    ensures
        crate::bplus_tree::tree_ids(t).contains(id),
{
    let kids = t->Inner_kids;
    crate::bplus_tree::lemma_forest_ids_cons(kids);
    crate::bplus_tree::lemma_child_ids_in_forest(kids, cp, id);
    assert(crate::bplus_tree::forest_ids(kids).contains(id));
}

/// Project a parent's leaf-link chain to child `cp`: `leaf_links_to(arena,
/// Inner{.., kids}, succ)` gives `leaf_links_to(arena, kids[cp], child_succ)`
/// where `child_succ` is `kids[cp+1]`'s first leaf (or `succ` if `cp` is last).
/// The decomposition direction (inverse of `lemma_forest_links_compose`), via
/// the `forest_leaf_ids` slice. Each child non-empty.
/// Reconstruct `subtree_wf` for the absorb branch of `insert_rec`'s internal
/// case. The child `cp` of `cur` became `ncl` (same root id, model gained `key`,
/// `subtree_wf` at `h-1` with the child's successor); the arena grew only inside
/// the child's region. Conclude the parent `Inner{gid, gseps, gkids.update(cp,
/// ncl)}` is `subtree_wf(arena2, _, h, succ)`, with model = old ∪ {key} and root
/// id `gid`. Pure assembly of the landed forest-update + frame + ordering lemmas.
pub(crate) proof fn reconstruct_absorb<K, L, S, const TRACK: bool>(
    arena1: Ghost<Seq<L::Node>>,
    arena2: Ghost<Seq<L::Node>>,
    cur: Ghost<Tree>,
    ncl: Ghost<Tree>,
    gid: Ghost<nat>,
    gseps: Ghost<Seq<nat>>,
    gkids: Ghost<Seq<Tree>>,
    cp: Ghost<int>,
    h: Ghost<nat>,
    succ: Ghost<nat>,
    child_succ: Ghost<nat>,
    key: K,
    node: Ghost<L::Node>,
    is_root: Ghost<bool>,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        cur@ == (Tree::Inner { id: gid@, seps: gseps@, kids: gkids@ }),
        h@ == crate::bplus_tree::tree_height(cur@),
        0 <= cp@ < gkids@.len(),
        // `cur` wf at the caller's root-ness; the rebuilt `nt` has the SAME
        // separators (absorb doesn't change this node's seps), so its occupancy
        // equals cur's and the output re-establishes at the same `is_root`.
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena1@, cur@, h@, succ@, is_root@),
        // the child result (genuinely non-root):
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena2@, ncl@, (h@ - 1) as nat, child_succ@, false),
        crate::bplus_tree::tree_root_id(ncl@) == crate::bplus_tree::tree_root_id(gkids@[cp@]),
        crate::bplus_tree::tree_keys(ncl@).to_set()
            == crate::bplus_tree::tree_keys(gkids@[cp@]).to_set().insert(key.id_nat()),
        // CHILD FOOTPRINT: subset+freshness, NOT exact equality — a node deep
        // under child cp may have split and been absorbed, so `ncl` carries the
        // old child's ids PLUS fresh tail slots (>= arena1.len()). The leftmost
        // leaf is pinned (splits add to the right). (Contract fix; (F0).)
        crate::bplus_tree::tree_ids(gkids@[cp@]).subset_of(crate::bplus_tree::tree_ids(ncl@)),
        (forall|id: nat| #[trigger] crate::bplus_tree::tree_ids(ncl@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        crate::bplus_tree::tree_leaf_ids(ncl@)[0] == crate::bplus_tree::tree_leaf_ids(gkids@[cp@])[0],
        // (weakening) ncl-min precondition REMOVED (separator-min cluster).
        child_succ@ == (if cp@ + 1 < gkids@.len() {
            crate::bplus_tree::tree_leaf_ids(gkids@[cp@ + 1])[0]
        } else { succ@ }),
        // arena2 grew and agrees with arena1 outside the child's footprint.
        arena1@.len() <= arena2@.len(),
        arena2@[gid@ as int] == node@,
        arena1@[gid@ as int] == node@,
        forall|id: nat| (#[trigger] crate::bplus_tree::tree_ids(cur@).contains(id))
            && !crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
            ==> arena1@[id as int] == arena2@[id as int],
        // the descent routed `key` into child cp (find_gt characterization).
        forall|j: int| 0 <= j < cp@ ==> gseps@[j] <= key.id_nat(),
        forall|j: int| cp@ <= j < gseps@.len() ==> key.id_nat() < gseps@[j],
    ensures
        ({
            let nkids = gkids@.update(cp@, ncl@);
            let nt = Tree::Inner { id: gid@, seps: gseps@, kids: nkids };
            &&& BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena2@, nt, h@, succ@, is_root@)
            &&& crate::bplus_tree::tree_root_id(nt) == gid@
            // PARENT FOOTPRINT: same subset+freshness propagated up one level.
            &&& crate::bplus_tree::tree_ids(cur@).subset_of(crate::bplus_tree::tree_ids(nt))
            &&& (forall|id: nat| crate::bplus_tree::tree_ids(nt).contains(id)
                    ==> crate::bplus_tree::tree_ids(cur@).contains(id) || id >= arena1@.len())
            &&& crate::bplus_tree::tree_leaf_ids(nt)[0] == crate::bplus_tree::tree_leaf_ids(cur@)[0]
            // min-key preservation propagated up: when key isn't a new min, nt
            // keeps cur's leftmost key.
                        // (weakening) min-key-preservation ensures clause REMOVED.
            &&& crate::bplus_tree::tree_keys(nt).to_set()
                    == crate::bplus_tree::tree_keys(cur@).to_set().insert(key.id_nat())
        }),
{
    let nkids = gkids@.update(cp@, ncl@);
    let nt = Tree::Inner { id: gid@, seps: gseps@, kids: nkids };
    let a1 = arena1@; let a2 = arena2@;
    L::lemma_arena_capacity();  // 1 <= leaf_cap (for lemma_tree_keys_nonempty)
    // unpack cur's subtree_wf: tree_wf(cur,h) at is_root@; relax to root-form for
    // the structural Inner-arm facts (count, forest_wf, ordering — not occupancy).
    if !is_root@ {
        crate::bplus_tree::lemma_tree_wf_relax_root(cur@, h@, L::leaf_cap_spec(), L::key_cap_spec());
    }
    assert(crate::bplus_tree::tree_wf(cur@, h@, L::leaf_cap_spec(), L::key_cap_spec(), true));
    assert(gkids@.len() == gseps@.len() + 1);  // tree_wf Inner arm

    // (1) binds(a2, nt): forest_binds_update over the updated child.
    assert(forest_binds_l::<L>(a1, gkids@));        // from binds(a1, cur) Inner arm
    assert(binds::<L>(a2, ncl@));                   // from child subtree_wf
    assert forall|i: int, j: int| 0 <= i < j < gkids@.len() implies
        (#[trigger] crate::bplus_tree::tree_ids(gkids@[i]))
            .disjoint(#[trigger] crate::bplus_tree::tree_ids(gkids@[j])) by {
        // tree_disjoint(cur) Inner arm.
    }
    assert forall|id: nat| (#[trigger] crate::bplus_tree::forest_ids(gkids@).contains(id))
        && !crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
        implies a1[id as int] == a2[id as int] by {
        // forest_ids(kids) ⊆ tree_ids(cur), and id outside the child region.
        assert(crate::bplus_tree::tree_ids(cur@).contains(id));
    }
    lemma_forest_binds_update::<L>(a1, a2, gkids@, cp@, ncl@);
    // binds(a2, nt) Inner arm: node fields at gid unchanged (a2[gid]==node==a1[gid]),
    // child_view reads gid's node (unchanged) == kids' root ids (root id preserved).
    assert(a2[gid@ as int] == a1[gid@ as int]);
    assert forall|i: int| 0 <= i < nkids.len() implies
        L::child_view(a2[gid@ as int], i) == crate::bplus_tree::tree_root_id(#[trigger] nkids[i]) by {
        if i == cp@ {
            assert(nkids[i] == ncl@);
            assert(crate::bplus_tree::tree_root_id(ncl@) == crate::bplus_tree::tree_root_id(gkids@[cp@]));
        } else {
            assert(nkids[i] == gkids@[i]);
        }
    }
    assert(binds::<L>(a2, nt));

    // (2) tree_wf(a2-independent): forest_wf update + cross-node ordering.
    crate::bplus_tree::lemma_forest_wf_update(gkids@, (h@ - 1) as nat,
        L::leaf_cap_spec(), L::key_cap_spec(), cp@, ncl@);
    // cross-node ordering: child cp gained `key`, which the descent bounded by
    // seps[cp-1] <= key < seps[cp]; other children unchanged.
    assert forall|i: int| 0 <= i < gseps@.len() implies
        crate::bplus_tree::keys_all_lt(#[trigger] nkids[i], gseps@[i]) by {
        if i == cp@ {
            // keys_all_lt(ncl, seps[cp]): old child < seps[cp] AND key < seps[cp].
            crate::bplus_tree::lemma_keys_all_lt_set(gkids@[cp@], gseps@[i]);
            crate::bplus_tree::lemma_keys_all_lt_set(ncl@, gseps@[i]);
            assert(key.id_nat() < gseps@[cp@]);
        } else {
            assert(nkids[i] == gkids@[i]);
        }
    }
    assert forall|i: int| 0 < i < nkids.len() implies
        crate::bplus_tree::keys_all_ge(#[trigger] nkids[i], gseps@[i - 1]) by {
        if i == cp@ {
            crate::bplus_tree::lemma_keys_all_ge_set(gkids@[cp@], gseps@[i - 1]);
            crate::bplus_tree::lemma_keys_all_ge_set(ncl@, gseps@[i - 1]);
            assert(gseps@[cp@ - 1] <= key.id_nat());
        } else {
            assert(nkids[i] == gkids@[i]);
        }
    }
    // (weakening) separator-min proof block for nt REMOVED (tree_wf no longer carries it).
    // tree_wf(nt) at the caller's is_root: nt.seps == gseps (absorb leaves this
    // node's separators unchanged), so nt's occupancy == cur's — established when
    // is_root@==false (cur met it), dropped when is_root@==true.
    assert(nt->Inner_seps == gseps@);
    assert(crate::bplus_tree::tree_wf(cur@, h@, L::leaf_cap_spec(), L::key_cap_spec(), is_root@));
    assert(crate::bplus_tree::tree_wf(nt, h@, L::leaf_cap_spec(), L::key_cap_spec(), is_root@));

    // (3) leaf_links_to(a2, nt, succ): compose over the updated children.
    reconstruct_absorb_links::<K, L, S, TRACK>(arena1, arena2, cur, ncl, gid, gseps, gkids, cp, h, succ, child_succ);

    // (4) tree_disjoint(nt): disjoint_update with the GROWN child. The bound is
    // arena1.len(): every old forest id is < arena1.len() (binds(a1, cur) puts
    // them in range), and ncl's fresh ids are >= arena1.len(), so they collide
    // with no sibling.
    assert forall|i: int, j: int| 0 <= i < j < gkids@.len() implies
        (#[trigger] crate::bplus_tree::tree_ids(gkids@[i]))
            .disjoint(#[trigger] crate::bplus_tree::tree_ids(gkids@[j])) by {}
    assert(!crate::bplus_tree::forest_ids(gkids@).contains(gid@));  // tree_disjoint(cur)
    // every old forest id is < arena1.len() (binds(a1, cur), forest_ids ⊆ tree_ids).
    assert forall|id: nat| #[trigger] crate::bplus_tree::forest_ids(gkids@).contains(id)
        implies id < arena1@.len() by {
        assert(crate::bplus_tree::tree_ids(cur@).contains(id));  // {gid} ∪ forest_ids
        lemma_tree_id_in_range::<L>(a1, cur@, id);
    }
    crate::bplus_tree::lemma_forest_disjoint_update(gkids@, cp@, ncl@, arena1@.len());
    // tree_disjoint(nt): forest_disjoint(nkids) + pairwise (both from the lemma)
    // + gid ∉ forest_ids(nkids). The last: an nkids id is an old forest id (gid
    // is not one, by tree_disjoint(cur)) or a fresh id >= arena1.len() > gid.
    assert(gid@ < arena1@.len()) by {
        assert(crate::bplus_tree::tree_ids(cur@).contains(gid@));
        lemma_tree_id_in_range::<L>(a1, cur@, gid@);
    }
    assert(!crate::bplus_tree::forest_ids(nkids).contains(gid@)) by {
        if crate::bplus_tree::forest_ids(nkids).contains(gid@) {
            // gid in nkids ⟹ (old forest id) or (>= arena1.len()). Neither holds:
            // gid ∉ forest_ids(gkids) and gid < arena1.len().
            assert(crate::bplus_tree::forest_ids(gkids@).contains(gid@)
                || gid@ >= arena1@.len());
        }
    }
    assert(crate::bplus_tree::tree_disjoint(nt));

    // (5) footprint subset+freshness + first-leaf preservation.
    //   tree_ids(nt) == {gid} ∪ forest_ids(nkids); tree_ids(cur) == {gid} ∪
    //   forest_ids(gkids). The forest subset/freshness from disjoint_update
    //   lifts to the parent by adding gid (< arena1.len()) to both sides.
    assert(crate::bplus_tree::tree_ids(cur@).subset_of(crate::bplus_tree::tree_ids(nt))) by {
        assert(crate::bplus_tree::tree_ids(nt) =~= set![gid@].union(crate::bplus_tree::forest_ids(nkids)));
        assert(crate::bplus_tree::tree_ids(cur@) =~= set![gid@].union(crate::bplus_tree::forest_ids(gkids@)));
    }
    assert forall|id: nat| crate::bplus_tree::tree_ids(nt).contains(id)
        implies crate::bplus_tree::tree_ids(cur@).contains(id) || id >= arena1@.len() by {
        assert(crate::bplus_tree::tree_ids(nt) =~= set![gid@].union(crate::bplus_tree::forest_ids(nkids)));
        if id == gid@ {
            assert(crate::bplus_tree::tree_ids(cur@).contains(gid@));
        }
    }
    // first leaf preserved (child cp's first leaf is pinned; child 0 unchanged).
    assert forall|i: int| 0 <= i < gkids@.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(gkids@[i]).len() >= 1 by {
        crate::bplus_tree::lemma_forest_wf_at(gkids@, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), i);
        crate::bplus_tree::lemma_tree_leaf_ids_nonempty(gkids@[i], (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    }
    crate::bplus_tree::lemma_tree_leaf_ids_nonempty(ncl@, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    crate::bplus_tree::lemma_forest_leaf_ids_update_first(gkids@, cp@, ncl@);
    assert(crate::bplus_tree::tree_leaf_ids(nt)[0] == crate::bplus_tree::tree_leaf_ids(cur@)[0]);

    // (weakening) min-key-preservation proof block REMOVED.

    // (6) model: tree_keys(nt) == forest_keys(nkids); update splits to old ∪ {key}.
    crate::bplus_tree::lemma_forest_keys_update(gkids@, cp@, ncl@);
    crate::bplus_tree::lemma_forest_keys_split(gkids@, cp@ + 1);
    crate::bplus_tree::lemma_forest_keys_split(gkids@, cp@);
    reconstruct_absorb_model::<K, L, S, TRACK>(cur, ncl, gkids, cp, key);
}

/// Frame for the split branch: slots `< arena1.len()` outside `tree_ids(cur)`
/// are unchanged in `arena2`. The recursion (which produced ncl/ncr) touched
/// only inside `tree_ids(gkids[cp]) ⊆ tree_ids(cur)` plus fresh tail slots, and
/// the parent's `set(idx, …)` is at `gid ∈ tree_ids(cur)`. So every sibling slot
/// is preserved.
pub(crate) proof fn reconstruct_split_frame<K, L, S, const TRACK: bool>(
    arena1: Ghost<Seq<L::Node>>,
    arena2: Ghost<Seq<L::Node>>,
    cur: Ghost<Tree>,
    gkids: Ghost<Seq<Tree>>,
    cp: Ghost<int>,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        cur@ is Inner,
        cur@->Inner_kids == gkids@,
        0 <= cp@ < gkids@.len(),
        arena1@.len() <= arena2@.len(),
        // the recursion's frame + the parent's set(gid): slots < arena1.len()
        // outside tree_ids(gkids[cp]) AND != gid are unchanged. (gid excluded
        // because the parent-absorb does set(idx=gid) — same spec fix as
        // reconstruct_child_split_absorb's frame precondition.)
        forall|i: int| 0 <= i < arena1@.len()
            && !crate::bplus_tree::tree_ids(gkids@[cp@]).contains(i as nat)
            && i != cur@->Inner_id
            ==> #[trigger] arena2@[i] == arena1@[i],
    ensures
        forall|i: int| 0 <= i < arena1@.len()
            && !crate::bplus_tree::tree_ids(cur@).contains(i as nat)
            ==> #[trigger] arena2@[i] == arena1@[i],
{
    assert forall|i: int| 0 <= i < arena1@.len()
        && !crate::bplus_tree::tree_ids(cur@).contains(i as nat)
        implies #[trigger] arena2@[i] == arena1@[i] by {
        // i outside tree_ids(cur) ⟹ outside tree_ids(gkids[cp]) (subset) AND
        // i != gid (gid ∈ tree_ids(cur)).
        if crate::bplus_tree::tree_ids(gkids@[cp@]).contains(i as nat) {
            lemma_child_ids_subset_tree::<L>(cur@, cp@, i as nat);
        }
        // i != cur->Inner_id: gid is the root of cur, so in tree_ids(cur).
        assert(crate::bplus_tree::tree_ids(cur@).contains(cur@->Inner_id));
    }
}

/// `forest_binds_l` on a contiguous subrange `[lo, hi)` of a forest that binds.
pub(crate) proof fn lemma_forest_binds_subrange<L: NodeLayout>(a: Seq<L::Node>, kids: Seq<Tree>, lo: int, hi: int)
    requires forest_binds_l::<L>(a, kids), 0 <= lo <= hi <= kids.len(),
    ensures forest_binds_l::<L>(a, kids.subrange(lo, hi)),
    decreases hi - lo,
{
    let sub = kids.subrange(lo, hi);
    if lo == hi {
        assert(sub.len() == 0);
    } else {
        // sub[0] == kids[lo] binds; sub.drop_first() == kids[lo+1..hi].
        lemma_forest_binds_at::<L>(a, kids, lo);
        assert(sub[0] == kids[lo]);
        assert(sub.drop_first() =~= kids.subrange(lo + 1, hi));
        lemma_forest_binds_subrange::<L>(a, kids, lo + 1, hi);
    }
}

/// An id in `forest_ids(kids.subrange(lo, hi))` is in `forest_ids(kids)`.
pub(crate) proof fn lemma_forest_ids_subrange_in<L: NodeLayout>(kids: Seq<Tree>, lo: int, hi: int, id: nat)
    requires 0 <= lo <= hi <= kids.len(),
        crate::bplus_tree::forest_ids(kids.subrange(lo, hi)).contains(id),
    ensures crate::bplus_tree::forest_ids(kids).contains(id),
{
    let sub = kids.subrange(lo, hi);
    crate::bplus_tree::lemma_forest_id_in_some_child(sub, id);
    let m = choose|m: int| 0 <= m < sub.len() && #[trigger] crate::bplus_tree::tree_ids(sub[m]).contains(id);
    assert(sub[m] == kids[lo + m]);
    crate::bplus_tree::lemma_forest_id_in_forest(kids, lo + m, id);
}

/// An id in `left`/`right` (the siblings of child cp) is disjoint from child cp's
/// footprint and is not `gid`. `is_left` selects `left = kids[0..cp]` vs `right =
/// kids[cp+1..]`. From `tree_disjoint(cur)` (pairwise children + gid ∉ children).
pub(crate) proof fn lemma_left_right_disjoint_cp<L: NodeLayout>(cur: Tree, cp: int, id: nat, is_left: bool)
    requires
        cur is Inner,
        crate::bplus_tree::tree_disjoint(cur),
        0 <= cp < cur->Inner_kids.len(),
        ({
            let kids = cur->Inner_kids;
            let sub = if is_left { kids.subrange(0, cp) } else { kids.subrange(cp + 1, kids.len() as int) };
            crate::bplus_tree::forest_ids(sub).contains(id)
        }),
    ensures
        !crate::bplus_tree::tree_ids(cur->Inner_kids[cp]).contains(id),
        id != cur->Inner_id,
{
    let kids = cur->Inner_kids;
    let sub = if is_left { kids.subrange(0, cp) } else { kids.subrange(cp + 1, kids.len() as int) };
    crate::bplus_tree::lemma_forest_id_in_some_child(sub, id);
    let m = choose|m: int| 0 <= m < sub.len() && #[trigger] crate::bplus_tree::tree_ids(sub[m]).contains(id);
    let orig = if is_left { m } else { cp + 1 + m };
    assert(sub[m] == kids[orig]);
    // pairwise child disjointness: tree_ids(kids[orig]) ⊥ tree_ids(kids[cp]) (orig != cp).
    if orig < cp {
        assert(crate::bplus_tree::tree_ids(kids[orig]).disjoint(crate::bplus_tree::tree_ids(kids[cp])));
    } else {
        assert(crate::bplus_tree::tree_ids(kids[cp]).disjoint(crate::bplus_tree::tree_ids(kids[orig])));
    }
    // gid ∉ any child's footprint (tree_disjoint clause: !forest_ids(kids).contains(gid)).
    crate::bplus_tree::lemma_forest_id_in_forest(kids, orig, id);
    assert(!crate::bplus_tree::forest_ids(kids).contains(cur->Inner_id));
}

/// Reconstruct `subtree_wf` for the child-split absorb branch (the child split
/// and this parent had room). Builds `nt = Inner{gid, gseps.insert(cp, sep),
/// gkids.update(cp, ncl).insert(cp+1, ncr)}` and proves it `subtree_wf` at
/// `(h, succ)` with model `∪ {key}`, footprint preserved-plus-fresh, leaf-ids
/// preserved-plus-spliced. The new children are `left ++ [ncl, ncr] ++ right`;
/// each wf clause assembles via the forest concat lemmas.
///
/// The spliced children `gkids.update(cp, ncl).insert(cp+1, ncr)` all bind in
/// the post-split arena `a2`. Reusable by BOTH split reconstructions (the
/// child-split-absorb parent and the parent-split halves). `ncl`/`ncr` bind in
/// `a2` directly (the recursion's results); the untouched siblings bind in `a1`
/// and frame to `a2` (their footprints are disjoint from `gkids[cp]` and from
/// `gid`, all slots unchanged). Then `binds` distributes over the concatenation
/// `left ++ [ncl, ncr] ++ right`.
pub(crate) proof fn lemma_splice_children_bind<K, L, S, const TRACK: bool>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    cur: Tree,
    gid: nat,
    gseps: Seq<nat>,
    gkids: Seq<Tree>,
    cp: int,
    ncl: Tree,
    ncr: Tree,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        cur == (Tree::Inner { id: gid, seps: gseps, kids: gkids }),
        0 <= cp < gkids.len(),
        a1.len() <= a2.len(),
        binds::<L>(a1, cur),
        crate::bplus_tree::tree_disjoint(cur),
        binds::<L>(a2, ncl),
        binds::<L>(a2, ncr),
        // siblings (outside gkids[cp]) and the parent slot gid are unchanged in a2.
        (forall|i: int| 0 <= i < a1.len()
            && !crate::bplus_tree::tree_ids(gkids[cp]).contains(i as nat)
            && i != gid
            ==> #[trigger] a2[i] == a1[i]),
    ensures
        forest_binds_l::<L>(a2, gkids.update(cp, ncl).insert(cp + 1, ncr)),
{
    let kids = gkids;
    let nkids = kids.update(cp, ncl).insert(cp + 1, ncr);
    let left = kids.subrange(0, cp);
    let right = kids.subrange(cp + 1, kids.len() as int);
    assert(forest_binds_l::<L>(a1, kids));  // binds(a1, cur) Inner arm
    lemma_forest_binds_subrange::<L>(a1, kids, 0, cp);
    lemma_forest_binds_subrange::<L>(a1, kids, cp + 1, kids.len() as int);
    assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(left).contains(id)
        implies a1[id as int] == a2[id as int] by {
        lemma_forest_ids_subrange_in::<L>(kids, 0, cp, id);
        assert(crate::bplus_tree::tree_ids(cur).contains(id));
        lemma_tree_id_in_range::<L>(a1, cur, id);
        lemma_left_right_disjoint_cp::<L>(cur, cp, id, true);
        assert(!crate::bplus_tree::tree_ids(gkids[cp]).contains(id));
        assert(id != gid);
    }
    assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(right).contains(id)
        implies a1[id as int] == a2[id as int] by {
        lemma_forest_ids_subrange_in::<L>(kids, cp + 1, kids.len() as int, id);
        assert(crate::bplus_tree::tree_ids(cur).contains(id));
        lemma_tree_id_in_range::<L>(a1, cur, id);
        lemma_left_right_disjoint_cp::<L>(cur, cp, id, false);
        assert(!crate::bplus_tree::tree_ids(gkids[cp]).contains(id));
        assert(id != gid);
    }
    lemma_forest_binds_frame_tail::<L>(a1, a2, left);
    lemma_forest_binds_frame_tail::<L>(a1, a2, right);
    lemma_forest_binds_pair::<L>(a2, ncl, ncr);
    lemma_forest_binds_concat::<L>(a2, left, seq![ncl, ncr]);
    assert((left + seq![ncl, ncr]) + right =~= nkids);
    lemma_forest_binds_concat::<L>(a2, left + seq![ncl, ncr], right);
}

/// Assembled from the structural ghost lemma `lemma_child_split_absorb_tree_wf`
/// (tree_wf + model) plus the arena layers: `binds` over the spliced children
/// (`lemma_forest_binds_concat` of the three pieces), the leaf-link chain, and
/// `tree_disjoint`. No assumes.
pub(crate) proof fn reconstruct_child_split_absorb<K, L, S, const TRACK: bool>(
    arena1: Ghost<Seq<L::Node>>,
    arena2: Ghost<Seq<L::Node>>,
    cur: Ghost<Tree>,
    ncl: Ghost<Tree>,
    ncr: Ghost<Tree>,
    gid: Ghost<nat>,
    gseps: Ghost<Seq<nat>>,
    gkids: Ghost<Seq<Tree>>,
    cp: Ghost<int>,
    h: Ghost<nat>,
    succ: Ghost<nat>,
    child_succ: Ghost<nat>,
    key: K,
    sep: L::Word,
    rid: L::ArenaIdx,
    pnode: Ghost<L::Node>,
    is_root: Ghost<bool>,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        cur@ == (Tree::Inner { id: gid@, seps: gseps@, kids: gkids@ }),
        h@ == crate::bplus_tree::tree_height(cur@),
        0 <= cp@ < gkids@.len(),
        // parent had room before the splice (the absorb branch guard `n < kc`).
        gseps@.len() < L::key_cap_spec(),
        // `cur` wf at the caller's root-ness; the rebuilt `nt` GAINS a separator
        // (gseps.len()+1), so its occupancy still meets the non-root bound when
        // is_root@==false, and is unconstrained when is_root@==true.
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena1@, cur@, h@, succ@, is_root@),
        // child split products (the recursion's Some result):
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena2@, ncl@, (h@ - 1) as nat,
            crate::bplus_tree::tree_leaf_ids(ncr@)[0], false),
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena2@, ncr@, (h@ - 1) as nat, child_succ@, false),
        crate::bplus_tree::tree_root_id(ncl@) == crate::bplus_tree::tree_root_id(gkids@[cp@]),
        crate::bplus_tree::tree_root_id(ncr@) == rid.as_nat(),
        crate::bplus_tree::tree_keys(ncl@).len() >= 1,
        crate::bplus_tree::tree_keys(ncr@).len() >= 1,
        // (second weakening) both `sep == tree_keys(ncr)[0]` and the weaker
        // `sep ∈ (ncl+ncr)` membership are REMOVED; only the ordering below is used.
        // median ordering of the two halves around `sep` (from the split).
        crate::bplus_tree::keys_all_lt(ncl@, sep.as_nat()),
        crate::bplus_tree::keys_all_ge(ncr@, sep.as_nat()),
        (crate::bplus_tree::tree_keys(ncl@) + crate::bplus_tree::tree_keys(ncr@)).to_set()
            == crate::bplus_tree::tree_keys(gkids@[cp@]).to_set().insert(key.id_nat()),
        child_succ@ == (if cp@ + 1 < gkids@.len() {
            crate::bplus_tree::tree_leaf_ids(gkids@[cp@ + 1])[0]
        } else { succ@ }),
        // footprint: ncl/ncr ids are old (in cur) or fresh (>= arena1.len()).
        (forall|id: nat| #[trigger] crate::bplus_tree::tree_ids(ncl@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        (forall|id: nat| #[trigger] crate::bplus_tree::tree_ids(ncr@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        // old child's ids retained across the two halves (split distributes them).
        (forall|id: nat| #![trigger crate::bplus_tree::tree_ids(ncl@).contains(id)] #![trigger crate::bplus_tree::tree_ids(ncr@).contains(id)] crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
            ==> crate::bplus_tree::tree_ids(ncl@).contains(id) || crate::bplus_tree::tree_ids(ncr@).contains(id)),
        // the two halves have disjoint footprints (split puts them apart).
        crate::bplus_tree::tree_ids(ncl@).disjoint(crate::bplus_tree::tree_ids(ncr@)),
        // first-leaf preservation: ncl (the left half) keeps the old child's
        // leftmost leaf (the split splices the new leaf to the RIGHT).
        crate::bplus_tree::tree_leaf_ids(ncl@).len() >= 1,
        crate::bplus_tree::tree_leaf_ids(ncl@)[0] == crate::bplus_tree::tree_leaf_ids(gkids@[cp@])[0],
        // arena layout: pnode at gid (the internal_insert_at result), children read back.
        arena1@.len() <= arena2@.len(),
        arena2@[gid@ as int] == pnode@,
        !L::is_leaf_spec(pnode@),
        L::count_spec(pnode@) == gseps@.len() + 1,
        L::keys_view(pnode@) == L::keys_view(arena1@[gid@ as int]).insert(cp@, sep),
        (forall|j: int| 0 <= j <= cp@ ==> #[trigger] L::child_view(pnode@, j) == L::child_view(arena1@[gid@ as int], j)),
        L::child_view(pnode@, cp@ + 1) == rid.as_nat(),
        (forall|j: int| cp@ + 1 < j <= gseps@.len() + 1 ==>
            L::child_view(pnode@, j) == L::child_view(arena1@[gid@ as int], (j - 1))),
        // recursion frame + the parent's set(gid): slots < arena1.len() outside
        // BOTH the recursed child's footprint AND the parent slot `gid` are
        // unchanged. (Was wrongly stated as outside `gkids[cp]` only, omitting the
        // `set(idx=gid)` the parent-absorb does — a spec bug surfaced by the
        // working code: arena2[gid] != arena1[gid].)
        (forall|i: int| 0 <= i < arena1@.len()
            && !crate::bplus_tree::tree_ids(gkids@[cp@]).contains(i as nat)
            && i != gid@
            ==> arena2@[i] == arena1@[i]),
        // descent routing (key within the surrounding separators).
        (forall|j: int| 0 <= j < cp@ ==> gseps@[j] <= key.id_nat()),
        (forall|j: int| cp@ <= j < gseps@.len() ==> key.id_nat() < gseps@[j]),
    ensures
        ({
            let nseps = gseps@.insert(cp@, sep.as_nat());
            let nkids = gkids@.update(cp@, ncl@).insert(cp@ + 1, ncr@);
            let nt = Tree::Inner { id: gid@, seps: nseps, kids: nkids };
            &&& BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena2@, nt, h@, succ@, is_root@)
            &&& crate::bplus_tree::tree_root_id(nt) == gid@
            &&& crate::bplus_tree::tree_keys(nt).to_set()
                    == crate::bplus_tree::tree_keys(cur@).to_set().insert(key.id_nat())
            // (F0) footprint subset+freshness + first-leaf preservation, same as
            // the pure-absorb path: a fresh node `rid` (and any deeper fresh
            // slots) were appended (>= arena1.len()), and the leftmost leaf is
            // pinned (the split spliced `ncr` to the RIGHT of `ncl`).
            &&& crate::bplus_tree::tree_ids(cur@).subset_of(crate::bplus_tree::tree_ids(nt))
            &&& (forall|id: nat| crate::bplus_tree::tree_ids(nt).contains(id)
                    ==> crate::bplus_tree::tree_ids(cur@).contains(id) || id >= arena1@.len())
            &&& crate::bplus_tree::tree_leaf_ids(nt)[0] == crate::bplus_tree::tree_leaf_ids(cur@)[0]
                        // (weakening) min-key-preservation ensures clause REMOVED.
        }),
{
    let a1 = arena1@; let a2 = arena2@;
    let kids = gkids@;
    let nseps = gseps@.insert(cp@, sep.as_nat());
    let nkids = kids.update(cp@, ncl@).insert(cp@ + 1, ncr@);
    let nt = Tree::Inner { id: gid@, seps: nseps, kids: nkids };
    let cur_t = cur@;
    let left = kids.subrange(0, cp@);
    let right = kids.subrange(cp@ + 1, kids.len() as int);
    L::lemma_arena_capacity();
    // cur is wf at is_root@; relax to root-form for the structural facts the
    // splice reads (count, sortedness, cross-node ordering — never occupancy).
    if !is_root@ {
        crate::bplus_tree::lemma_tree_wf_relax_root(cur_t, h@, L::leaf_cap_spec(), L::key_cap_spec());
    }
    assert(crate::bplus_tree::tree_wf(cur_t, h@, L::leaf_cap_spec(), L::key_cap_spec(), true));
    assert(kids.len() == gseps@.len() + 1);

    // splice == concatenation of the three pieces.
    assert(nkids =~= left + seq![ncl@, ncr@] + right);

    // ---- (1) tree_wf(nt) + model: the structural ghost lemma. ----
    // parent had room: `gseps.len() < key_cap` (the absorb branch guard `n < kc`).
    crate::bplus_tree::lemma_child_split_absorb_tree_wf(
        gid@, gseps@, kids, cp@, ncl@, ncr@, sep.as_nat(), key.id_nat(),
        h@, L::leaf_cap_spec(), L::key_cap_spec(), is_root@);
    assert(crate::bplus_tree::tree_wf(nt, h@, L::leaf_cap_spec(), L::key_cap_spec(), is_root@));
    assert(crate::bplus_tree::tree_keys(nt).to_set()
        == crate::bplus_tree::tree_keys(cur_t).to_set().insert(key.id_nat()));

    // ---- (2) binds(a2, nt). ----
    // children bind in a2 (reusable splice-binds lemma): ncl/ncr from the
    // recursion, siblings framed from a1.
    assert(binds::<L>(a2, ncl@));
    assert(binds::<L>(a2, ncr@));
    lemma_splice_children_bind::<K, L, S, TRACK>(a1, a2, cur_t, gid@, gseps@, kids, cp@, ncl@, ncr@);
    assert(forest_binds_l::<L>(a2, nkids));
    // binds(a2, nt) Inner arm: the parent node `pnode` at gid, its keys_view and
    // child_view match nseps / nkids' root ids.
    // preconditions for the binds-node lemma: parent's keys_view length, and the
    // a1 node's keys/child views (from binds(a1, cur) Inner arm).
    assert(binds::<L>(a1, cur_t));
    assert(L::keys_view(a1[gid@ as int]).len() == gseps@.len()) by {
        L::lemma_keys_view_len(a1[gid@ as int]);
        assert(L::count_spec(a1[gid@ as int]) == gseps@.len());  // binds(a1,cur) Inner arm
    }
    lemma_child_split_binds_node::<K, L, S, TRACK>(
        a1, a2, gid@, gseps@, kids, cp@, ncl@, ncr@, sep, rid, pnode@);
    assert(binds::<L>(a2, nt));

    // ---- (3) leaf_links_to(a2, nt, succ). ----
    // ncr non-empty (wf at h-1, non-root) — the link splice reads its first leaf.
    crate::bplus_tree::lemma_tree_leaf_ids_nonempty(ncr@, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    // bridge the frame to the links lemma's `forest_ids(kids)` agreement form: a
    // child-footprint id outside gkids[cp] is in tree_ids(cur), != gid (gid ∉ any
    // child), and < arena1.len(), so the contract's frame clause applies.
    assert forall|id: nat| #![trigger crate::bplus_tree::forest_ids(gkids@).contains(id)] #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(gkids@).contains(id)
        && !crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
        implies a1[id as int] == a2[id as int] by {
        assert(crate::bplus_tree::tree_ids(cur@).contains(id));  // forest_ids ⊆ tree_ids(cur)
        lemma_tree_id_in_range::<L>(a1, cur@, id);  // id < arena1.len()
        // id != gid: gid ∉ forest_ids(gkids) (tree_disjoint(cur)).
        assert(!crate::bplus_tree::forest_ids(gkids@).contains(gid@));
    }
    reconstruct_child_split_links::<K, L, S, TRACK>(
        arena1, arena2, cur, ncl, ncr, gid, gseps, gkids, cp, h, succ, child_succ,
        Ghost(sep.as_nat()), Ghost(rid.as_nat()));

    // ---- (4) tree_disjoint(nt) + (5) footprint subset+freshness + first-leaf. ----
    // ncl/ncr tree_disjoint come from their subtree_wf; ncl ⊇ child cp + ncl⊥ncr
    // + first-leaf are preconditions; the wrapper supplies bound = arena1.len().
    assert(crate::bplus_tree::tree_disjoint(ncl@));  // subtree_wf(ncl)
    assert(crate::bplus_tree::tree_disjoint(ncr@));  // subtree_wf(ncr)
    crate::bplus_tree::lemma_tree_leaf_ids_nonempty(ncl@, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    reconstruct_child_split_disjoint::<K, L, S, TRACK>(
        arena1, cur, ncl, ncr, gid, gseps, gkids, cp, h, succ, Ghost(sep.as_nat()));
    assert(crate::bplus_tree::tree_disjoint(nt));
    assert(crate::bplus_tree::tree_ids(cur@).subset_of(crate::bplus_tree::tree_ids(nt)));
    assert(crate::bplus_tree::tree_leaf_ids(nt)[0] == crate::bplus_tree::tree_leaf_ids(cur@)[0]);
    // (weakening) min-key-preservation proof block REMOVED.
}

/// `binds(a2, nt)` Inner arm for the child-split splice: the parent node `pnode`
/// at `gid` has `keys_view == nseps` and `child_view(i) == root id of nkids[i]`.
/// The `internal_insert_at` postconditions on `pnode` (keys inserted at cp, child
/// cp+1 == rid, others shifted) line up exactly with the spliced `nseps`/`nkids`.
pub(crate) proof fn lemma_child_split_binds_node<K, L, S, const TRACK: bool>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    gid: nat,
    gseps: Seq<nat>,
    gkids: Seq<Tree>,
    cp: int,
    ncl: Tree,
    ncr: Tree,
    sep: L::Word,
    rid: L::ArenaIdx,
    pnode: L::Node,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        0 <= cp < gkids.len(),
        gkids.len() == gseps.len() + 1,
        0 <= cp <= gseps.len(),
        L::keys_view(a1[gid as int]).len() == gseps.len(),
        a2[gid as int] == pnode,
        !L::is_leaf_spec(pnode),
        L::count_spec(pnode) == gseps.len() + 1,
        L::keys_view(pnode) == L::keys_view(a1[gid as int]).insert(cp, sep),
        // a1's parent node bound gseps + gkids' root ids (binds(a1, cur) Inner arm).
        (forall|i: int| 0 <= i < gseps.len() ==> (#[trigger] L::keys_view(a1[gid as int])[i]).as_nat() == gseps[i]),
        (forall|i: int| 0 <= i < gkids.len() ==> L::child_view(a1[gid as int], i) == crate::bplus_tree::tree_root_id(#[trigger] gkids[i])),
        // pnode's child slots: [0..cp] same, cp+1 == rid, (cp+1, ..] shifted by one.
        (forall|j: int| 0 <= j <= cp ==> #[trigger] L::child_view(pnode, j) == L::child_view(a1[gid as int], j)),
        L::child_view(pnode, cp + 1) == rid.as_nat(),
        (forall|j: int| cp + 1 < j <= gseps.len() + 1 ==> L::child_view(pnode, j) == L::child_view(a1[gid as int], (j - 1))),
        crate::bplus_tree::tree_root_id(ncl) == crate::bplus_tree::tree_root_id(gkids[cp]),
        crate::bplus_tree::tree_root_id(ncr) == rid.as_nat(),
        // (weakening) sep == tree_keys(ncr)[0] REMOVED (was unused in binds_node).
    ensures
        ({
            let nseps = gseps.insert(cp, sep.as_nat());
            let nkids = gkids.update(cp, ncl).insert(cp + 1, ncr);
            // keys_view(pnode) projects to nseps, and child_view to nkids' roots.
            &&& (forall|i: int| 0 <= i < nseps.len() ==> (#[trigger] L::keys_view(pnode)[i]).as_nat() == nseps[i])
            &&& (forall|i: int| 0 <= i < nkids.len() ==> L::child_view(pnode, i) == crate::bplus_tree::tree_root_id(#[trigger] nkids[i]))
            &&& L::count_spec(pnode) == nseps.len()
        }),
{
    let nseps = gseps.insert(cp, sep.as_nat());
    let nkids = gkids.update(cp, ncl).insert(cp + 1, ncr);
    assert(nseps.len() == gseps.len() + 1);
    assert(nkids.len() == gkids.len() + 1);
    // keys: keys_view(pnode) == keys_view(a1[gid]).insert(cp, sep) projects to nseps.
    assert forall|i: int| 0 <= i < nseps.len() implies
        (#[trigger] L::keys_view(pnode)[i]).as_nat() == nseps[i] by {
        if i < cp {
            assert(L::keys_view(pnode)[i] == L::keys_view(a1[gid as int])[i]);
            assert(nseps[i] == gseps[i]);
        } else if i == cp {
            assert(L::keys_view(pnode)[i] == sep);
            assert(nseps[i] == sep.as_nat());
        } else {
            assert(L::keys_view(pnode)[i] == L::keys_view(a1[gid as int])[i - 1]);
            assert(nseps[i] == gseps[i - 1]);
        }
    }
    // children: child_view(pnode) maps to nkids' root ids per the splice index map.
    assert forall|i: int| 0 <= i < nkids.len() implies
        L::child_view(pnode, i) == crate::bplus_tree::tree_root_id(#[trigger] nkids[i]) by {
        if i < cp {
            assert(nkids[i] == gkids[i]);
            assert(L::child_view(pnode, i) == L::child_view(a1[gid as int], i));
        } else if i == cp {
            assert(nkids[i] == ncl);
            assert(L::child_view(pnode, i) == L::child_view(a1[gid as int], i));
            assert(crate::bplus_tree::tree_root_id(ncl) == crate::bplus_tree::tree_root_id(gkids[cp]));
        } else if i == cp + 1 {
            assert(nkids[i] == ncr);
            assert(L::child_view(pnode, i) == rid.as_nat());
        } else {
            assert(nkids[i] == gkids[i - 1]);
            assert(L::child_view(pnode, i) == L::child_view(a1[gid as int], i - 1));
        }
    }
}

/// The combined node's child slots (`isplit_cchild`, what `internal_split_at`
/// distributes to the two halves) equal the spliced children's root ids: for all
/// `0 <= j < ckids.len()`, `isplit_cchild(pnode, cp, rid, j) == tree_root_id(
/// ckids[j])` where `ckids = gkids.update(cp, ncl).insert(cp+1, ncr)`. `pnode` is
/// the ORIGINAL parent node (binds `gkids`' root ids); `ncl`/`ncr` carry the new
/// children's root ids (`gkids[cp]`'s and `rid`). This is the bridge that lets
/// the parent-split halves' `binds` reduce to the already-bound `ckids`.
pub(crate) proof fn lemma_isplit_cchild_is_ckid<K, L, S, const TRACK: bool>(
    a1: Seq<L::Node>,
    gid: nat,
    gseps: Seq<nat>,
    gkids: Seq<Tree>,
    cp: int,
    ncl: Tree,
    ncr: Tree,
    rid: L::ArenaIdx,
    pnode: L::Node,
    j: int,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        0 <= cp < gkids.len(),
        0 <= j < gkids.len() + 1,  // ckids has one more child
        pnode == a1[gid as int],
        // pnode binds gkids' root ids (binds(a1, cur) Inner arm).
        (forall|i: int| 0 <= i < gkids.len() ==> L::child_view(pnode, i) == crate::bplus_tree::tree_root_id(#[trigger] gkids[i])),
        crate::bplus_tree::tree_root_id(ncl) == crate::bplus_tree::tree_root_id(gkids[cp]),
        crate::bplus_tree::tree_root_id(ncr) == rid.as_nat(),
    ensures
        ({
            let ckids = gkids.update(cp, ncl).insert(cp + 1, ncr);
            L::isplit_cchild(pnode, cp, rid, j) == crate::bplus_tree::tree_root_id(ckids[j])
        }),
{
    let ckids = gkids.update(cp, ncl).insert(cp + 1, ncr);
    // ckids index map (the splice).
    assert(ckids[j] == (
        if j < cp { gkids[j] } else if j == cp { ncl } else if j == cp + 1 { ncr } else { gkids[j - 1] }
    ));
    // expose isplit_cchild's cases generically.
    L::lemma_isplit_cchild(pnode, cp, rid, j);
    // isplit_cchild: j<=cp -> child_view(pnode,j); j==cp+1 -> rid; else child_view(pnode,j-1).
    if j < cp {
        assert(L::child_view(pnode, j) == crate::bplus_tree::tree_root_id(gkids[j]));
    } else if j == cp {
        assert(L::child_view(pnode, cp) == crate::bplus_tree::tree_root_id(gkids[cp]));
        assert(crate::bplus_tree::tree_root_id(ncl) == crate::bplus_tree::tree_root_id(gkids[cp]));
    } else if j == cp + 1 {
    } else {
        assert(L::child_view(pnode, j - 1) == crate::bplus_tree::tree_root_id(gkids[j - 1]));
    }
}

/// `binds(a2, half)` for one half of a parent split, where `half = Inner{hid,
/// cseps[off..off+slen], ckids[off..off+slen+1]}` and the half's arena node `pn`
/// (at `hid`) is `internal_split_at`'s output: `keys_view(pn) == cseps[off..]`
/// and `child_view(pn, j) == isplit_cchild(pnode, cp, rid, off+j)`. Reduces to:
/// the node's keys/children project (via the cseps subrange + the isplit_cchild
/// bridge), and the half's children bind (subrange of the bound `ckids`). `sep`
/// is the actual stored separator (`internal_split_at`'s `new_sep`); `binds`
/// reads only that the node's `keys_view` projects to it, so the value is
/// otherwise unconstrained (post-weakening it need not equal `ncr_first(ncr)`).
pub(crate) proof fn lemma_parent_split_half_binds<K, L, S, const TRACK: bool>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    gid: nat,
    gseps: Seq<nat>,
    gkids: Seq<Tree>,
    cp: int,
    ncl: Tree,
    ncr: Tree,
    sep: nat,
    rid: L::ArenaIdx,
    pnode: L::Node,
    hid: nat,
    pn: L::Node,
    off: int,
    slen: int,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        0 <= cp < gkids.len(),
        gkids.len() == gseps.len() + 1,
        cp <= gseps.len(),
        0 <= off,
        off + slen + 1 <= gkids.len() + 1,  // ckids.len() == gkids.len()+1 (update keeps len, insert +1)
        pnode == a1[gid as int],
        hid < a2.len(),
        a2[hid as int] == pn,
        !L::is_leaf_spec(pn),
        // the half node's views (internal_split_at output, shifted by off).
        L::count_spec(pn) == slen,
        (forall|i: int| 0 <= i < slen ==>
            (#[trigger] L::keys_view(pn)[i]).as_nat() == gseps.insert(cp, sep)[off + i]),
        (forall|j: int| 0 <= j < slen + 1 ==>
            L::child_view(pn, j) == L::isplit_cchild(pnode, cp, rid, off + j)),
        // pnode binds gkids' roots; ncl/ncr roots; ckids bind in a2.
        (forall|i: int| 0 <= i < gkids.len() ==> L::child_view(pnode, i) == crate::bplus_tree::tree_root_id(#[trigger] gkids[i])),
        crate::bplus_tree::tree_root_id(ncl) == crate::bplus_tree::tree_root_id(gkids[cp]),
        crate::bplus_tree::tree_root_id(ncr) == rid.as_nat(),
        forest_binds_l::<L>(a2, gkids.update(cp, ncl).insert(cp + 1, ncr)),
    ensures
        ({
            let cseps = gseps.insert(cp, sep);
            let ckids = gkids.update(cp, ncl).insert(cp + 1, ncr);
            binds::<L>(a2, Tree::Inner {
                id: hid,
                seps: cseps.subrange(off, off + slen),
                kids: ckids.subrange(off, off + slen + 1),
            })
        }),
{
    let cseps = gseps.insert(cp, sep);
    let ckids = gkids.update(cp, ncl).insert(cp + 1, ncr);
    // length bookkeeping: update keeps len, insert(cp+1,..) adds 1 (cp+1 <= len).
    assert(cseps.len() == gseps.len() + 1);   // cp <= gseps.len()
    assert(gkids.update(cp, ncl).len() == gkids.len());
    assert(ckids.len() == gkids.len() + 1);   // insert at cp+1 <= gkids.len()
    assert(off + slen <= cseps.len());        // off+slen+1 <= ckids.len() == cseps.len()+1
    assert(off + slen + 1 <= ckids.len());
    let hseps = cseps.subrange(off, off + slen);
    let hkids = ckids.subrange(off, off + slen + 1);
    let half = Tree::Inner { id: hid, seps: hseps, kids: hkids };
    assert(hseps.len() == slen);
    assert(hkids.len() == slen + 1);
    // keys: keys_view(pn)[i] == cseps[off+i] == hseps[i].
    assert forall|i: int| 0 <= i < hseps.len() implies
        (#[trigger] L::keys_view(pn)[i]).as_nat() == hseps[i] by {
        assert(hseps[i] == cseps[off + i]);  // subrange index
    }
    // children: child_view(pn, j) == isplit_cchild(pnode, cp, rid, off+j)
    //   == tree_root_id(ckids[off+j]) == tree_root_id(hkids[j]).
    assert forall|j: int| 0 <= j < hkids.len() implies
        L::child_view(pn, j) == crate::bplus_tree::tree_root_id(#[trigger] hkids[j]) by {
        lemma_isplit_cchild_is_ckid::<K, L, S, TRACK>(a1, gid, gseps, gkids, cp, ncl, ncr, rid, pnode, off + j);
        assert(hkids[j] == ckids[off + j]);
    }
    // half's children bind: subrange of forest_binds_l(a2, ckids).
    lemma_forest_binds_subrange::<L>(a2, ckids, off, off + slen + 1);
    assert(forest_binds_l::<L>(a2, hkids));
}

/// Spec helper: the first (least) key of `ncr` (the promoted separator). Named so
/// the half-binds lemma can refer to the combined seps without threading `sep`.
pub open(crate) spec fn ncr_first<L: NodeLayout>(ncr: Tree) -> nat {
    crate::bplus_tree::tree_keys(ncr)[0]
}

/// `tree_disjoint(nt)` + footprint subset/freshness + first-leaf preservation for
/// the child-split splice: a thin arena-side wrapper that supplies the freshness
/// `bound = arena1.len()` (every old id is in range, every new id is a fresh tail
/// slot) to the pure-ghost `lemma_child_split_absorb_ids`.
pub(crate) proof fn reconstruct_child_split_disjoint<K, L, S, const TRACK: bool>(
    arena1: Ghost<Seq<L::Node>>,
    cur: Ghost<Tree>,
    ncl: Ghost<Tree>,
    ncr: Ghost<Tree>,
    gid: Ghost<nat>,
    gseps: Ghost<Seq<nat>>,
    gkids: Ghost<Seq<Tree>>,
    cp: Ghost<int>,
    h: Ghost<nat>,
    succ: Ghost<nat>,
    sep: Ghost<nat>,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        cur@ == (Tree::Inner { id: gid@, seps: gseps@, kids: gkids@ }),
        h@ == crate::bplus_tree::tree_height(cur@),
        0 <= cp@ < gkids@.len(),
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena1@, cur@, h@, succ@, true),
        crate::bplus_tree::tree_disjoint(ncl@),
        crate::bplus_tree::tree_disjoint(ncr@),
        crate::bplus_tree::tree_ids(ncl@).disjoint(crate::bplus_tree::tree_ids(ncr@)),
        // old child's ids retained across the two halves (split distributes them).
        (forall|id: nat| #![trigger crate::bplus_tree::tree_ids(ncl@).contains(id)] #![trigger crate::bplus_tree::tree_ids(ncr@).contains(id)] crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
            ==> crate::bplus_tree::tree_ids(ncl@).contains(id) || crate::bplus_tree::tree_ids(ncr@).contains(id)),
        (forall|id: nat| #[trigger] crate::bplus_tree::tree_ids(ncl@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        (forall|id: nat| #[trigger] crate::bplus_tree::tree_ids(ncr@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        crate::bplus_tree::tree_leaf_ids(ncl@).len() >= 1,
        crate::bplus_tree::tree_leaf_ids(ncl@)[0] == crate::bplus_tree::tree_leaf_ids(gkids@[cp@])[0],
    ensures
        ({
            let nkids = gkids@.update(cp@, ncl@).insert(cp@ + 1, ncr@);
            let nt = Tree::Inner { id: gid@, seps: gseps@.insert(cp@, sep@), kids: nkids };
            &&& crate::bplus_tree::tree_disjoint(nt)
            &&& crate::bplus_tree::tree_ids(cur@).subset_of(crate::bplus_tree::tree_ids(nt))
            &&& (forall|id: nat| crate::bplus_tree::tree_ids(nt).contains(id)
                    ==> crate::bplus_tree::tree_ids(cur@).contains(id) || id >= arena1@.len())
            &&& crate::bplus_tree::tree_leaf_ids(nt).len() >= 1
            &&& crate::bplus_tree::tree_leaf_ids(nt)[0] == crate::bplus_tree::tree_leaf_ids(cur@)[0]
        }),
{
    let a1 = arena1@;
    // every old id < arena1.len() (binds(a1, cur) in-range).
    assert forall|id: nat| #[trigger] crate::bplus_tree::tree_ids(cur@).contains(id)
        implies id < a1.len() by {
        lemma_tree_id_in_range::<L>(a1, cur@, id);
    }
    // each child non-empty (cur's tree_wf at h-1).
    assert forall|i: int| 0 <= i < gkids@.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(gkids@[i]).len() >= 1 by {
        crate::bplus_tree::lemma_forest_wf_at(gkids@, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), i);
        crate::bplus_tree::lemma_tree_leaf_ids_nonempty(gkids@[i], (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    }
    crate::bplus_tree::lemma_child_split_absorb_ids(
        gid@, gseps@, gkids@, cp@, ncl@, ncr@, sep@, a1.len());
}

/// Leaf-link chain for the child-split splice: `leaf_links_to(a2, nt, succ)`. The
/// chain decomposes over the spliced children; child cp's old chain is replaced
/// by `ncl -> ncr -> (cp+1's first leaf | succ)`, the siblings are framed.
///
/// Decompose `cur`'s chain to `forest_links_to(a1, gkids, succ)`, splice in the
/// two halves (`lemma_forest_links_splice`), then compose back to a whole-subtree
/// chain (`lemma_forest_links_compose`).
pub(crate) proof fn reconstruct_child_split_links<K, L, S, const TRACK: bool>(
    arena1: Ghost<Seq<L::Node>>,
    arena2: Ghost<Seq<L::Node>>,
    cur: Ghost<Tree>,
    ncl: Ghost<Tree>,
    ncr: Ghost<Tree>,
    gid: Ghost<nat>,
    gseps: Ghost<Seq<nat>>,
    gkids: Ghost<Seq<Tree>>,
    cp: Ghost<int>,
    h: Ghost<nat>,
    succ: Ghost<nat>,
    child_succ: Ghost<nat>,
    sep: Ghost<nat>,
    rid: Ghost<nat>,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        cur@ == (Tree::Inner { id: gid@, seps: gseps@, kids: gkids@ }),
        h@ == crate::bplus_tree::tree_height(cur@),
        0 <= cp@ < gkids@.len(),
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena1@, cur@, h@, succ@, true),
        // the two halves' chains in a2, and ncr non-empty.
        crate::bplus_tree::tree_leaf_ids(ncr@).len() >= 1,
        leaf_links_to::<L>(arena2@, ncl@, crate::bplus_tree::tree_leaf_ids(ncr@)[0]),
        leaf_links_to::<L>(arena2@, ncr@, child_succ@),
        // ncl keeps the old child's first leaf; child_succ is cp's old successor.
        crate::bplus_tree::tree_leaf_ids(ncl@).len() >= 1,
        crate::bplus_tree::tree_leaf_ids(ncl@)[0] == crate::bplus_tree::tree_leaf_ids(gkids@[cp@])[0],
        child_succ@ == (if cp@ + 1 < gkids@.len() {
            crate::bplus_tree::tree_leaf_ids(gkids@[cp@ + 1])[0]
        } else { succ@ }),
        // a2 agrees with a1 on the CHILD footprints outside cp (siblings unchanged).
        // Stated over `forest_ids(kids)` (not `tree_ids(cur)`) so it excludes `gid`,
        // the parent slot — which DID change (the splice rewrote pnode at gid).
        forall|id: nat| (#[trigger] crate::bplus_tree::forest_ids(gkids@).contains(id))
            && !crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
            ==> arena1@[id as int] == arena2@[id as int],
    ensures
        leaf_links_to::<L>(arena2@,
            Tree::Inner { id: gid@, seps: gseps@.insert(cp@, sep@),
                kids: gkids@.update(cp@, ncl@).insert(cp@ + 1, ncr@) }, succ@),
{
    let a1 = arena1@; let a2 = arena2@;
    let kids = gkids@;
    let nkids = kids.update(cp@, ncl@).insert(cp@ + 1, ncr@);
    assert(crate::bplus_tree::tree_wf(cur@, h@, L::leaf_cap_spec(), L::key_cap_spec(), true));

    // each old child non-empty.
    assert forall|i: int| 0 <= i < kids.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1 by {
        crate::bplus_tree::lemma_forest_wf_at(kids, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), i);
        crate::bplus_tree::lemma_tree_leaf_ids_nonempty(kids[i], (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    }
    // decompose cur's chain to the per-child forest chain in a1.
    crate::bplus_tree::lemma_forest_ids_cons(kids);
    lemma_forest_links_decompose::<L>(a1, gid@, gseps@, kids, succ@);
    // bridge the arena agreement: outside cp's footprint, a1 == a2 (forest_ids ⊆ cur).
    assert forall|id: nat| #![trigger crate::bplus_tree::forest_ids(kids).contains(id)] #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(kids).contains(id)
        && !crate::bplus_tree::tree_ids(kids[cp@]).contains(id)
        implies a1[id as int] == a2[id as int] by {
        assert(crate::bplus_tree::tree_ids(cur@).contains(id));
    }
    // pairwise child disjointness (tree_disjoint(cur)).
    assert forall|i: int, j: int| 0 <= i < j < kids.len() implies
        (#[trigger] crate::bplus_tree::tree_ids(kids[i]))
            .disjoint(#[trigger] crate::bplus_tree::tree_ids(kids[j])) by {}
    // splice the two halves into the forest chain.
    lemma_forest_links_splice::<L>(a1, a2, kids, cp@, ncl@, ncr@, succ@, child_succ@);
    // each spliced child non-empty (for compose).
    assert forall|i: int| 0 <= i < nkids.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(nkids[i]).len() >= 1 by {
        if i < cp@ { assert(nkids[i] == kids[i]); }
        else if i == cp@ { assert(nkids[i] == ncl@); }
        else if i == cp@ + 1 { assert(nkids[i] == ncr@); }
        else { assert(nkids[i] == kids[i - 1]); }
    }
    // compose back to the whole-subtree chain at the new node.
    lemma_forest_links_compose::<L>(a2, gid@, gseps@.insert(cp@, sep@), nkids, succ@);
}

/// Reconstruct the two halves of a PARENT split (the child `cp` split into
/// `(ncl, ncr)` AND this parent was full). The twin of `reconstruct_child_split_
/// absorb` (which handles the "had room" case): `lt` (kept at `gid`) and `rt`
/// (fresh at `rid`) are both `subtree_wf` at height `h`, separated by the promoted
/// median, with combined model `cur's ∪ {key}`. Single arena, three snapshots of
/// it: `arena1` (pre-recursion), `arena_rec` (post-recursion, where `ncl`/`ncr`
/// bind), `arena2 == arena_rec.update(gid, pl).push(pr)` (post-mutation).
///
/// `sep`/`crid` are passed as REAL typed exec params (`L::Word` / `L::ArenaIdx`)
/// so `isplit_cchild(pnode, cp, crid, j)` typechecks with no conversion, and the
/// call site discharges `internal_split_at`'s `pl`/`pr` postconditions verbatim.
/// `crid` (== ncr's root) is the recursion's right-half id; it is NOT `rid` (rt's
/// root, the fresh push slot) — the two are deliberately distinct params.
///
/// `rlimit(50)`: this composes eight building-block lemmas (tree_wf, two
/// half_binds, the link splice + half_links, two half_ids, footprint, disjoint)
/// in one body; the bump over the default covers the combined query (raised
/// 30→50 when the Vec wf gained the `!TRACK ⟹ no frames` conjunct, which
/// enlarges the ambient context this instantiates against).
#[verifier::rlimit(50)]
pub(crate) proof fn reconstruct_parent_split<K, L, S, const TRACK: bool>(
    arena1: Ghost<Seq<L::Node>>,
    arena_rec: Ghost<Seq<L::Node>>,
    arena2: Ghost<Seq<L::Node>>,
    cur: Ghost<Tree>,
    gseps: Ghost<Seq<nat>>,
    gkids: Ghost<Seq<Tree>>,
    cp: Ghost<int>,
    ncl: Ghost<Tree>,
    ncr: Ghost<Tree>,
    child_succ: Ghost<nat>,
    lt: Ghost<Tree>,
    rt: Ghost<Tree>,
    sep: L::Word,
    crid: L::ArenaIdx,
    gid: Ghost<nat>,
    h: Ghost<nat>,
    succ: Ghost<nat>,
    key: K,
    rid: L::ArenaIdx,
    pnode: Ghost<L::Node>,
    pl: Ghost<L::Node>,
    pr: Ghost<L::Node>,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        cur@ == (Tree::Inner { id: gid@, seps: gseps@, kids: gkids@ }),
        h@ == crate::bplus_tree::tree_height(cur@),
        h@ >= 1,
        0 <= cp@ < gkids@.len(),
        // parent was FULL (the split-branch guard `n == kc`).
        gseps@.len() == L::key_cap_spec(),
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena1@, cur@, h@, succ@, true),
        // ---- the recursion's `Some` products (child cp split into ncl, ncr) ----
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena_rec@, ncl@, (h@ - 1) as nat,
            crate::bplus_tree::tree_leaf_ids(ncr@)[0], false),
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena_rec@, ncr@, (h@ - 1) as nat, child_succ@, false),
        crate::bplus_tree::tree_root_id(ncl@) == crate::bplus_tree::tree_root_id(gkids@[cp@]),
        crate::bplus_tree::tree_root_id(ncr@) == crid.as_nat(),
        crate::bplus_tree::tree_keys(ncl@).len() >= 1,
        crate::bplus_tree::tree_keys(ncr@).len() >= 1,
        crate::bplus_tree::keys_all_lt(ncl@, sep.as_nat()),
        crate::bplus_tree::keys_all_ge(ncr@, sep.as_nat()),
        (crate::bplus_tree::tree_keys(ncl@) + crate::bplus_tree::tree_keys(ncr@)).to_set()
            == crate::bplus_tree::tree_keys(gkids@[cp@]).to_set().insert(key.id_nat()),
        child_succ@ == (if cp@ + 1 < gkids@.len() {
            crate::bplus_tree::tree_leaf_ids(gkids@[cp@ + 1])[0]
        } else { succ@ }),
        crate::bplus_tree::tree_leaf_ids(ncl@).len() >= 1,
        crate::bplus_tree::tree_leaf_ids(ncl@)[0] == crate::bplus_tree::tree_leaf_ids(gkids@[cp@])[0],
        (forall|id: nat| #[trigger] crate::bplus_tree::tree_ids(ncl@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        (forall|id: nat| #[trigger] crate::bplus_tree::tree_ids(ncr@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        (forall|id: nat| #![trigger crate::bplus_tree::tree_ids(ncl@).contains(id)] #![trigger crate::bplus_tree::tree_ids(ncr@).contains(id)] crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
            ==> crate::bplus_tree::tree_ids(ncl@).contains(id) || crate::bplus_tree::tree_ids(ncr@).contains(id)),
        crate::bplus_tree::tree_ids(ncl@).disjoint(crate::bplus_tree::tree_ids(ncr@)),
        // recursion frame: slots < arena1.len() outside child cp's footprint are
        // unchanged in arena_rec (the parent slot gid is still its original pnode).
        (forall|i: int| 0 <= i < arena1@.len()
            && !crate::bplus_tree::tree_ids(gkids@[cp@]).contains(i as nat)
            ==> arena_rec@[i] == arena1@[i]),
        arena1@.len() <= arena_rec@.len(),
        // ---- the two ghost halves (subranges of the combined arrangement) ----
        ({
            let cseps = gseps@.insert(cp@, sep.as_nat());
            let ckids = gkids@.update(cp@, ncl@).insert(cp@ + 1, ncr@);
            let imid = L::isplit_mid_spec() as int;
            &&& lt@ == (Tree::Inner { id: gid@, seps: cseps.subrange(0, imid), kids: ckids.subrange(0, imid + 1) })
            &&& rt@ == (Tree::Inner { id: rid.as_nat(), seps: cseps.subrange(imid + 1, cseps.len() as int),
                    kids: ckids.subrange(imid + 1, ckids.len() as int) })
        }),
        // ---- pnode is the original parent node at gid (binds gkids' roots) ----
        pnode@ == arena1@[gid@ as int],
        !L::is_leaf_spec(pnode@),
        crate::bplus_tree::tree_root_id(cur@) == gid@,
        L::count_spec(pnode@) == gseps@.len(),
        L::node_wf(pnode@),
        (forall|i: int| 0 <= i < gseps@.len() ==> (#[trigger] L::keys_view(pnode@)[i]).as_nat() == gseps@[i]),
        (forall|i: int| 0 <= i < gkids@.len() ==> L::child_view(pnode@, i) == crate::bplus_tree::tree_root_id(#[trigger] gkids@[i])),
        cp@ <= gseps@.len(),
        // ---- pl/pr view facts (internal_split_at's tuple ensures, verbatim) ----
        // pl is the left half [0..imid] of `keys_view(pnode).insert(cp, sep)`, pr
        // the right half [imid+1..]; children carved by isplit_cchild with the
        // recursion's right-half id `crid` as new_child (internal_split_at was
        // called with `crid` == ncr's root, NOT `rid` == rt's fresh push slot).
        // Stated in Word-space exactly as the mutator emits.
        !L::is_leaf_spec(pl@),
        !L::is_leaf_spec(pr@),
        L::node_wf(pl@),
        L::node_wf(pr@),
        L::count_spec(pl@) == L::isplit_mid_spec(),
        L::count_spec(pr@) == (L::key_cap_spec() - L::isplit_mid_spec()) as nat,
        L::keys_view(pl@) == L::keys_view(pnode@).insert(cp@, sep).subrange(0, L::isplit_mid_spec() as int),
        L::keys_view(pr@) == L::keys_view(pnode@).insert(cp@, sep).subrange(
            L::isplit_mid_spec() as int + 1, (L::key_cap_spec() + 1) as int),
        (forall|j: int| 0 <= j <= L::isplit_mid_spec() ==>
            #[trigger] L::child_view(pl@, j) == L::isplit_cchild(pnode@, cp@, crid, j)),
        (forall|j: int| 0 <= j <= (L::key_cap_spec() - L::isplit_mid_spec()) ==>
            #[trigger] L::child_view(pr@, j) == L::isplit_cchild(pnode@, cp@, crid, L::isplit_mid_spec() as int + 1 + j)),
        // ---- arena2 layout: set(gid, pl) then push(pr) at new_int == rid ----
        arena2@ == arena_rec@.update(gid@ as int, pl@).push(pr@),
        rid.as_nat() == arena_rec@.len(),
        gid@ < arena_rec@.len(),
        // descent routing (key within the surrounding separators).
        (forall|j: int| 0 <= j < cp@ ==> gseps@[j] <= key.id_nat()),
        (forall|j: int| cp@ <= j < gseps@.len() ==> key.id_nat() < gseps@[j]),
    ensures
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena2@, lt@, h@,
            crate::bplus_tree::tree_leaf_ids(rt@)[0], false),
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena2@, rt@, h@, succ@, false),
        crate::bplus_tree::tree_root_id(lt@) == gid@,
        crate::bplus_tree::tree_root_id(rt@) == rid.as_nat(),
        crate::bplus_tree::tree_keys(rt@).len() >= 1,
        ({
            let promoted = gseps@.insert(cp@, sep.as_nat())[L::isplit_mid_spec() as int];
            // cross-node ordering of the two halves around the promoted median.
            &&& crate::bplus_tree::keys_all_lt(lt@, promoted)
            &&& crate::bplus_tree::keys_all_ge(rt@, promoted)
        }),
        (crate::bplus_tree::tree_keys(lt@) + crate::bplus_tree::tree_keys(rt@)).to_set()
            == crate::bplus_tree::tree_keys(cur@).to_set().insert(key.id_nat()),
        (forall|id: nat| crate::bplus_tree::tree_ids(lt@).contains(id)
            ==> crate::bplus_tree::tree_ids(cur@).contains(id) || id >= arena1@.len()),
        (forall|id: nat| crate::bplus_tree::tree_ids(rt@).contains(id)
            ==> crate::bplus_tree::tree_ids(cur@).contains(id) || id >= arena1@.len()),
        // FRAME: arena grew, and every old slot outside cur's footprint is unchanged.
        arena1@.len() <= arena2@.len(),
        (forall|i: int| 0 <= i < arena1@.len()
            && !crate::bplus_tree::tree_ids(cur@).contains(i as nat)
            ==> #[trigger] arena2@[i] == arena1@[i]),
        // the two halves have disjoint footprints, retain cur's ids, and lt keeps
        // cur's leftmost leaf (the shape the grandparent's `Some` arm consumes).
        crate::bplus_tree::tree_ids(lt@).disjoint(crate::bplus_tree::tree_ids(rt@)),
        (forall|id: nat| crate::bplus_tree::tree_ids(cur@).contains(id)
            ==> crate::bplus_tree::tree_ids(lt@).contains(id) || crate::bplus_tree::tree_ids(rt@).contains(id)),
        crate::bplus_tree::tree_leaf_ids(lt@).len() >= 1,
        crate::bplus_tree::tree_leaf_ids(lt@)[0] == crate::bplus_tree::tree_leaf_ids(cur@)[0],
{
    let a1 = arena1@; let ar = arena_rec@; let a2 = arena2@;
    let kids = gkids@;
    let cseps = gseps@.insert(cp@, sep.as_nat());
    let ckids = kids.update(cp@, ncl@).insert(cp@ + 1, ncr@);
    let imid = L::isplit_mid_spec() as int;
    let promoted = cseps[imid];
    let cur_t = cur@;
    L::lemma_arena_capacity();
    L::lemma_isplit_mid();  // imid == key_cap/2, 1 <= imid < key_cap
    assert(crate::bplus_tree::tree_wf(cur_t, h@, L::leaf_cap_spec(), L::key_cap_spec(), false));
    assert(kids.len() == gseps@.len() + 1);
    assert(cseps.len() == L::key_cap_spec() + 1);
    assert(ckids.len() == cseps.len() + 1);

    // ---- (1) tree_wf(lt) + tree_wf(rt) + model + cross-half ordering. ----
    crate::bplus_tree::lemma_parent_split_tree_wf(
        gid@, rid.as_nat(), gseps@, kids, cp@, ncl@, ncr@, sep.as_nat(), key.id_nat(),
        imid, h@, L::leaf_cap_spec(), L::key_cap_spec());
    assert(crate::bplus_tree::tree_wf(lt@, h@, L::leaf_cap_spec(), L::key_cap_spec(), false));
    assert(crate::bplus_tree::tree_wf(rt@, h@, L::leaf_cap_spec(), L::key_cap_spec(), false));
    assert(crate::bplus_tree::keys_all_lt(lt@, promoted));
    assert(crate::bplus_tree::keys_all_ge(rt@, promoted));
    // model: (lt+rt) == cur ∪ {key} (lemma states it vs Inner{gid,gseps,gkids} == cur).
    assert((crate::bplus_tree::tree_keys(lt@) + crate::bplus_tree::tree_keys(rt@)).to_set()
        == crate::bplus_tree::tree_keys(cur_t).to_set().insert(key.id_nat()));

    // rt non-empty: rt is wf at h>=1 non-root ⟹ carries >= 1 key.
    crate::bplus_tree::lemma_tree_keys_nonempty(rt@, h@, L::leaf_cap_spec(), L::key_cap_spec());

    // ---- arena framing scaffolding: relate a2 to ar, a1. ----
    // a2 == ar.update(gid, pl).push(pr): slot gid is pl, slot rid (== ar.len()) is
    // pr, every other old slot < ar.len() is ar's, and a2.len() == ar.len()+1.
    assert(a2.len() == ar.len() + 1);
    assert(a2[gid@ as int] == pl@) by { assert(gid@ < ar.len()); }
    assert(a2[rid.as_nat() as int] == pr@);
    assert forall|i: int| 0 <= i < ar.len() && i != gid@ implies a2[i] == ar[i] by {}

    // pl/pr views are preconditions (internal_split_at's tuple ensures, verbatim).
    assert(L::count_spec(pl@) == imid);
    assert(L::count_spec(pr@) == (L::key_cap_spec() - imid) as nat);

    // ---- (2) binds(a2, lt) and binds(a2, rt). ----
    // First, forest_binds_l(a2, ckids): ncl/ncr bind in a2 (framed from ar across
    // set(gid,pl)+push(pr); gid ∉ their footprints, pr is a fresh tail slot), and
    // siblings bind from a1.
    assert(binds::<L>(a1, cur_t));
    // gid ∉ tree_ids(ncl)/tree_ids(ncr) (parent id, outside child cp; ncl/ncr ⊆ cp ∪ fresh).
    crate::bplus_tree::lemma_node_id_not_in_child::<>(cur_t, cp@);
    lemma_tree_id_in_range::<L>(a1, cur_t, gid@);
    assert(crate::bplus_tree::tree_ids(cur_t).contains(gid@));
    assert(gid@ < a1.len());
    assert(!crate::bplus_tree::tree_ids(gkids@[cp@]).contains(gid@));
    if crate::bplus_tree::tree_ids(ncl@).contains(gid@) {
        assert(crate::bplus_tree::tree_ids(gkids@[cp@]).contains(gid@) || gid@ >= a1.len());
        assert(false);
    }
    if crate::bplus_tree::tree_ids(ncr@).contains(gid@) {
        assert(crate::bplus_tree::tree_ids(gkids@[cp@]).contains(gid@) || gid@ >= a1.len());
        assert(false);
    }
    // ncl/ncr bind in a2: frame from ar across the single set(gid,pl) (gid ∉ their
    // footprints) and the push (a tail extension preserves binds). Discharge the
    // agreement (ar == a2 on each footprint) BEFORE the frame lemma call.
    assert forall|id: nat| #![trigger ar[id as int]] #![trigger a2[id as int]] crate::bplus_tree::tree_ids(ncl@).contains(id)
        implies ar[id as int] == a2[id as int] by {
        lemma_tree_id_in_range::<L>(ar, ncl@, id);  // id < ar.len()
        assert(id != gid@);  // gid ∉ tree_ids(ncl)
    }
    lemma_binds_frame::<L>(ar, a2, ncl@);
    assert forall|id: nat| #![trigger ar[id as int]] #![trigger a2[id as int]] crate::bplus_tree::tree_ids(ncr@).contains(id)
        implies ar[id as int] == a2[id as int] by {
        lemma_tree_id_in_range::<L>(ar, ncr@, id);
        assert(id != gid@);  // gid ∉ tree_ids(ncr)
    }
    lemma_binds_frame::<L>(ar, a2, ncr@);
    assert(binds::<L>(a2, ncl@));
    assert(binds::<L>(a2, ncr@));
    // siblings (a1, cur) are unchanged from a1 to a2 outside child cp & gid: ar ==
    // a1 there (recursion frame), and a2 == ar there too. Bridge for splice-binds.
    assert forall|i: int| 0 <= i < a1.len()
        && !crate::bplus_tree::tree_ids(gkids@[cp@]).contains(i as nat)
        && i != gid@
        implies a2[i] == a1[i] by {
        assert(ar[i] == a1[i]);  // recursion frame
        assert(i < ar.len());    // a1.len() <= ar.len()
        assert(a2[i] == ar[i]);  // i != gid, i < ar.len()
    }
    lemma_splice_children_bind::<K, L, S, TRACK>(a1, a2, cur_t, gid@, gseps@, kids, cp@, ncl@, ncr@);
    assert(forest_binds_l::<L>(a2, ckids));

    // binds(a2, lt): the half node pl at gid, via lemma_parent_split_half_binds.
    assert(L::keys_view(a1[gid@ as int]).len() == gseps@.len()) by {
        L::lemma_keys_view_len(a1[gid@ as int]);
    }
    // Word→nat projection of the combined separator list: keys_view(pnode).insert
    // (cp, sep) projects index-wise to cseps == gseps.insert(cp, sep.as_nat()).
    let cwords = L::keys_view(pnode@).insert(cp@, sep);
    assert(cwords.len() == cseps.len());
    assert forall|k: int| 0 <= k < cseps.len() implies (#[trigger] cwords[k]).as_nat() == cseps[k] by {
        if k < cp@ {
            assert(cwords[k] == L::keys_view(pnode@)[k]);  // insert below cp
            assert(cseps[k] == gseps@[k]);
        } else if k == cp@ {
            assert(cwords[k] == sep);
            assert(cseps[k] == sep.as_nat());
        } else {
            assert(cwords[k] == L::keys_view(pnode@)[k - 1]);  // insert above cp
            assert(cseps[k] == gseps@[k - 1]);
        }
    }
    // pl/pr keys project to the cseps subranges (the half_binds keys precondition).
    assert forall|i: int| 0 <= i < imid implies
        (#[trigger] L::keys_view(pl@)[i]).as_nat() == cseps[0 + i] by {
        assert(L::keys_view(pl@)[i] == cwords[i]);  // subrange(0,imid)
    }
    assert forall|i: int| 0 <= i < (L::key_cap_spec() - imid) implies
        (#[trigger] L::keys_view(pr@)[i]).as_nat() == cseps[(imid + 1) + i] by {
        assert(L::keys_view(pr@)[i] == cwords[imid + 1 + i]);  // subrange(imid+1, ..)
    }
    lemma_parent_split_half_binds::<K, L, S, TRACK>(
        a1, a2, gid@, gseps@, kids, cp@, ncl@, ncr@, sep.as_nat(), crid, pnode@,
        gid@, pl@, 0, imid);
    assert(binds::<L>(a2, lt@));
    // binds(a2, rt): the half node pr at rid (== new_int), off == imid+1, slen ==
    // key_cap-imid. The isplit_cchild new_child arg is `crid` (ncr's root), not rid.
    lemma_parent_split_half_binds::<K, L, S, TRACK>(
        a1, a2, gid@, gseps@, kids, cp@, ncl@, ncr@, sep.as_nat(), crid, pnode@,
        rid.as_nat(), pr@, imid + 1, (L::key_cap_spec() - imid) as int);
    assert(binds::<L>(a2, rt@));

    // ---- (3) leaf_links_to(a2, lt, rt's first leaf) and leaf_links_to(a2, rt, succ). ----
    // First build forest_links_to(a2, ckids, succ) via the child-split splice
    // (identical to reconstruct_child_split_links' middle step), then split it at
    // m == imid+1 into the two halves.
    crate::bplus_tree::lemma_tree_leaf_ids_nonempty(ncr@, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    crate::bplus_tree::lemma_tree_leaf_ids_nonempty(ncl@, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    // each old child non-empty.
    assert forall|i: int| 0 <= i < kids.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1 by {
        crate::bplus_tree::lemma_forest_wf_at(kids, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), i);
        crate::bplus_tree::lemma_tree_leaf_ids_nonempty(kids[i], (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    }
    // ncl/ncr's chains in a2 (framed from ar; subtree_wf(ar, ncl, .., ncr[0]) gives
    // the chain, and a2 agrees with ar on their footprints — discharge agreement
    // BEFORE the frame call). These reuse the agreements proven above for binds.
    lemma_leaf_links_frame::<L>(ar, a2, ncl@, crate::bplus_tree::tree_leaf_ids(ncr@)[0]);
    lemma_leaf_links_frame::<L>(ar, a2, ncr@, child_succ@);
    assert(leaf_links_to::<L>(a2, ncl@, crate::bplus_tree::tree_leaf_ids(ncr@)[0]));
    assert(leaf_links_to::<L>(a2, ncr@, child_succ@));
    // decompose cur's chain in a1, splice in ncl/ncr to get forest_links_to(a2, ckids).
    crate::bplus_tree::lemma_forest_ids_cons(kids);
    lemma_forest_links_decompose::<L>(a1, gid@, gseps@, kids, succ@);
    assert forall|id: nat| #![trigger crate::bplus_tree::forest_ids(kids).contains(id)] #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(kids).contains(id)
        && !crate::bplus_tree::tree_ids(kids[cp@]).contains(id)
        implies a1[id as int] == a2[id as int] by {
        assert(crate::bplus_tree::tree_ids(cur_t).contains(id));
        lemma_tree_id_in_range::<L>(a1, cur_t, id);
        assert(!crate::bplus_tree::forest_ids(kids).contains(gid@));  // tree_disjoint(cur)
        assert(id != gid@);
    }
    assert forall|i: int, j: int| 0 <= i < j < kids.len() implies
        (#[trigger] crate::bplus_tree::tree_ids(kids[i]))
            .disjoint(#[trigger] crate::bplus_tree::tree_ids(kids[j])) by {}
    lemma_forest_links_splice::<L>(a1, a2, kids, cp@, ncl@, ncr@, succ@, child_succ@);
    assert(forest_links_to::<L>(a2, ckids, succ@));
    // each spliced child non-empty.
    assert forall|i: int| 0 <= i < ckids.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(ckids[i]).len() >= 1 by {
        if i < cp@ { assert(ckids[i] == kids[i]); }
        else if i == cp@ { assert(ckids[i] == ncl@); }
        else if i == cp@ + 1 { assert(ckids[i] == ncr@); }
        else { assert(ckids[i] == kids[i - 1]); }
    }
    // split the chain at m == imid+1 into the two halves' chains.
    lemma_parent_split_half_links::<L>(a2, ckids, gid@, rid.as_nat(),
        cseps.subrange(0, imid), cseps.subrange(imid + 1, cseps.len() as int), succ@, imid + 1);
    // the half-links lemma states the chains for Inner nodes with ckids subranges;
    // those ARE lt/rt (same id, seps, kids).
    assert(crate::bplus_tree::tree_leaf_ids(ckids[imid + 1])[0] == crate::bplus_tree::tree_leaf_ids(rt@)[0]) by {
        // rt's first child is ckids[imid+1] (rt.kids == ckids[imid+1..]).
        assert(rt@->Inner_kids[0] == ckids[imid + 1]);
        crate::bplus_tree::lemma_forest_leaf_ids_cons(rt@->Inner_kids);
    }
    assert(leaf_links_to::<L>(a2, lt@, crate::bplus_tree::tree_leaf_ids(rt@)[0]));
    assert(leaf_links_to::<L>(a2, rt@, succ@));

    // ---- (4) footprint / disjoint / first-leaf. ----
    let lkids = ckids.subrange(0, imid + 1);
    let rkids = ckids.subrange(imid + 1, ckids.len() as int);
    assert(lkids + rkids =~= ckids) by {
        assert(ckids.subrange(0, imid + 1) + ckids.subrange(imid + 1, ckids.len() as int) =~= ckids);
    }
    // forest_disjoint(ckids) + pairwise + gid ∉ forest_ids(ckids): the combined
    // node Inner{gid, cseps, ckids} is tree_disjoint, by the SAME pure-ghost ids
    // lemma the child-split absorb uses. tree_disjoint unfolds to exactly these.
    let combined = Tree::Inner { id: gid@, seps: cseps, kids: ckids };
    assert(crate::bplus_tree::tree_disjoint(cur_t));  // subtree_wf(a1, cur)
    assert forall|id: nat| #[trigger] crate::bplus_tree::tree_ids(cur_t).contains(id) implies id < a1.len() by {
        lemma_tree_id_in_range::<L>(a1, cur_t, id);
    }
    assert(crate::bplus_tree::tree_disjoint(ncl@));  // subtree_wf(ar, ncl)
    assert(crate::bplus_tree::tree_disjoint(ncr@));  // subtree_wf(ar, ncr)
    crate::bplus_tree::lemma_child_split_absorb_ids(
        gid@, gseps@, kids, cp@, ncl@, ncr@, sep.as_nat(), a1.len());
    assert(crate::bplus_tree::tree_disjoint(combined));  // == lemma's `nt`
    assert(!crate::bplus_tree::forest_ids(ckids).contains(gid@));  // tree_disjoint(combined)
    assert(crate::bplus_tree::forest_disjoint(ckids));
    assert forall|i: int, j: int| 0 <= i < j < ckids.len() implies
        (#[trigger] crate::bplus_tree::tree_ids(ckids[i]))
            .disjoint(#[trigger] crate::bplus_tree::tree_ids(ckids[j])) by {}  // tree_disjoint(combined)
    // freshness of ckids' ids: combined retains cur's ids and adds only fresh ones.
    assert forall|id: nat| #[trigger] crate::bplus_tree::forest_ids(ckids).contains(id)
        implies crate::bplus_tree::forest_ids(kids).contains(id) || id >= a1.len() by {
        // forest_ids(ckids) ⊆ tree_ids(combined); lemma: combined's ids are cur's ∪ fresh.
        assert(crate::bplus_tree::tree_ids(combined).contains(id)) by {
            assert(crate::bplus_tree::tree_ids(combined) =~= set![gid@].union(crate::bplus_tree::forest_ids(ckids)));
        }
        // combined's ids ⊆ cur's ∪ {>= a1.len()} (lemma ensures), and gid ∉ ckids.
        assert(crate::bplus_tree::tree_ids(cur_t).contains(id) || id >= a1.len());
        if crate::bplus_tree::tree_ids(cur_t).contains(id) && id != gid@ {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));  // tree_ids(cur)=={gid}∪forest_ids(kids)
        }
    }
    assert(crate::bplus_tree::forest_ids(kids).subset_of(crate::bplus_tree::forest_ids(ckids))) by {
        // cur's children ids are retained in the splice (combined ⊇ cur).
        assert(crate::bplus_tree::tree_ids(cur_t).subset_of(crate::bplus_tree::tree_ids(combined)));
        assert forall|id: nat| crate::bplus_tree::forest_ids(kids).contains(id)
            implies crate::bplus_tree::forest_ids(ckids).contains(id) by {
            assert(crate::bplus_tree::tree_ids(cur_t).contains(id));
            assert(crate::bplus_tree::tree_ids(combined).contains(id));
            if id == gid@ { assert(false); }  // gid ∉ forest_ids(ckids), and gid ∉ forest_ids(kids)
        }
    }
    // every ckids id is < ar.len() (the splice's children all bind in a2 == ar +
    // tail; binds in-range puts each tree id below the arena length). Old ids are
    // < a1.len() <= ar.len(); fresh ones the recursion allocated are < ar.len().
    assert forall|id: nat| #[trigger] crate::bplus_tree::forest_ids(ckids).contains(id)
        implies id < ar.len() by {
        crate::bplus_tree::lemma_forest_id_in_some_child(ckids, id);
        let m = choose|m: int| 0 <= m < ckids.len() && #[trigger] crate::bplus_tree::tree_ids(ckids[m]).contains(id);
        // ckids[m] binds in a2 (forest_binds_l(a2, ckids)); a tree id < a2.len() == ar.len()+1.
        lemma_forest_binds_at::<L>(a2, ckids, m);
        lemma_tree_id_in_range::<L>(a2, ckids[m], id);  // id < a2.len() == ar.len()+1
        // and id != rid (== ar.len()): rid is gid-or-fresh root of rt, the slot pr,
        // which is NOT a child root inside ckids (ckids roots are gkids/ncl/ncr).
        if id == rid.as_nat() {
            // rid == ar.len() is the freshly pushed pr slot; no ckids child has it
            // as an id (ncl/ncr ids are < ar.len(): they bind in arena_rec).
            assert(id < ar.len()) by {
                if crate::bplus_tree::tree_ids(ncl@).contains(id) { lemma_tree_id_in_range::<L>(ar, ncl@, id); }
                else if crate::bplus_tree::tree_ids(ncr@).contains(id) { lemma_tree_id_in_range::<L>(ar, ncr@, id); }
                else {
                    // id is in some old sibling gkids[j], all < a1.len() <= ar.len().
                    assert(crate::bplus_tree::tree_ids(cur_t).contains(id)) by {
                        crate::bplus_tree::lemma_child_ids_in_forest(kids, if m < cp@ { m } else { m - 1 }, id);
                    }
                    lemma_tree_id_in_range::<L>(a1, cur_t, id);
                }
            }
        }
    }
    assert(!crate::bplus_tree::forest_ids(ckids).contains(gid@)) by {
        // gid ∉ forest_ids(ckids) was shown via tree_disjoint(combined) above.
    }
    // disjoint footprints of lt and rt (distinct roots gid (< ar.len()), rid (== ar.len())).
    crate::bplus_tree::lemma_parent_split_disjoint(gid@, rid.as_nat(), ckids, lt@, rt@, lkids, rkids, ar.len());
    // tree_disjoint of each half (subrange of forest_disjoint(ckids) + pairwise; the
    // half root gid/rid ∉ its children's footprints). lemma_parent_split_half_ids
    // gives it for the empty-seps Inner, which has the SAME tree_ids as lt/rt (seps-
    // independent), so tree_disjoint transfers.
    crate::bplus_tree::lemma_parent_split_half_ids(ckids, gid@, 0, imid, ar.len());
    crate::bplus_tree::lemma_parent_split_half_ids(ckids, rid.as_nat(), imid + 1,
        (L::key_cap_spec() - imid) as int, ar.len());
    assert(crate::bplus_tree::tree_disjoint(lt@)) by {
        assert(crate::bplus_tree::tree_disjoint(Tree::Inner { id: gid@, seps: Seq::<nat>::empty(), kids: lkids }));
        // tree_disjoint reads only id + kids, and lt has id==gid, kids==lkids.
    }
    assert(crate::bplus_tree::tree_disjoint(rt@)) by {
        assert(crate::bplus_tree::tree_disjoint(Tree::Inner { id: rid.as_nat(), seps: Seq::<nat>::empty(), kids: rkids }));
    }
    // footprint subset/freshness/first-leaf via lemma_parent_split_footprint.
    crate::bplus_tree::lemma_parent_split_footprint(
        cur_t, gid@, rid.as_nat(), kids, lt@, rt@, lkids, rkids, ckids, a1.len());
    assert(crate::bplus_tree::tree_ids(lt@).disjoint(crate::bplus_tree::tree_ids(rt@)));
    assert(crate::bplus_tree::tree_leaf_ids(lt@)[0] == crate::bplus_tree::tree_leaf_ids(cur_t)[0]);

    // ---- (5) subtree_wf assembly + the global frame ensures. ----
    assert(BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(a2, lt@, h@, crate::bplus_tree::tree_leaf_ids(rt@)[0], false));
    assert(BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(a2, rt@, h@, succ@, false));
    // global frame: slots < a1.len() outside tree_ids(cur) are unchanged in a2.
    assert forall|i: int| 0 <= i < a1.len()
        && !crate::bplus_tree::tree_ids(cur_t).contains(i as nat)
        implies a2[i] == a1[i] by {
        // i != gid (gid ∈ tree_ids(cur)); i outside child cp ⟹ ar[i]==a1[i]; i<ar.len.
        assert(i != gid@);
        if crate::bplus_tree::tree_ids(gkids@[cp@]).contains(i as nat) {
            crate::bplus_tree::lemma_child_ids_in_forest(kids, cp@, i as nat);
            assert(crate::bplus_tree::tree_ids(cur_t).contains(i as nat));  // contradiction
        }
        assert(ar[i] == a1[i]);
        assert(i < ar.len());
        assert(a2[i] == ar[i]);
    }
}

/// Leaf-link sub-step of [`reconstruct_absorb`]: `leaf_links_to(a2, nt, succ)`
/// via `forest_links_to` over the updated children, then `lemma_forest_links_
/// compose`. The child `cp`'s chain (to `child_succ`) is the recursion's result;
/// the others are framed from `cur`'s chain.
pub(crate) proof fn reconstruct_absorb_links<K, L, S, const TRACK: bool>(
    arena1: Ghost<Seq<L::Node>>,
    arena2: Ghost<Seq<L::Node>>,
    cur: Ghost<Tree>,
    ncl: Ghost<Tree>,
    gid: Ghost<nat>,
    gseps: Ghost<Seq<nat>>,
    gkids: Ghost<Seq<Tree>>,
    cp: Ghost<int>,
    h: Ghost<nat>,
    succ: Ghost<nat>,
    child_succ: Ghost<nat>,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        cur@ == (Tree::Inner { id: gid@, seps: gseps@, kids: gkids@ }),
        h@ == crate::bplus_tree::tree_height(cur@),
        0 <= cp@ < gkids@.len(),
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena1@, cur@, h@, succ@, true),
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena2@, ncl@, (h@ - 1) as nat, child_succ@, false),
        crate::bplus_tree::tree_root_id(ncl@) == crate::bplus_tree::tree_root_id(gkids@[cp@]),
        // child footprint: subset+freshness (ncl GREW under a deep absorb), with
        // the leftmost leaf pinned. The links chain reads only each child's FIRST
        // leaf at boundaries, so first-leaf preservation is all it needs — the
        // full leaf-id sequence may legitimately grow. (Contract fix; (F0).)
        crate::bplus_tree::tree_ids(gkids@[cp@]).subset_of(crate::bplus_tree::tree_ids(ncl@)),
        (forall|id: nat| #[trigger] crate::bplus_tree::tree_ids(ncl@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        crate::bplus_tree::tree_leaf_ids(ncl@)[0] == crate::bplus_tree::tree_leaf_ids(gkids@[cp@])[0],
        child_succ@ == (if cp@ + 1 < gkids@.len() {
            crate::bplus_tree::tree_leaf_ids(gkids@[cp@ + 1])[0]
        } else { succ@ }),
        arena1@.len() <= arena2@.len(),
        forall|id: nat| (#[trigger] crate::bplus_tree::tree_ids(cur@).contains(id))
            && !crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
            ==> arena1@[id as int] == arena2@[id as int],
    ensures
        leaf_links_to::<L>(arena2@, Tree::Inner { id: gid@, seps: gseps@, kids: gkids@.update(cp@, ncl@) }, succ@),
{
    let a1 = arena1@; let a2 = arena2@;
    let kids = gkids@;
    let nkids = kids.update(cp@, ncl@);
    let cur_t = cur@;

    // each child non-empty (tree_wf at h-1).
    assert forall|i: int| 0 <= i < nkids.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(nkids[i]).len() >= 1 by {
        crate::bplus_tree::lemma_forest_wf_at(kids, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), i);
        if i == cp@ {
            assert(nkids[i] == ncl@);
            crate::bplus_tree::lemma_tree_leaf_ids_nonempty(ncl@, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
        } else {
            assert(nkids[i] == kids[i]);
            crate::bplus_tree::lemma_tree_leaf_ids_nonempty(kids[i], (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
        }
    }
    // child-boundary successors are unchanged by the update: at each boundary the
    // link chain reads the next child's FIRST leaf, and first-leaves are pinned
    // (cp's by the precondition, every other child verbatim). Full leaf-id-seq
    // equality is NOT asserted (ncl may have grown), only the first leaf.
    assert forall|i: int| 0 <= i < nkids.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(nkids[i])[0] == crate::bplus_tree::tree_leaf_ids(kids[i])[0] by {
        if i == cp@ { assert(nkids[i] == ncl@); } else { assert(nkids[i] == kids[i]); }
    }

    // bridge: forest_ids agreement (from tree_ids(cur) agreement; forest_ids(kids)
    // ⊆ tree_ids(cur)), and pairwise child disjointness (tree_disjoint(cur)).
    assert forall|id: nat| #![trigger crate::bplus_tree::forest_ids(kids).contains(id)] #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(kids).contains(id)
        && !crate::bplus_tree::tree_ids(kids[cp@]).contains(id)
        implies a1[id as int] == a2[id as int] by {
        crate::bplus_tree::lemma_forest_ids_cons(kids);
        assert(crate::bplus_tree::tree_ids(cur_t).contains(id));  // {gid} ∪ forest_ids(kids)
    }
    assert forall|i: int, j: int| 0 <= i < j < kids.len() implies
        (#[trigger] crate::bplus_tree::tree_ids(kids[i]))
            .disjoint(#[trigger] crate::bplus_tree::tree_ids(kids[j])) by {
        // tree_disjoint(cur) Inner arm.
    }
    // each OLD child non-empty (needed by decompose over `kids` and by the
    // build over `gkids`); from cur's tree_wf at h-1.
    assert forall|i: int| 0 <= i < kids.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1 by {
        crate::bplus_tree::lemma_forest_wf_at(kids, (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), i);
        crate::bplus_tree::lemma_tree_leaf_ids_nonempty(kids[i], (h@ - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    }
    // forest_links_to(a1, kids, succ) (decompose cur's chain), then build for a2.
    let gid = cur_t->Inner_id;
    lemma_forest_links_decompose::<L>(a1, gid, gseps@, kids, succ@);
    lemma_build_forest_links::<K, L, S, TRACK>(arena1, arena2, cur, ncl, gkids, cp, h, succ, child_succ);
    lemma_forest_links_compose::<L>(a2, gid, gseps@, nkids, succ@);
}

/// Decompose an internal node's chain into `forest_links_to` over its children
/// (the converse of `lemma_forest_links_compose`): from `leaf_links_to(arena,
/// Inner{.., kids}, succ)` derive `forest_links_to(arena, kids, succ)`, via the
/// per-child projection `lemma_leaf_links_project`.
pub(crate) proof fn lemma_forest_links_decompose<L: NodeLayout>(
    arena: Seq<L::Node>,
    id: nat,
    seps: Seq<nat>,
    kids: Seq<Tree>,
    succ: nat,
)
    requires
        leaf_links_to::<L>(arena, Tree::Inner { id, seps, kids }, succ),
        forall|i: int| 0 <= i < kids.len() ==> #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1,
    ensures
        forest_links_to::<L>(arena, kids, succ),
    decreases kids,
{
    if kids.len() == 0 {
    } else {
        // child 0's chain to (kids[1]'s first leaf | succ) via projection at cp==0.
        lemma_leaf_links_project::<L>(arena, id, seps, kids, succ, 0);
        // tail: leaf_links_to(Inner{.., kids.drop_first()}, succ) then recurse.
        let df = kids.drop_first();
        assert forall|i: int| 0 <= i < df.len() implies
            #[trigger] crate::bplus_tree::tree_leaf_ids(df[i]).len() >= 1 by {
            assert(df[i] == kids[i + 1]);
        }
        lemma_links_drop_first::<L>(arena, id, seps, kids, succ);
        lemma_forest_links_decompose::<L>(arena, id, seps.drop_first(), df, succ);
    }
}

/// `leaf_links_to(Inner{.., kids}, succ)` restricted to the tail children:
/// `leaf_links_to(Inner{.., kids.drop_first()}, succ)`. (Drops the head child's
/// leaf positions; the tail's chain is the suffix of the parent's.)
pub(crate) proof fn lemma_links_drop_first<L: NodeLayout>(
    arena: Seq<L::Node>,
    id: nat,
    seps: Seq<nat>,
    kids: Seq<Tree>,
    succ: nat,
)
    requires
        leaf_links_to::<L>(arena, Tree::Inner { id, seps, kids }, succ),
        kids.len() > 0,
        forall|i: int| 0 <= i < kids.len() ==> #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1,
    ensures
        leaf_links_to::<L>(arena, Tree::Inner { id, seps: seps.drop_first(), kids: kids.drop_first() }, succ),
{
    let df = kids.drop_first();
    let l = crate::bplus_tree::tree_leaf_ids(Tree::Inner { id, seps, kids });
    let tl = crate::bplus_tree::tree_leaf_ids(Tree::Inner { id, seps: seps.drop_first(), kids: df });
    let head = crate::bplus_tree::tree_leaf_ids(kids[0]);
    crate::bplus_tree::lemma_forest_leaf_ids_cons(kids);
    assert(l == head + tl);                 // forest_leaf_ids split
    assert(head.len() >= 1);
    // tl[p] == l[head.len() + p]; the parent chain at head.len()+p gives tl's chain.
    assert forall|p: int| 0 <= p < tl.len() implies
        #[trigger] L::link_view(arena[tl[p] as int]) == (if p + 1 < tl.len() { tl[p + 1] } else { succ }) by {
        let hp = head.len() + p;
        assert(l[hp] == tl[p]);
        assert(L::link_view(arena[l[hp] as int])
            == (if hp + 1 < l.len() { l[hp + 1] } else { succ }));   // parent chain at hp
        if p + 1 < tl.len() {
            assert(l[hp + 1] == tl[p + 1]);
            assert(hp + 1 < l.len());
        } else {
            assert(hp + 1 == l.len());
        }
    }
}

/// Build `forest_links_to(a2, nkids, succ)` for the absorb update from
/// `forest_links_to(a1, kids, succ)` plus the recursion's child-cp chain and the
/// frame (other children's footprints unchanged in a2). Inducts on the kids.
pub(crate) proof fn lemma_build_forest_links<K, L, S, const TRACK: bool>(
    arena1: Ghost<Seq<L::Node>>,
    arena2: Ghost<Seq<L::Node>>,
    cur: Ghost<Tree>,
    ncl: Ghost<Tree>,
    gkids: Ghost<Seq<Tree>>,
    cp: Ghost<int>,
    h: Ghost<nat>,
    succ: Ghost<nat>,
    child_succ: Ghost<nat>,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        cur@ == (Tree::Inner { id: cur@->Inner_id, seps: cur@->Inner_seps, kids: gkids@ }),
        0 <= cp@ < gkids@.len(),
        forest_links_to::<L>(arena1@, gkids@, succ@),
        leaf_links_to::<L>(arena2@, ncl@, child_succ@),
        // first-leaf preservation suffices (chain reads only boundary first-leaves);
        // the full leaf-id sequence may grow under a deep absorb. (Contract fix.)
        crate::bplus_tree::tree_leaf_ids(ncl@)[0] == crate::bplus_tree::tree_leaf_ids(gkids@[cp@])[0],
        child_succ@ == (if cp@ + 1 < gkids@.len() {
            crate::bplus_tree::tree_leaf_ids(gkids@[cp@ + 1])[0]
        } else { succ@ }),
        // a2 agrees with a1 on the forest footprint except cp's child region.
        forall|id: nat| (#[trigger] crate::bplus_tree::forest_ids(gkids@).contains(id))
            && !crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
            ==> arena1@[id as int] == arena2@[id as int],
        forall|i: int| 0 <= i < gkids@.len() ==> #[trigger] crate::bplus_tree::tree_leaf_ids(gkids@[i]).len() >= 1,
        // children footprints pairwise disjoint (so framing is valid).
        forall|i: int, j: int| 0 <= i < j < gkids@.len() ==>
            (#[trigger] crate::bplus_tree::tree_ids(gkids@[i]))
                .disjoint(#[trigger] crate::bplus_tree::tree_ids(gkids@[j])),
    ensures
        forest_links_to::<L>(arena2@, gkids@.update(cp@, ncl@), succ@),
    decreases gkids@.len(),
{
    let a1 = arena1@; let a2 = arena2@;
    let kids = gkids@;
    let nkids = kids.update(cp@, ncl@);
    let df = kids.drop_first();
    // forest_links_to(a1, kids, succ) unfolds: leaf_links_to(a1, kids[0], s0a) &&
    // forest_links_to(a1, df, succ), where s0a is kids[1]'s first leaf or succ.
    let s0 = if kids.len() > 1 { crate::bplus_tree::tree_leaf_ids(kids[1])[0] } else { succ@ };
    // nkids[1] (if any) has the same first leaf as kids[1] (update at cp preserves
    // leaf-ids; for index 1 either 1==cp (then ncl preserves) or 1!=cp (then ==kids[1])).
    assert(nkids.len() == kids.len());
    let ns0 = if nkids.len() > 1 { crate::bplus_tree::tree_leaf_ids(nkids[1])[0] } else { succ@ };
    assert(ns0 == s0) by {
        if kids.len() > 1 {
            if 1 == cp@ {
                assert(nkids[1] == ncl@);
                assert(crate::bplus_tree::tree_leaf_ids(ncl@)[0] == crate::bplus_tree::tree_leaf_ids(kids[cp@])[0]);
            } else {
                assert(nkids[1] == kids[1]);
            }
        }
    }

    // Single induction in lemma_forest_links_update (no per-branch stubs).
    lemma_forest_links_update::<L>(a1, a2, kids, cp@, ncl@, succ@, child_succ@);
}

/// The forest-links analogue of `lemma_forest_binds_update`: from
/// `forest_links_to(a1, kids, succ)`, the recursion's new chain for child `cp`
/// (`leaf_links_to(a2, ncl, child_succ)`), agreement outside `cp`'s footprint,
/// leaf-ids preserved, and pairwise-disjoint children, derive
/// `forest_links_to(a2, kids.update(cp, ncl), succ)`. One induction on `kids`.
pub(crate) proof fn lemma_forest_links_update<L: NodeLayout>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    kids: Seq<Tree>,
    cp: int,
    ncl: Tree,
    succ: nat,
    child_succ: nat,
)
    requires
        forest_links_to::<L>(a1, kids, succ),
        0 <= cp < kids.len(),
        leaf_links_to::<L>(a2, ncl, child_succ),
        // first-leaf preservation only — the chain reads boundary first-leaves;
        // `tree_ids(ncl)` equality is NOT needed (the body frames kids[0] via
        // its own footprint, and the recursion via the agreement clause), so the
        // grown `ncl` footprint is fine. (Subset+freshness contract fix.)
        crate::bplus_tree::tree_leaf_ids(ncl)[0] == crate::bplus_tree::tree_leaf_ids(kids[cp])[0],
        child_succ == (if cp + 1 < kids.len() {
            crate::bplus_tree::tree_leaf_ids(kids[cp + 1])[0]
        } else { succ }),
        forall|i: int| 0 <= i < kids.len() ==> #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1,
        forall|id: nat| (#[trigger] crate::bplus_tree::forest_ids(kids).contains(id))
            && !crate::bplus_tree::tree_ids(kids[cp]).contains(id)
            ==> a1[id as int] == a2[id as int],
        forall|i: int, j: int| 0 <= i < j < kids.len() ==>
            (#[trigger] crate::bplus_tree::tree_ids(kids[i]))
                .disjoint(#[trigger] crate::bplus_tree::tree_ids(kids[j])),
    ensures
        forest_links_to::<L>(a2, kids.update(cp, ncl), succ),
    decreases kids.len(),
{
    let nkids = kids.update(cp, ncl);
    let df = kids.drop_first();
    crate::bplus_tree::lemma_forest_ids_cons(kids);
    // forest_links_to(a1, kids, succ) head/tail (definitional unfold).
    let s0a = if kids.len() > 1 { crate::bplus_tree::tree_leaf_ids(kids[1])[0] } else { succ };
    assert(leaf_links_to::<L>(a1, kids[0], s0a));
    assert(forest_links_to::<L>(a1, df, succ));
    // nkids head successor (s0) equals s0a (leaf-ids preserved at index 1).
    let s0 = if nkids.len() > 1 { crate::bplus_tree::tree_leaf_ids(nkids[1])[0] } else { succ };
    assert(s0 == s0a) by {
        if kids.len() > 1 {
            if 1 == cp { assert(nkids[1] == ncl); } else { assert(nkids[1] == kids[1]); }
        }
    }

    if cp == 0 {
        // head -> ncl, chain to child_succ == s0a; tail df unchanged (framed).
        assert(nkids[0] == ncl);
        assert(child_succ == s0a);
        assert(nkids.drop_first() =~= df);
        // df footprints disjoint from kids[0]==kids[cp]; agreement on forest_ids(df).
        assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(df).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
            // id in some df[m]==kids[m+1]; disjoint from kids[0]==kids[cp].
            crate::bplus_tree::lemma_forest_id_in_some_child(df, id);
            let m = choose|m: int| 0 <= m < df.len() && #[trigger] crate::bplus_tree::tree_ids(df[m]).contains(id);
            assert(df[m] == kids[m + 1]);
            assert(crate::bplus_tree::tree_ids(kids[0]).disjoint(crate::bplus_tree::tree_ids(kids[m + 1])));
            assert(!crate::bplus_tree::tree_ids(kids[cp]).contains(id));
        }
        assert forall|i: int| 0 <= i < df.len() implies
            #[trigger] crate::bplus_tree::tree_leaf_ids(df[i]).len() >= 1 by { assert(df[i] == kids[i + 1]); }
        lemma_forest_links_frame_ids::<L>(a1, a2, df, succ);
    } else {
        // head kids[0] unchanged (disjoint from kids[cp]); tail recurse on df.
        assert(nkids[0] == kids[0]);
        assert(nkids.drop_first() =~= df.update(cp - 1, ncl));
        // kids[0] chain unchanged in a2 (its footprint disjoint from kids[cp]).
        assert forall|id: nat| #![trigger a1[id as int], a2[id as int]] crate::bplus_tree::tree_ids(kids[0]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
            assert(crate::bplus_tree::tree_ids(kids[0]).disjoint(crate::bplus_tree::tree_ids(kids[cp])));
            assert(!crate::bplus_tree::tree_ids(kids[cp]).contains(id));
        }
        lemma_leaf_links_frame::<L>(a1, a2, kids[0], s0a);
        // recurse DIRECTLY on df (strictly smaller) — establish df's preconditions.
        assert(df[cp - 1] == kids[cp]);
        assert forall|i: int| 0 <= i < df.len() implies
            #[trigger] crate::bplus_tree::tree_leaf_ids(df[i]).len() >= 1 by { assert(df[i] == kids[i + 1]); }
        assert(child_succ == (if (cp - 1) + 1 < df.len() {
            crate::bplus_tree::tree_leaf_ids(df[(cp - 1) + 1])[0]
        } else { succ })) by {
            if cp + 1 < kids.len() { assert(df[cp] == kids[cp + 1]); }
        }
        assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(df).contains(id)
            && !crate::bplus_tree::tree_ids(df[cp - 1]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
        }
        assert forall|i: int, j: int| 0 <= i < j < df.len() implies
            (#[trigger] crate::bplus_tree::tree_ids(df[i]))
                .disjoint(#[trigger] crate::bplus_tree::tree_ids(df[j])) by {
            assert(df[i] == kids[i + 1]); assert(df[j] == kids[j + 1]);
        }
        lemma_forest_links_update::<L>(a1, a2, df, cp - 1, ncl, succ, child_succ);
        // assemble: forest_links_to(a2, nkids, succ) = head chain && tail.
        assert(forest_links_to::<L>(a2, df.update(cp - 1, ncl), succ));
    }
}

/// One-step unfold of `forest_links_to` over a non-empty head (the `cons` lemma):
/// `forest_links_to(kids)` iff `leaf_links_to(kids[0], s0) && forest_links_to(df)`
/// where `s0` is `kids[1]`'s first leaf (or `succ`).
/// `forest_links_to` FROM the flat chain condition on the forest's leaf-id
/// sequence. The two are definitionally the same statement written at different
/// granularities; this is the direction the bulk loader needs, since it proves
/// the chain once at the leaf level and every level above inherits it (their
/// `forest_leaf_ids` are all the same sequence).
pub(crate) proof fn lemma_forest_links_from_chain<L: NodeLayout>(
    arena: Seq<L::Node>, kids: Seq<Tree>, succ: nat,
)
    requires
        chain_links_to::<L>(arena, crate::bplus_tree::forest_leaf_ids(kids), succ),
        forall|i: int| 0 <= i < kids.len()
            ==> #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1,
    ensures forest_links_to::<L>(arena, kids, succ),
    decreases kids,
{
    if kids.len() == 0 {
    } else {
        let df = kids.drop_first();
        let all = crate::bplus_tree::forest_leaf_ids(kids);
        let head = crate::bplus_tree::tree_leaf_ids(kids[0]);
        let tl = crate::bplus_tree::forest_leaf_ids(df);
        crate::bplus_tree::lemma_forest_leaf_ids_cons(kids);
        assert(all == head + tl);
        assert forall|i: int| 0 <= i < df.len() implies
            #[trigger] crate::bplus_tree::tree_leaf_ids(df[i]).len() >= 1 by {
            assert(df[i] == kids[i + 1]);
        }

        // Head: `leaf_links_to(kids[0], s0)` is the chain restricted to `head`,
        // whose own tail element must point at `tl[0]` -- and `tl[0]` is child 1's
        // first leaf, which is `s0`.
        let s0 = if kids.len() > 1 {
            crate::bplus_tree::tree_leaf_ids(kids[1])[0]
        } else {
            succ
        };
        if kids.len() > 1 {
            crate::bplus_tree::lemma_forest_leaf_ids_cons(df);
            assert(tl.len() >= 1);
            assert(tl[0] == crate::bplus_tree::tree_leaf_ids(df[0])[0]);
            assert(df[0] == kids[1]);
            assert(s0 == tl[0]);
        } else {
            assert(df.len() == 0);
            assert(tl =~= Seq::<nat>::empty());
        }
        assert forall|p: int| 0 <= p < head.len() implies
            #[trigger] L::link_view(arena[head[p] as int])
                == (if p + 1 < head.len() { head[p + 1] } else { s0 }) by {
            assert(all[p] == head[p]);
            assert(L::link_view(arena[all[p] as int])
                == (if p + 1 < all.len() { all[p + 1] } else { succ }));
            if p + 1 < head.len() {
                assert(all[p + 1] == head[p + 1]);
            } else {
                // p is head's last: the next element of `all` (if any) is tl[0].
                assert(p + 1 == head.len());
                if tl.len() > 0 { assert(all[p + 1] == tl[0]); }
            }
        }
        assert(leaf_links_to::<L>(arena, kids[0], s0));

        // Tail: shift the chain past `head`.
        assert forall|p: int| 0 <= p < tl.len() implies
            #[trigger] L::link_view(arena[tl[p] as int])
                == (if p + 1 < tl.len() { tl[p + 1] } else { succ }) by {
            let hp = head.len() + p;
            assert(all[hp] == tl[p]);
            assert(L::link_view(arena[all[hp] as int])
                == (if hp + 1 < all.len() { all[hp + 1] } else { succ }));
            if p + 1 < tl.len() { assert(all[hp + 1] == tl[p + 1]); }
        }
        lemma_forest_links_from_chain::<L>(arena, df, succ);
    }
}

/// A CONTIGUOUS RUN OF LEAVES assembles into `forest_links_to` from per-index
/// link facts. The bulk loader's leaf level is exactly this shape: `kids[q]` is
/// `Leaf { id: off + q }` and slot `off + q` links to `off + q + 1`, with the last
/// linking to `succ`. `forest_links_to` peels from the left, so the induction
/// walks `off` forward one leaf at a time.
///
/// Without this the loader would have to state its chain invariant in the
/// recursive form, which it cannot: it grows the forest at the RIGHT end, where
/// `forest_links_to`'s head-successor argument changes every iteration.
pub(crate) proof fn lemma_forest_links_leaf_run<L: NodeLayout>(
    arena: Seq<L::Node>, kids: Seq<Tree>, off: nat, succ: nat,
)
    requires
        forall|q: int| 0 <= q < kids.len() ==>
            (#[trigger] kids[q]) is Leaf
                && crate::bplus_tree::tree_root_id(kids[q]) == (off + q) as nat,
        forall|q: int| 0 <= q < kids.len() ==>
            #[trigger] L::link_view(arena[off as int + q])
                == (if q + 1 < kids.len() { (off + q + 1) as nat } else { succ }),
    ensures forest_links_to::<L>(arena, kids, succ),
    decreases kids.len(),
{
    if kids.len() == 0 {
    } else {
        // Head: a leaf's `tree_leaf_ids` is the singleton of its own id, so
        // `leaf_links_to` at `kids[0]` is the single link fact at `off`.
        assert(kids[0] is Leaf);
        assert(crate::bplus_tree::tree_leaf_ids(kids[0]) =~= seq![off]);
        let s0 = if kids.len() > 1 {
            crate::bplus_tree::tree_leaf_ids(kids[1])[0]
        } else {
            succ
        };
        if kids.len() > 1 {
            assert(kids[1] is Leaf);
            assert(crate::bplus_tree::tree_leaf_ids(kids[1]) =~= seq![(off + 1) as nat]);
            assert(s0 == (off + 1) as nat);
        }
        assert(L::link_view(arena[off as int]) == s0);
        assert(leaf_links_to::<L>(arena, kids[0], s0));

        let df = kids.drop_first();
        assert forall|q: int| 0 <= q < df.len() implies
            (#[trigger] df[q]) is Leaf
                && crate::bplus_tree::tree_root_id(df[q]) == ((off + 1) + q) as nat by {
            assert(df[q] == kids[q + 1]);
        }
        assert forall|q: int| 0 <= q < df.len() implies
            #[trigger] L::link_view(arena[(off + 1) as int + q])
                == (if q + 1 < df.len() { ((off + 1) + q + 1) as nat } else { succ }) by {
            assert(L::link_view(arena[off as int + (q + 1)])
                == (if q + 2 < kids.len() { (off + q + 2) as nat } else { succ }));
        }
        lemma_forest_links_leaf_run::<L>(arena, df, (off + 1) as nat, succ);
    }
}

pub(crate) proof fn lemma_forest_links_cons<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>, succ: nat)
    requires kids.len() > 0,
    ensures
        forest_links_to::<L>(arena, kids, succ) == (
            leaf_links_to::<L>(arena, kids[0],
                if kids.len() > 1 { crate::bplus_tree::tree_leaf_ids(kids[1])[0] } else { succ })
            && forest_links_to::<L>(arena, kids.drop_first(), succ)
        ),
{
}

/// Split a forest chain at `m`: `forest_links_to(kids, succ)` decomposes into the
/// left run `forest_links_to(kids[0..m], kids[m]'s first leaf)` and the right run
/// `forest_links_to(kids[m..], succ)`. The left run threads to the right run's
/// head leaf, exactly the boundary the two split halves need (left half links to
/// the right half's first leaf, right half links to `succ`). Induction on `m`.
pub(crate) proof fn lemma_forest_links_split_at<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>, succ: nat, m: int)
    requires
        forest_links_to::<L>(arena, kids, succ),
        0 < m < kids.len(),
        forall|i: int| 0 <= i < kids.len() ==> #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1,
    ensures
        forest_links_to::<L>(arena, kids.subrange(0, m), crate::bplus_tree::tree_leaf_ids(kids[m])[0]),
        forest_links_to::<L>(arena, kids.subrange(m, kids.len() as int), succ),
    decreases m,
{
    let head_succ = crate::bplus_tree::tree_leaf_ids(kids[m])[0];
    lemma_forest_links_cons::<L>(arena, kids, succ);
    let df = kids.drop_first();
    let s0 = if kids.len() > 1 { crate::bplus_tree::tree_leaf_ids(kids[1])[0] } else { succ };
    assert(leaf_links_to::<L>(arena, kids[0], s0));
    assert(forest_links_to::<L>(arena, df, succ));
    assert forall|i: int| 0 <= i < df.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(df[i]).len() >= 1 by { assert(df[i] == kids[i + 1]); }
    if m == 1 {
        // left run is [kids[0]], threading to kids[1]'s first leaf == s0 == head_succ.
        assert(kids.subrange(0, 1) =~= seq![kids[0]]);
        assert(kids[1] == kids[m]);
        assert(s0 == head_succ);
        lemma_forest_links_cons::<L>(arena, kids.subrange(0, 1), head_succ);
        assert(kids.subrange(0, 1).drop_first() =~= Seq::<Tree>::empty());
        // right run kids[1..] == df.
        assert(kids.subrange(m, kids.len() as int) =~= df);
    } else {
        // recurse on df at m-1: gives forest_links_to(df[0..m-1], df[m-1] first) and
        // forest_links_to(df[m-1..], succ). df[m-1] == kids[m].
        assert(df[m - 1] == kids[m]);
        lemma_forest_links_split_at::<L>(arena, df, succ, m - 1);
        // left run kids[0..m] == [kids[0]] ++ df[0..m-1], threading to head_succ.
        assert(kids.subrange(0, m).drop_first() =~= df.subrange(0, m - 1));
        assert(kids.subrange(0, m)[0] == kids[0]);
        // head successor of kids[0..m] is kids[1]'s first leaf == s0 == df[0]'s first.
        lemma_forest_links_cons::<L>(arena, kids.subrange(0, m), head_succ);
        if m > 1 {
            assert(kids.subrange(0, m)[1] == kids[1]);
        }
        // right run kids[m..] == df[m-1..].
        assert(kids.subrange(m, kids.len() as int) =~= df.subrange(m - 1, df.len() as int));
    }
}

/// Both halves of a parent split get their `leaf_links_to` from the combined
/// chain `forest_links_to(a2, ckids, succ)`: split it at `m == imid+1` (the right
/// half's start), then compose each run into a whole-subtree chain. The left half
/// `Inner{lid, lseps, ckids[0..m]}` links to `ckids[m]`'s first leaf (the right
/// half's leftmost leaf); the right half `Inner{rid, rseps, ckids[m..]}` links to
/// `succ`. `lseps`/`rseps` are arbitrary (leaf_links ignores separators).
pub(crate) proof fn lemma_parent_split_half_links<L: NodeLayout>(
    a2: Seq<L::Node>,
    ckids: Seq<Tree>,
    lid: nat,
    rid: nat,
    lseps: Seq<nat>,
    rseps: Seq<nat>,
    succ: nat,
    m: int,
)
    requires
        forest_links_to::<L>(a2, ckids, succ),
        0 < m < ckids.len(),
        forall|i: int| 0 <= i < ckids.len() ==> #[trigger] crate::bplus_tree::tree_leaf_ids(ckids[i]).len() >= 1,
    ensures
        leaf_links_to::<L>(a2, Tree::Inner { id: lid, seps: lseps, kids: ckids.subrange(0, m) },
            crate::bplus_tree::tree_leaf_ids(ckids[m])[0]),
        leaf_links_to::<L>(a2, Tree::Inner { id: rid, seps: rseps, kids: ckids.subrange(m, ckids.len() as int) }, succ),
{
    let lkids = ckids.subrange(0, m);
    let rkids = ckids.subrange(m, ckids.len() as int);
    lemma_forest_links_split_at::<L>(a2, ckids, succ, m);
    // each half's children non-empty (subrange of non-empty children).
    assert forall|i: int| 0 <= i < lkids.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(lkids[i]).len() >= 1 by { assert(lkids[i] == ckids[i]); }
    assert forall|i: int| 0 <= i < rkids.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(rkids[i]).len() >= 1 by { assert(rkids[i] == ckids[m + i]); }
    lemma_forest_links_compose::<L>(a2, lid, lseps, lkids, crate::bplus_tree::tree_leaf_ids(ckids[m])[0]);
    lemma_forest_links_compose::<L>(a2, rid, rseps, rkids, succ);
}

/// The leaf-link analogue of `lemma_forest_links_update`, but for the child-split
/// SPLICE: child `cp` becomes the two halves `ncl, ncr`. The chain re-threads as
/// `… -> ncl -> ncr -> (cp+1's first leaf | succ) -> …`. `ncl` chains to `ncr`'s
/// first leaf, `ncr` chains to `child_succ` (the old child's successor). Siblings
/// are framed from `a1`. One induction on `kids`, peeling the head until `cp`.
pub(crate) proof fn lemma_forest_links_splice<L: NodeLayout>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    kids: Seq<Tree>,
    cp: int,
    ncl: Tree,
    ncr: Tree,
    succ: nat,
    child_succ: nat,
)
    requires
        forest_links_to::<L>(a1, kids, succ),
        0 <= cp < kids.len(),
        // the two halves' chains (in a2): ncl -> ncr's first leaf, ncr -> child_succ.
        crate::bplus_tree::tree_leaf_ids(ncr).len() >= 1,
        leaf_links_to::<L>(a2, ncl, crate::bplus_tree::tree_leaf_ids(ncr)[0]),
        leaf_links_to::<L>(a2, ncr, child_succ),
        // ncl keeps the old child's first leaf (so the boundary into cp is unchanged).
        crate::bplus_tree::tree_leaf_ids(ncl).len() >= 1,
        crate::bplus_tree::tree_leaf_ids(ncl)[0] == crate::bplus_tree::tree_leaf_ids(kids[cp])[0],
        // child_succ is the old child cp's successor first-leaf.
        child_succ == (if cp + 1 < kids.len() {
            crate::bplus_tree::tree_leaf_ids(kids[cp + 1])[0]
        } else { succ }),
        forall|i: int| 0 <= i < kids.len() ==> #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1,
        // a2 agrees with a1 outside cp's footprint (siblings framed).
        forall|id: nat| (#[trigger] crate::bplus_tree::forest_ids(kids).contains(id))
            && !crate::bplus_tree::tree_ids(kids[cp]).contains(id)
            ==> a1[id as int] == a2[id as int],
        forall|i: int, j: int| 0 <= i < j < kids.len() ==>
            (#[trigger] crate::bplus_tree::tree_ids(kids[i]))
                .disjoint(#[trigger] crate::bplus_tree::tree_ids(kids[j])),
    ensures
        forest_links_to::<L>(a2, kids.update(cp, ncl).insert(cp + 1, ncr), succ),
    decreases kids.len(),
{
    let nkids = kids.update(cp, ncl).insert(cp + 1, ncr);
    let df = kids.drop_first();
    crate::bplus_tree::lemma_forest_ids_cons(kids);
    lemma_forest_links_cons::<L>(a1, kids, succ);
    let s0a = if kids.len() > 1 { crate::bplus_tree::tree_leaf_ids(kids[1])[0] } else { succ };
    assert(leaf_links_to::<L>(a1, kids[0], s0a));
    assert(forest_links_to::<L>(a1, df, succ));

    if cp == 0 {
        // nkids == [ncl, ncr] ++ df. Head chains: ncl -> ncr[0], ncr -> child_succ
        // == s0a (the old child 0's successor, == kids[1]'s first leaf or succ).
        assert(nkids[0] == ncl);
        assert(nkids.drop_first()[0] == ncr);
        assert(nkids.drop_first().drop_first() =~= df);
        assert(child_succ == s0a);
        // df's chain is unchanged (framed): its footprints are disjoint from kids[0].
        assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(df).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
            crate::bplus_tree::lemma_forest_id_in_some_child(df, id);
            let m = choose|m: int| 0 <= m < df.len() && #[trigger] crate::bplus_tree::tree_ids(df[m]).contains(id);
            assert(df[m] == kids[m + 1]);
            assert(crate::bplus_tree::tree_ids(kids[0]).disjoint(crate::bplus_tree::tree_ids(kids[m + 1])));
            assert(!crate::bplus_tree::tree_ids(kids[0]).contains(id));
        }
        assert forall|i: int| 0 <= i < df.len() implies
            #[trigger] crate::bplus_tree::tree_leaf_ids(df[i]).len() >= 1 by { assert(df[i] == kids[i + 1]); }
        lemma_forest_links_frame_ids::<L>(a1, a2, df, succ);
        // build forest_links_to(a2, [ncl, ncr] ++ df, succ) via two cons steps.
        let tail1 = nkids.drop_first();           // [ncr] ++ df
        assert(tail1.drop_first() =~= df);
        // forest_links_to(a2, tail1, succ): head ncr -> child_succ == (df[0] first | succ).
        lemma_forest_links_cons::<L>(a2, tail1, succ);
        let s_ncr = if tail1.len() > 1 { crate::bplus_tree::tree_leaf_ids(tail1[1])[0] } else { succ };
        assert(s_ncr == child_succ) by {
            if df.len() > 0 { assert(tail1[1] == df[0]); assert(df[0] == kids[1]); }
        }
        lemma_forest_links_cons::<L>(a2, nkids, succ);
        let s_ncl = if nkids.len() > 1 { crate::bplus_tree::tree_leaf_ids(nkids[1])[0] } else { succ };
        assert(nkids[1] == ncr);
        assert(s_ncl == crate::bplus_tree::tree_leaf_ids(ncr)[0]);
    } else {
        // head kids[0] unchanged (disjoint from kids[cp]); recurse on df at cp-1.
        assert(nkids[0] == kids[0]);
        assert(nkids.drop_first() =~= df.update(cp - 1, ncl).insert(cp - 1 + 1, ncr));
        assert forall|id: nat| #![trigger a1[id as int], a2[id as int]] crate::bplus_tree::tree_ids(kids[0]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
            assert(crate::bplus_tree::tree_ids(kids[0]).disjoint(crate::bplus_tree::tree_ids(kids[cp])));
            assert(!crate::bplus_tree::tree_ids(kids[cp]).contains(id));
        }
        lemma_leaf_links_frame::<L>(a1, a2, kids[0], s0a);
        // df preconditions.
        assert(df[cp - 1] == kids[cp]);
        assert forall|i: int| 0 <= i < df.len() implies
            #[trigger] crate::bplus_tree::tree_leaf_ids(df[i]).len() >= 1 by { assert(df[i] == kids[i + 1]); }
        assert(child_succ == (if (cp - 1) + 1 < df.len() {
            crate::bplus_tree::tree_leaf_ids(df[(cp - 1) + 1])[0]
        } else { succ })) by {
            if cp + 1 < kids.len() { assert(df[cp] == kids[cp + 1]); }
        }
        assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(df).contains(id)
            && !crate::bplus_tree::tree_ids(df[cp - 1]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
        }
        assert forall|i: int, j: int| 0 <= i < j < df.len() implies
            (#[trigger] crate::bplus_tree::tree_ids(df[i]))
                .disjoint(#[trigger] crate::bplus_tree::tree_ids(df[j])) by {
            assert(df[i] == kids[i + 1]); assert(df[j] == kids[j + 1]);
        }
        lemma_forest_links_splice::<L>(a1, a2, df, cp - 1, ncl, ncr, succ, child_succ);
        // assemble head + tail. s0 for nkids == s0a. nkids[1] is kids[1] when cp != 1,
        // or ncl when cp == 1 (and ncl's first leaf == kids[1]'s first leaf == s0a).
        lemma_forest_links_cons::<L>(a2, nkids, succ);
        let s0 = if nkids.len() > 1 { crate::bplus_tree::tree_leaf_ids(nkids[1])[0] } else { succ };
        assert(s0 == s0a) by {
            if kids.len() > 1 {
                if cp == 1 {
                    assert(nkids[1] == ncl);
                    assert(crate::bplus_tree::tree_leaf_ids(ncl)[0] == crate::bplus_tree::tree_leaf_ids(kids[cp])[0]);
                    assert(kids[cp] == kids[1]);
                } else {
                    assert(nkids[1] == kids[1]);
                }
            }
        }
    }
}

/// `forest_links_to` framed across arenas agreeing on `forest_ids`. Inducts.
pub(crate) proof fn lemma_forest_links_frame_ids<L: NodeLayout>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    kids: Seq<Tree>,
    succ: nat,
)
    requires
        forest_links_to::<L>(a1, kids, succ),
        forall|id: nat| (#[trigger] crate::bplus_tree::forest_ids(kids).contains(id))
            ==> a1[id as int] == a2[id as int],
        forall|i: int| 0 <= i < kids.len() ==> #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1,
    ensures
        forest_links_to::<L>(a2, kids, succ),
    decreases kids,
{
    if kids.len() == 0 {
    } else {
        let df = kids.drop_first();
        crate::bplus_tree::lemma_forest_ids_cons(kids);
        let s0 = if kids.len() > 1 { crate::bplus_tree::tree_leaf_ids(kids[1])[0] } else { succ };
        assert(leaf_links_to::<L>(a1, kids[0], s0));
        // tree_ids(kids[0]) ⊆ forest_ids(kids), so the agreement transfers.
        assert forall|id: nat| #![trigger a1[id as int], a2[id as int]] crate::bplus_tree::tree_ids(kids[0]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            crate::bplus_tree::lemma_child_ids_in_forest(kids, 0, id);
        }
        lemma_leaf_links_frame::<L>(a1, a2, kids[0], s0);
        assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(df).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
        }
        assert forall|i: int| 0 <= i < df.len() implies
            #[trigger] crate::bplus_tree::tree_leaf_ids(df[i]).len() >= 1 by { assert(df[i] == kids[i + 1]); }
        lemma_forest_links_frame_ids::<L>(a1, a2, df, succ);
    }
}

/// Sanity spec for the `cp>0` successor (the child_succ is computed the same way
/// for `kids` and its tail `df` at index `cp-1`).
spec fn child_succ_for(kids: Seq<Tree>, cp: int, succ: nat) -> nat {
    if cp + 1 < kids.len() { crate::bplus_tree::tree_leaf_ids(kids[cp + 1])[0] } else { succ }
}

/// Model sub-step of [`reconstruct_absorb`]: the parent's in-order keys gain
/// exactly `key`. Pure `Seq`/`Set` algebra over the `forest_keys` split.
pub(crate) proof fn reconstruct_absorb_model<K, L, S, const TRACK: bool>(
    cur: Ghost<Tree>,
    ncl: Ghost<Tree>,
    gkids: Ghost<Seq<Tree>>,
    cp: Ghost<int>,
    key: K,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        cur@ is Inner,
        cur@->Inner_kids == gkids@,
        0 <= cp@ < gkids@.len(),
        crate::bplus_tree::tree_keys(ncl@).to_set()
            == crate::bplus_tree::tree_keys(gkids@[cp@]).to_set().insert(key.id_nat()),
    ensures
        crate::bplus_tree::tree_keys(Tree::Inner { id: cur@->Inner_id, seps: cur@->Inner_seps, kids: gkids@.update(cp@, ncl@) }).to_set()
            == crate::bplus_tree::tree_keys(cur@).to_set().insert(key.id_nat()),
{
    let kids = gkids@;
    let nkids = kids.update(cp@, ncl@);
    let lefts = kids.subrange(0, cp@);
    let rights = kids.subrange(cp@ + 1, kids.len() as int);
    let lk = crate::bplus_tree::forest_keys(lefts);
    let rk = crate::bplus_tree::forest_keys(rights);
    // forest_keys(nkids) == lk + tree_keys(ncl) + rk; forest_keys(kids) == lk +
    // tree_keys(kids[cp]) + rk (both via the update/split lemmas).
    crate::bplus_tree::lemma_forest_keys_update(kids, cp@, ncl@);
    crate::bplus_tree::lemma_forest_keys_split(kids, cp@);
    crate::bplus_tree::lemma_forest_keys_split(kids, cp@ + 1);
    crate::bplus_tree::lemma_forest_keys_update(kids, cp@, kids[cp@]);
    assert(kids.update(cp@, kids[cp@]) =~= kids);  // identity update
    let nm = crate::bplus_tree::forest_keys(nkids);
    let om = crate::bplus_tree::forest_keys(kids);
    assert(nm == lk + crate::bplus_tree::tree_keys(ncl@) + rk);
    assert(om == lk + crate::bplus_tree::tree_keys(kids[cp@]) + rk);
    // set of a 3-way concat is the union of the three sets; the middle gains key.
    lemma_concat3_set(lk, crate::bplus_tree::tree_keys(ncl@), rk);
    lemma_concat3_set(lk, crate::bplus_tree::tree_keys(kids[cp@]), rk);
    assert(nm.to_set() =~= om.to_set().insert(key.id_nat()));
    assert(crate::bplus_tree::tree_keys(Tree::Inner { id: cur@->Inner_id, seps: cur@->Inner_seps, kids: nkids }) == nm);
    assert(crate::bplus_tree::tree_keys(cur@) == om);
}

/// `(a + b + c).to_set() == a.to_set() ∪ b.to_set() ∪ c.to_set()`. Pure Seq/Set.
pub(crate) proof fn lemma_concat3_set(a: Seq<nat>, b: Seq<nat>, c: Seq<nat>)
    ensures (a + b + c).to_set() == a.to_set().union(b.to_set()).union(c.to_set()),
{
    assert((a + b + c).to_set() =~= a.to_set().union(b.to_set()).union(c.to_set())) by {
        assert forall|k: nat| #[trigger] (a + b + c).to_set().contains(k)
            <==> a.to_set().union(b.to_set()).union(c.to_set()).contains(k) by {
            crate::bplus_tree::lemma_concat_contains(a + b, c, k);
            crate::bplus_tree::lemma_concat_contains(a, b, k);
        }
    }
}

pub(crate) proof fn lemma_leaf_links_project<L: NodeLayout>(
    arena: Seq<L::Node>,
    id: nat,
    seps: Seq<nat>,
    kids: Seq<Tree>,
    succ: nat,
    cp: int,
)
    requires
        leaf_links_to::<L>(arena, Tree::Inner { id, seps, kids }, succ),
        0 <= cp < kids.len(),
        forall|i: int| 0 <= i < kids.len() ==> #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1,
    ensures
        leaf_links_to::<L>(arena, kids[cp],
            if cp + 1 < kids.len() { crate::bplus_tree::tree_leaf_ids(kids[cp + 1])[0] } else { succ }),
{
    let t = Tree::Inner { id, seps, kids };
    let l = crate::bplus_tree::tree_leaf_ids(t);
    assert(l == crate::bplus_tree::forest_leaf_ids(kids));
    let off = crate::bplus_tree::leaf_id_offset(kids, cp);
    let cl = crate::bplus_tree::tree_leaf_ids(kids[cp]);
    let csucc = if cp + 1 < kids.len() { crate::bplus_tree::tree_leaf_ids(kids[cp + 1])[0] } else { succ };
    let fl = crate::bplus_tree::forest_leaf_ids(kids);
    assert(l == fl);
    crate::bplus_tree::lemma_forest_leaf_ids_slice(kids, cp);  // fl[off+q] == cl[q]
    // child cl occupies fl[off .. off+cl.len()]; its chain follows from fl's.
    assert forall|p: int| 0 <= p < cl.len() implies
        #[trigger] L::link_view(arena[cl[p] as int]) == (if p + 1 < cl.len() { cl[p + 1] } else { csucc }) by {
        assert(fl[off + p] == cl[p]);                 // slice at q == p
        // l's chain at off+p.
        assert(L::link_view(arena[l[off + p] as int])
            == (if off + p + 1 < l.len() { l[off + p + 1] } else { succ }));
        if p + 1 < cl.len() {
            assert(fl[off + (p + 1)] == cl[p + 1]);   // slice at q == p+1
            assert(off + (p + 1) == off + p + 1);
        } else if cp + 1 < kids.len() {
            // next child's first leaf == fl[off + cl.len()] == csucc.
            let off2 = crate::bplus_tree::leaf_id_offset(kids, cp + 1);
            let cl2 = crate::bplus_tree::tree_leaf_ids(kids[cp + 1]);
            crate::bplus_tree::lemma_forest_leaf_ids_slice(kids, cp + 1);  // fl[off2+q] == cl2[q]
            crate::bplus_tree::lemma_leaf_id_offset_succ(kids, cp);        // off2 == off + cl.len()
            assert(cl2.len() >= 1);
            // instantiate the slice forall at q==0 in its exact spec-applied shape.
            assert(crate::bplus_tree::forest_leaf_ids(kids)[
                    crate::bplus_tree::leaf_id_offset(kids, cp + 1) as int + 0]
                == crate::bplus_tree::tree_leaf_ids(kids[cp + 1])[0]);
            assert(p + 1 == cl.len());           // this branch: !(p+1<cl.len) && p<cl.len
            // off2 == leaf_id_offset(kids,cp) + tree_leaf_ids(kids[cp]).len() == off + cl.len().
            assert(crate::bplus_tree::leaf_id_offset(kids, cp + 1)
                == crate::bplus_tree::leaf_id_offset(kids, cp)
                    + crate::bplus_tree::tree_leaf_ids(kids[cp]).len());
            assert(off2 == off + cl.len());
            assert(off + p + 1 == off2);
            assert(fl[off2 as int] == cl2[0]);
            assert(off + p + 1 < l.len());
        } else {
            // cp is the last child: off + cl.len() == l.len(), link == succ == csucc.
            crate::bplus_tree::lemma_leaf_id_offset_last(kids, cp);  // off + cl.len() == fl.len()
            assert(off + p + 1 == l.len());
        }
    }
}

/// Extract child `cp`'s `subtree_wf` from the parent `cur`'s. binds via
/// `lemma_inner_binds_child`, `tree_wf` via `lemma_forest_wf_at`, leaf-links via
/// `lemma_leaf_links_project`, disjoint via `lemma_forest_disjoint_at`.
pub(crate) proof fn lemma_inner_child_subtree_wf<K, L, S, const TRACK: bool>(
    arena: Seq<L::Node>,
    cur: Tree,
    h: nat,
    succ: nat,
    cp: int,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        // root-form (weakest) input: this reads only the Inner arm's forest_wf to
        // project a CHILD's wf (always non-root), so is_root is irrelevant.
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena, cur, h, succ, true),
        cur is Inner,
        0 <= cp < cur->Inner_kids.len(),
        h == crate::bplus_tree::tree_height(cur),
    ensures
        ({
            let kids = cur->Inner_kids;
            BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena, kids[cp], (h - 1) as nat,
                if cp + 1 < kids.len() { crate::bplus_tree::tree_leaf_ids(kids[cp + 1])[0] } else { succ },
                false)
        }),
{
    let id = cur->Inner_id;
    let seps = cur->Inner_seps;
    let kids = cur->Inner_kids;
    // tree_wf(cur, h): children wf at h-1, kids.len() == seps.len()+1.
    crate::bplus_tree::lemma_forest_wf_at(kids, (h - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), cp);
    // each child non-empty (tree_wf at h-1).
    assert forall|i: int| 0 <= i < kids.len() implies
        #[trigger] crate::bplus_tree::tree_leaf_ids(kids[i]).len() >= 1 by {
        crate::bplus_tree::lemma_forest_wf_at(kids, (h - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), i);
        crate::bplus_tree::lemma_tree_leaf_ids_nonempty(kids[i], (h - 1) as nat,
            L::leaf_cap_spec(), L::key_cap_spec(), false);
    }
    lemma_inner_binds_child::<L>(arena, id, seps, kids, cp);
    lemma_leaf_links_project::<L>(arena, id, seps, kids, succ, cp);
    crate::bplus_tree::lemma_forest_disjoint_at(kids, cp);
}

/// Frame lemma for `binds` (the dynamic-frames separation). If two arenas agree
/// on every id in `tree_ids(t)` — `t`'s footprint — then `t` binds in one iff it
/// binds in the other. So a mutation confined to ids outside `tree_ids(t)`
/// preserves `binds(_, t)`. This is what lets a split touch one subtree's nodes
/// and frame out every disjoint subtree's binding for free.
pub(crate) proof fn lemma_binds_frame<L: NodeLayout>(a1: Seq<L::Node>, a2: Seq<L::Node>, t: Tree)
    requires
        binds::<L>(a1, t),
        a1.len() <= a2.len(),
        forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::tree_ids(t).contains(id) ==> a1[id as int] == a2[id as int],
    ensures
        binds::<L>(a2, t),
    decreases t,
{
    match t {
        Tree::Leaf { id, keys } => {
            // tree_ids(Leaf) == {id}; a1[id]==a2[id], so the leaf arm transfers.
            assert(crate::bplus_tree::tree_ids(t).contains(id));
            assert(a1[id as int] == a2[id as int]);
        }
        Tree::Inner { id, seps, kids } => {
            // id and every child's footprint are in tree_ids(t); recurse on kids.
            assert(crate::bplus_tree::tree_ids(t).contains(id));
            assert(a1[id as int] == a2[id as int]);
            lemma_forest_binds_frame::<L>(a1, a2, kids, t);
        }
    }
}

/// Forest companion of [`lemma_binds_frame`]. `parent` carries the `tree_ids`
/// containment: every `forest_ids(kids)` id is in `tree_ids(parent)`, so the
/// agreement hypothesis lifts to each child.
pub(crate) proof fn lemma_forest_binds_frame<L: NodeLayout>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    kids: Seq<Tree>,
    parent: Tree,
)
    requires
        forest_binds_l::<L>(a1, kids),
        a1.len() <= a2.len(),
        parent is Inner,
        parent->Inner_kids == kids,
        forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::tree_ids(parent).contains(id)
            ==> a1[id as int] == a2[id as int],
    ensures
        forest_binds_l::<L>(a2, kids),
    decreases kids,
{
    if kids.len() == 0 {
    } else {
        let df = kids.drop_first();
        // tree_ids(parent) ⊇ forest_ids(kids) = tree_ids(kids[0]) ∪ forest_ids(df).
        crate::bplus_tree::lemma_forest_ids_cons(kids);
        // head child binds under a2 (its footprint ⊆ parent's, agreement lifts).
        assert forall|id: nat| #![trigger a1[id as int], a2[id as int]] crate::bplus_tree::tree_ids(kids[0]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            // tree_ids(kids[0]) ⊆ forest_ids(kids) ⊆ tree_ids(parent).
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
            assert(crate::bplus_tree::tree_ids(parent).contains(id));
        }
        lemma_binds_frame::<L>(a1, a2, kids[0]);
        // tail: build a synthetic parent over df to carry containment.
        let dparent = Tree::Inner {
            id: parent->Inner_id,
            seps: parent->Inner_seps,
            kids: df,
        };
        assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::tree_ids(dparent).contains(id)
            implies a1[id as int] == a2[id as int] by {
            // tree_ids(dparent) = {pid} ∪ forest_ids(df) ⊆ {pid} ∪ forest_ids(kids)
            //                   ⊆ tree_ids(parent).
            if id == parent->Inner_id {
                assert(crate::bplus_tree::tree_ids(parent).contains(id));
            } else {
                assert(crate::bplus_tree::forest_ids(df).contains(id));
                assert(crate::bplus_tree::forest_ids(kids).contains(id));
                assert(crate::bplus_tree::tree_ids(parent).contains(id));
            }
        }
        lemma_forest_binds_frame::<L>(a1, a2, df, dparent);
    }
}

/// Frame lemma for `leaf_links_to`. `leaf_links_to` reads `link_view` only at
/// `tree_leaf_ids(t)` slots, all of which are in `tree_ids(t)`
/// (`lemma_leaf_id_in_tree_ids`); so two arenas agreeing on `tree_ids(t)` agree
/// on the chain. A mutation outside `t`'s region preserves its leaf links.
pub(crate) proof fn lemma_leaf_links_frame<L: NodeLayout>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    t: Tree,
    succ: nat,
)
    requires
        leaf_links_to::<L>(a1, t, succ),
        forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::tree_ids(t).contains(id) ==> a1[id as int] == a2[id as int],
    ensures
        leaf_links_to::<L>(a2, t, succ),
{
    let lids = crate::bplus_tree::tree_leaf_ids(t);
    assert forall|p: int| 0 <= p < lids.len() implies
        #[trigger] L::link_view(a2[lids[p] as int]) == (if p + 1 < lids.len() { lids[p + 1] } else { succ }) by {
        crate::bplus_tree::lemma_leaf_id_in_tree_ids(t, p);  // lids[p] in tree_ids(t)
        assert(a1[lids[p] as int] == a2[lids[p] as int]);
        // the leaf_links_to(a1) instance at p gives the rhs.
        assert(L::link_view(a1[lids[p] as int]) == (if p + 1 < lids.len() { lids[p + 1] } else { succ }));
    }
}

/// Combined frame for `subtree_wf` (modulo the height/occupancy, which are
/// arena-independent ghost facts). If `a2` agrees with `a1` on `tree_ids(t)`,
/// then `binds` and `leaf_links_to` transfer; `tree_wf` and `tree_disjoint` are
/// pure ghost (no arena), so the whole `subtree_wf` carries. The frame step for
/// a sibling subtree untouched by a mutation in another subtree's region.
pub(crate) proof fn lemma_subtree_wf_frame<K, L, S, const TRACK: bool>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    t: Tree,
    h: nat,
    succ: nat,
    is_root: bool,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(a1, t, h, succ, is_root),
        a1.len() <= a2.len(),
        forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::tree_ids(t).contains(id) ==> a1[id as int] == a2[id as int],
    ensures
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(a2, t, h, succ, is_root),
{
    lemma_binds_frame::<L>(a1, a2, t);
    lemma_leaf_links_frame::<L>(a1, a2, t, succ);
    // tree_wf and tree_disjoint are arena-independent, carried by the requires.
}

/// `subtree_wf` framed across a single-slot `update` whose slot is outside the
/// subtree's footprint: `subtree_wf(arena, t, …)` + `id_slot ∉ tree_ids(t)` ⟹
/// `subtree_wf(arena.update(id_slot, v), t, …)`. The agreement (slot `id_slot`
/// is the only change, and it's outside `t`) is discharged once here, so callers
/// don't fight the `id != id_slot` quantifier reasoning.
pub(crate) proof fn lemma_subtree_wf_frame_update<K, L, S, const TRACK: bool>(
    arena: Seq<L::Node>,
    t: Tree,
    id_slot: nat,
    v: L::Node,
    h: nat,
    succ: nat,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena, t, h, succ, false),
        id_slot < arena.len(),
        !crate::bplus_tree::tree_ids(t).contains(id_slot),
    ensures
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(arena.update(id_slot as int, v), t, h, succ, false),
{
    let a2 = arena.update(id_slot as int, v);
    assert(arena.len() <= a2.len());
    assert forall|id: nat| #![trigger arena[id as int]] #![trigger a2[id as int]] crate::bplus_tree::tree_ids(t).contains(id)
        implies arena[id as int] == a2[id as int] by {
        // id < arena.len() (binds in-range), and id != id_slot (id ∈ tree_ids(t),
        // id_slot ∉), so the update at id_slot doesn't touch slot id.
        lemma_tree_id_in_range::<L>(arena, t, id);
        if id == id_slot {
            assert(crate::bplus_tree::tree_ids(t).contains(id_slot));  // contradiction
        }
        assert(id != id_slot);
        assert(a2[id as int] == arena[id as int]);  // update at id_slot != id
    }
    lemma_subtree_wf_frame::<K, L, S, TRACK>(arena, a2, t, h, succ, false);
}

/// Rebuild `forest_binds_l` after replacing child `cp` by a new subtree `nc` in
/// the *new* arena `a2`: the absorb step's reconstruction. `a2` binds `nc` (the
/// recursive result) and agrees with the old arena `a1` on every *other* child's
/// footprint (the recursion grew the arena and touched only `nc`'s region; the
/// siblings' ids are disjoint from `nc`'s, by `tree_disjoint` on the parent).
pub(crate) proof fn lemma_forest_binds_update<L: NodeLayout>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    kids: Seq<Tree>,
    cp: int,
    nc: Tree,
)
    requires
        forest_binds_l::<L>(a1, kids),
        a1.len() <= a2.len(),
        0 <= cp < kids.len(),
        binds::<L>(a2, nc),
        crate::bplus_tree::forest_disjoint(kids),
        // pairwise disjointness of the children (the parent's tree_disjoint clause).
        (forall|i: int, j: int| 0 <= i < j < kids.len() ==>
            (#[trigger] crate::bplus_tree::tree_ids(kids[i]))
                .disjoint(#[trigger] crate::bplus_tree::tree_ids(kids[j]))),
        // NOTE: no `tree_ids(nc) == tree_ids(kids[cp])` here — `nc` may have GROWN
        // (deep-absorb of a split). binds(a2,nc) is supplied directly and the
        // siblings are framed by the agreement clause below; footprint equality
        // was never used by the body, only threaded to the recursion. Dropping it
        // is part of the subset+freshness contract fix (see `insert_rec` (F0)).
        // a2 agrees with a1 on the forest footprint EXCEPT the replaced child's
        // region (the recursion mutated only inside `tree_ids(kids[cp])`; the
        // fresh tail slots it allocated are outside `forest_ids(kids)` entirely).
        forall|id: nat| (#[trigger] crate::bplus_tree::forest_ids(kids).contains(id))
            && !crate::bplus_tree::tree_ids(kids[cp]).contains(id)
            ==> a1[id as int] == a2[id as int],
    ensures
        forest_binds_l::<L>(a2, kids.update(cp, nc)),
    decreases kids,
{
    crate::bplus_tree::lemma_forest_disjoint_cons(kids);
    crate::bplus_tree::lemma_forest_ids_cons(kids);
    let u = kids.update(cp, nc);
    let df = kids.drop_first();
    // tree_ids(kids[0]) disjoint from forest_ids(df): df[m]==kids[m+1], pairwise (0,m+1).
    assert forall|id: nat| crate::bplus_tree::tree_ids(kids[0]).contains(id)
        implies !(#[trigger] crate::bplus_tree::forest_ids(df).contains(id)) by {
        if crate::bplus_tree::forest_ids(df).contains(id) {
            crate::bplus_tree::lemma_forest_id_in_some_child(df, id);
            let m = choose|m: int| 0 <= m < df.len() && #[trigger] crate::bplus_tree::tree_ids(df[m]).contains(id);
            assert(df[m] == kids[m + 1]);
            assert(crate::bplus_tree::tree_ids(kids[0]).disjoint(crate::bplus_tree::tree_ids(kids[m + 1])));
        }
    }
    if cp == 0 {
        assert(u[0] == nc);
        assert(u.drop_first() =~= df);
        assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(df).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
            assert(!crate::bplus_tree::tree_ids(kids[0]).contains(id));
        }
        lemma_forest_binds_frame_tail::<L>(a1, a2, df);
    } else {
        assert(df[cp - 1] == kids[cp]);
        assert(u[0] == kids[0]);
        assert(u.drop_first() =~= df.update(cp - 1, nc));
        // head kids[0] binds in a2: disjoint from kids[cp] (0 < cp), so framed.
        assert forall|id: nat| #![trigger a1[id as int], a2[id as int]] crate::bplus_tree::tree_ids(kids[0]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
            assert(crate::bplus_tree::tree_ids(kids[0]).disjoint(crate::bplus_tree::tree_ids(kids[cp])));
            assert(!crate::bplus_tree::tree_ids(kids[cp]).contains(id));
        }
        lemma_binds_frame::<L>(a1, a2, kids[0]);
        // recurse on the tail.
        assert forall|i: int, j: int| 0 <= i < j < df.len() implies
            (#[trigger] crate::bplus_tree::tree_ids(df[i]))
                .disjoint(#[trigger] crate::bplus_tree::tree_ids(df[j])) by {
            assert(df[i] == kids[i + 1]); assert(df[j] == kids[j + 1]);
        }
        assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(df).contains(id)
            && !crate::bplus_tree::tree_ids(df[cp - 1]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
        }
        lemma_forest_binds_update::<L>(a1, a2, df, cp - 1, nc);
    }
}

/// Helper: every subtree in a forest binds in `a2` if it binds in `a1` and `a2`
/// agrees with `a1` on the whole forest footprint `forest_ids(kids)`. (Frame the
/// entire forest.) Single-variable agreement over `forest_ids` (the union of the
/// children's footprints) so the quantifier has a clean trigger.
pub(crate) proof fn lemma_forest_binds_frame_tail<L: NodeLayout>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    kids: Seq<Tree>,
)
    requires
        forest_binds_l::<L>(a1, kids),
        a1.len() <= a2.len(),
        forall|id: nat| (#[trigger] crate::bplus_tree::forest_ids(kids).contains(id))
            ==> a1[id as int] == a2[id as int],
    ensures
        forest_binds_l::<L>(a2, kids),
    decreases kids,
{
    if kids.len() == 0 {
    } else {
        let df = kids.drop_first();
        crate::bplus_tree::lemma_forest_ids_cons(kids);
        // kids[0] binds in a2: its footprint ⊆ forest_ids(kids), so agreement holds.
        assert forall|id: nat| #![trigger a1[id as int], a2[id as int]] crate::bplus_tree::tree_ids(kids[0]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
        }
        lemma_binds_frame::<L>(a1, a2, kids[0]);
        assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::forest_ids(df).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
        }
        lemma_forest_binds_frame_tail::<L>(a1, a2, df);
    }
}

/// `forest_binds_l(a, [x, y])` from `binds(a, x)` and `binds(a, y)` (the two-
/// element base case, with the recursive unfold made explicit for the SMT solver).
pub(crate) proof fn lemma_forest_binds_pair<L: NodeLayout>(a: Seq<L::Node>, x: Tree, y: Tree)
    requires binds::<L>(a, x), binds::<L>(a, y),
    ensures forest_binds_l::<L>(a, seq![x, y]),
{
    let s = seq![x, y];
    assert(s[0] == x);
    assert(s.drop_first() =~= seq![y]);
    assert(seq![y][0] == y);
    assert(seq![y].drop_first() =~= Seq::<Tree>::empty());
    assert(forest_binds_l::<L>(a, Seq::<Tree>::empty()));
    assert(forest_binds_l::<L>(a, seq![y]));
}

/// `forest_binds_l` distributes over concatenation: if both `x` and `y` bind in
/// `a`, so does `x + y`. (The child-split-absorb splice builds the new children
/// as `left ++ [ncl, ncr] ++ right`; this composes the per-piece binds.)
/// `forest_binds_l` survives a `push` onto the END of the arena: every existing
/// child reads only slots that were already there, so the appended slot cannot
/// disturb any of them. The bulk loader's framing step — it pushes one node per
/// iteration and must carry the whole previously built level across it.
pub(crate) proof fn lemma_forest_binds_frame_push<L: NodeLayout>(
    a1: Seq<L::Node>, a2: Seq<L::Node>, kids: Seq<Tree>, node: L::Node,
)
    requires
        forest_binds_l::<L>(a1, kids),
        a2 == a1.push(node),
    ensures forest_binds_l::<L>(a2, kids),
    decreases kids,
{
    if kids.len() == 0 {
    } else {
        // `push` agrees with the original on every old index, which is all
        // `binds` reads (its ids are `< a1.len()` by `binds` itself).
        assert(a1.len() <= a2.len());
        assert forall|id: nat| #![trigger a1[id as int]] #![trigger a2[id as int]] crate::bplus_tree::tree_ids(kids[0]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            lemma_binds_ids_in_range::<L>(a1, kids[0], id);
            assert(a2[id as int] == a1.push(node)[id as int]);
        }
        lemma_binds_frame::<L>(a1, a2, kids[0]);
        lemma_forest_binds_frame_push::<L>(a1, a2, kids.drop_first(), node);
    }
}

/// `binds` only mentions arena ids that are IN RANGE: every id in `tree_ids(t)`
/// is `< arena.len()`. Read straight off `binds`'s own per-node `id < arena.len()`
/// clause, recursively.
pub(crate) proof fn lemma_binds_ids_in_range<L: NodeLayout>(
    arena: Seq<L::Node>, t: Tree, id: nat,
)
    requires binds::<L>(arena, t), crate::bplus_tree::tree_ids(t).contains(id),
    ensures id < arena.len(),
    decreases t,
{
    match t {
        Tree::Leaf { id: lid, .. } => {
            assert(crate::bplus_tree::tree_ids(t) == set![lid]);
        }
        Tree::Inner { id: nid, kids, .. } => {
            if id == nid {
            } else {
                assert(crate::bplus_tree::forest_ids(kids).contains(id));
                crate::bplus_tree::lemma_forest_id_in_some_child(kids, id);
                let m = choose|m: int| 0 <= m < kids.len()
                    && (#[trigger] crate::bplus_tree::tree_ids(kids[m])).contains(id);
                lemma_forest_binds_at::<L>(arena, kids, m);
                lemma_binds_ids_in_range::<L>(arena, kids[m], id);
            }
        }
    }
}

/// `forest_binds_l` extends by one at the RIGHT end. The bulk loader's shape:
/// it appends each freshly built subtree, and `forest_binds_l` peels from the
/// left, so the extension goes through `concat` with a singleton.
pub(crate) proof fn lemma_forest_binds_push<L: NodeLayout>(a: Seq<L::Node>, kids: Seq<Tree>, x: Tree)
    requires forest_binds_l::<L>(a, kids), binds::<L>(a, x),
    ensures forest_binds_l::<L>(a, kids.push(x)),
{
    let one = seq![x];
    assert(one.len() == 1);
    assert(one[0] == x);
    assert(one.drop_first() =~= Seq::<Tree>::empty());
    assert(forest_binds_l::<L>(a, Seq::<Tree>::empty()));
    assert(forest_binds_l::<L>(a, one)) by {
        reveal_with_fuel(forest_binds_l, 2);
    }
    lemma_forest_binds_concat::<L>(a, kids, one);
    assert(kids.push(x) =~= kids + one);
}

pub(crate) proof fn lemma_forest_binds_concat<L: NodeLayout>(a: Seq<L::Node>, x: Seq<Tree>, y: Seq<Tree>)
    requires forest_binds_l::<L>(a, x), forest_binds_l::<L>(a, y),
    ensures forest_binds_l::<L>(a, x + y),
    decreases x,
{
    if x.len() == 0 {
        assert(x + y =~= y);
    } else {
        let xdf = x.drop_first();
        // forest_binds_l(a, x) ⟹ binds(a, x[0]) && forest_binds_l(a, xdf).
        assert((x + y)[0] == x[0]);
        assert((x + y).drop_first() =~= xdf + y);
        lemma_forest_binds_concat::<L>(a, xdf, y);
    }
}

/// Per-key projection from `binds` at a leaf subtree, without needing `tree_wf`:
/// if `cur == Leaf{id, keys}` binds in `arena` and `0 <= i < keys.len()`, the
/// arena node's `i`-th word projects to `keys[i]`. The recursion's leaf scan
/// uses this (it has `subtree_wf`'s `binds`, not a root-form `tree_wf`).
pub(crate) proof fn lemma_leaf_binds_key_at<K, L, S, const TRACK: bool>(
    arena: Seq<L::Node>,
    cur: Tree,
    id: nat,
    i: int,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        binds::<L>(arena, cur),
        cur == (Tree::Leaf { id, keys: crate::bplus_tree::tree_keys(cur) }),
        0 <= i < crate::bplus_tree::tree_keys(cur).len(),
    ensures
        (#[trigger] L::keys_view(arena[id as int])[i]).as_nat() == crate::bplus_tree::tree_keys(cur)[i],
{
    match cur {
        Tree::Leaf { id: cid, keys } => {
            // binds leaf arm: forall j. keys_view(arena[cid])[j].as_nat() == keys[j].
            assert(cid == id);
            assert(crate::bplus_tree::tree_keys(cur) == keys);
        }
        Tree::Inner { .. } => { assert(false); }
    }
}

/// The model of a leaf-root tree is strictly sorted (`tree_wf`'s leaf arm).
pub(crate) proof fn lemma_leaf_sorted<K, L, S, const TRACK: bool>(t: &BPlusTreeSet<K, L, S, TRACK>)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        t.wf(),
        L::is_leaf_spec(t.arena()[t.root.as_nat() as int]),
    ensures
        crate::bplus_tree::strictly_sorted(crate::bplus_tree::tree_keys(t.tree@)),
{
    let root_id = t.root.as_nat() as int;
    match t.tree@ {
        Tree::Leaf { id, keys } => {
            assert(crate::bplus_tree::tree_keys(t.tree@) == keys);
        }
        Tree::Inner { id, .. } => {
            assert(id == root_id as nat);
            assert(!L::is_leaf_spec(t.arena()[root_id]));
            assert(false);
        }
    }
}

/// Leaf-root facts from `wf` + the leaf guard: the arena root node is
/// node-well-formed and its key count equals the ghost model length. Both
/// follow from `binds`'s leaf arm (count == keys.len()) and `tree_wf`'s leaf
/// arm (keys.len() <= leaf_cap ⟹ node_wf).
pub(crate) proof fn lemma_leaf_facts<K, L, S, const TRACK: bool>(t: &BPlusTreeSet<K, L, S, TRACK>)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        t.wf(),
        L::is_leaf_spec(t.arena()[t.root.as_nat() as int]),
    ensures
        L::node_wf(t.arena()[t.root.as_nat() as int]),
        crate::bplus_tree::tree_keys(t.tree@).len()
            == L::count_spec(t.arena()[t.root.as_nat() as int]),
{
    let root_id = t.root.as_nat() as int;
    let node = t.arena()[root_id];
    match t.tree@ {
        Tree::Leaf { id, keys } => {
            // binds(arena, Leaf): id == root (root-id agreement), is_leaf,
            // count == keys.len(); tree_keys(Leaf) == keys.
            assert(crate::bplus_tree::tree_keys(t.tree@) == keys);
            assert(L::count_spec(node) == keys.len());  // binds leaf arm
            // tree_wf(Leaf): keys.len() <= leaf_cap; node_wf_iff turns that into node_wf.
            L::lemma_node_wf_iff(node);
        }
        Tree::Inner { id, .. } => {
            // binds(Inner) requires !is_leaf(arena[id]) with id == root, but the
            // guard says arena[root] is a leaf — contradiction.
            assert(id == root_id as nat);
            assert(!L::is_leaf_spec(node));
            assert(false);
        }
    }
}

/// `binds` at a leaf root, instantiated at one key index: the arena node's
/// `i`-th key word projects (`as_nat`) to the ghost key `gkeys[i]`. Pulls the
/// leaf arm of `binds` out so `contains`' loop can use it per element.
pub(crate) proof fn lemma_leaf_binds_key<K, L, S, const TRACK: bool>(
    t: &BPlusTreeSet<K, L, S, TRACK>,
    i: int,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        t.wf(),
        L::is_leaf_spec(t.arena()[t.root.as_nat() as int]),
        0 <= i < L::count_spec(t.arena()[t.root.as_nat() as int]),
    ensures
        L::keys_view(t.arena()[t.root.as_nat() as int])[i].as_nat()
            == crate::bplus_tree::tree_keys(t.tree@)[i],
{
    // The ghost root is a Leaf (root-id agreement + the arena node is a leaf +
    // binds is consistent), so binds' leaf arm gives the per-key projection and
    // tree_keys(Leaf) is exactly its key sequence.
    let root_id = t.root.as_nat() as int;
    let node = t.arena()[root_id];
    match t.tree@ {
        Tree::Leaf { id, keys } => {
            // binds leaf arm: forall j. keys_view(arena[id])[j].as_nat() == keys[j];
            // and tree_keys(Leaf) == keys, so the i-th word projects to keys[i].
            assert(id == root_id as nat);
            assert(crate::bplus_tree::tree_keys(t.tree@) == keys);
            // the leaf-arm forall instantiated at i gives the conclusion.
        }
        Tree::Inner { id, .. } => {
            assert(id == root_id as nat);
            assert(!L::is_leaf_spec(node));
            assert(false);
        }
    }
}

impl<K, L, S, const TRACK: bool> BPlusTreeSet<K, L, S, TRACK>
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
{

    /// (M6) THE ARENA NEVER OVERFLOWS. From `wf` alone (plus the static fact that
    /// the key type steals a bit, true for every tree key), the live arena has
    /// enough headroom for another full insert: `arena.len() + tree_height + 3 <
    /// ArenaIdx::max_nat()` — exactly `insert_general`'s capacity precondition.
    ///
    /// Proof chain (see [[bplus-m6-arena-capacity-plan]]): wf gives
    /// `arena.len() == node_count` and `model_bounded`; a set has `nkeys <=
    /// id_bound` (`lemma_sorted_bounded_len`); the structural bound gives
    /// `L_min*(node_count-1) <= 2*nkeys <= 2*id_bound == max_nat`; with `L_min >= 7`
    /// and `height <= node_count`, `arena.len() + height + 3 <= 2*node_count + 3
    /// <= 2*(max_nat/7 + 1) + 3 < max_nat`.
    pub(crate) proof fn lemma_arena_never_overflows(&self)
        requires self.wf(), K::is_bit_stealing(),
        ensures
            self.arena().len() + crate::bplus_tree::tree_height(self.tree@) + 3
                < <L::ArenaIdx as IndexLike>::max_nat(),
    {
        let mx = <L::ArenaIdx as IndexLike>::max_nat();
        let lmin = (L::leaf_cap_spec() + 1) / 2;
        let nc = crate::bplus_tree::node_count(self.tree@);
        let nkeys = self.model().len();
        let idb = K::id_bound();

        // id_bound == max_nat/2: id steals a bit (id_bound*2 == Index::max_nat),
        // and Word == K::Index has the same range as ArenaIdx.
        K::lemma_id_bound_word_relation();                 // idb*2 == K::Index::max_nat
        L::lemma_word_arena_same_width();                  // Word::max_nat == ArenaIdx::max_nat
        assert(<L::Word as IndexLike>::max_nat() == <K::Index as IndexLike>::max_nat());
        assert(idb * 2 == mx);
        assert(idb == mx / 2) by (nonlinear_arith) requires idb * 2 == mx;
        L::lemma_capacity_headroom(idb);                   // lmin >= 7, mx >= 16, 2*idb==mx

        // nkeys <= id_bound (strictly-sorted bounded model = a set in [0, id_bound)).
        crate::bplus_tree::lemma_tree_wf_sorted(self.tree@,
            crate::bplus_tree::tree_height(self.tree@), L::leaf_cap_spec(), L::key_cap_spec(), true);
        crate::bplus_tree::lemma_sorted_bounded_len(self.model(), idb);
        assert(nkeys <= idb);

        // structural: lmin*(nc-1) <= 2*nkeys <= 2*idb == mx.
        crate::bplus_tree::lemma_node_count_bound(self.tree@,
            crate::bplus_tree::tree_height(self.tree@), L::leaf_cap_spec(), L::key_cap_spec());
        assert(lmin * (nc - 1) <= 2 * nkeys);
        assert(2 * nkeys <= 2 * idb) by (nonlinear_arith) requires nkeys <= idb;
        assert(lmin * (nc - 1) <= mx);

        // lmin >= 7 ⟹ 7*(nc-1) <= lmin*(nc-1) <= mx, so nc-1 <= mx/7, nc <= mx/7 + 1.
        assert(7 * (nc - 1) <= lmin * (nc - 1)) by (nonlinear_arith) requires lmin >= 7, nc >= 1;
        crate::bplus_tree::lemma_node_count_pos(self.tree@);   // nc >= 1
        assert(7 * (nc - 1) <= mx);
        assert(nc - 1 <= mx / 7) by (nonlinear_arith) requires 7 * (nc - 1) <= mx;

        // arena.len() == nc (wf), height <= nc.
        crate::bplus_tree::lemma_height_le_node_count(self.tree@);
        assert(self.arena().len() == nc);
        // 2*nc + 3 <= 2*(mx/7 + 1) + 3 == 2*mx/7 + 5 < mx  (since mx >= 16).
        assert(self.arena().len() + crate::bplus_tree::tree_height(self.tree@) + 3 <= 2 * nc + 3);
        assert(2 * nc + 3 < mx) by (nonlinear_arith)
            requires nc - 1 <= mx / 7, mx >= 16, nc >= 1;
    }

    /// Leaf-root fast path (Phase 8.2: NOT public — its erased leaf-root
    /// precondition would be a foot-gun for ordinary callers). Currently
    /// unwired: the total `insert` handles every tree shape through the
    /// recursion; this verified single-leaf path is retained as the building
    /// block for production's O(1) rightmost-append fast path (a Phase 9 /
    /// performance follow-up if the insert_random bench gate ever needs it).
    #[allow(dead_code)]
    fn insert_root_leaf(&mut self, key: K) -> (added: bool)
        requires
            old(self).wf(),
            L::is_leaf_spec(old(self).arena()[old(self).root.as_nat() as int]),
            old(self).nkeys_spec() < usize::MAX,
            // Arena capacity is discharged internally (M6): the root is a leaf, so
            // tree_height == 0 and lemma_arena_never_overflows gives arena.len()+3 <
            // max_nat, hence the +2 this path needs. Only the static bit-stealing
            // fact is required of the caller.
            K::is_bit_stealing(),
        ensures
            final(self).wf(),
            added == !old(self).model().contains(key.id_nat()),
            final(self).model().to_set() == old(self).model().to_set().insert(key.id_nat()),
    {
        // Runtime guard (overflow): a verified caller proves `nkeys < usize::MAX`;
        // an unverified one is trapped before the `nkeys + 1` count would wrap.
        // (The arena cannot overflow — that is discharged internally — so this
        // key count is the only client-facing capacity bound on insert.)
        crate::guard::check_precondition(
            self.nkeys < usize::MAX,
            "BPlusTreeSet::insert: key count would overflow usize",
        );
        // recover the arena-capacity fact from wf (root leaf ⟹ height 0).
        proof { self.lemma_arena_never_overflows(); }
        let ghost root_id = self.root.as_nat() as int;
        let ghost gkeys = crate::bplus_tree::tree_keys(self.tree@);
        proof { lemma_leaf_facts::<K, L, S, TRACK>(self); }

        let mut leaf = self.nodes.get_index(self.root);
        let n = L::count(&leaf);
        let kw: L::Word = key.to_index();

        // pos = find_ge(keys, target), through `S`: the verified in-node search,
        // whose postcondition is exactly the find-position characterization the
        // sorted-insert lemma needs. Production: `S::find_ge` at bplus.rs:661.
        proof {
            assert(L::node_wf(leaf));
            assert(gkeys.len() == n as nat);
            lemma_tree_wf_sorted_seps_view::<L>(self.arena(), self.tree@,
                self.root.as_nat(), leaf);
        }
        let pos = self.leaf_find_ge(&leaf, kw);
        proof {
            assert(pos as nat <= gkeys.len());
            assert forall|j: int| 0 <= j < pos implies gkeys[j] < key.id_nat() by {
                lemma_leaf_binds_key::<K, L, S, TRACK>(self, j);
            }
            assert forall|j: int| pos <= j < n implies key.id_nat() <= gkeys[j] by {
                lemma_leaf_binds_key::<K, L, S, TRACK>(self, j);
            }
        }

        // Decide presence at the boundary: keys[pos] >= target already, so the
        // target is present iff keys[pos] <= target too, and only there.
        let mut present = false;
        if pos < n {
            let ki: L::Word = L::key(&leaf, pos);
            let le = ki.le(kw);
            proof {
                <L::Word as IndexLike>::lemma_order_is_as_nat(ki, kw);
                assert(L::count_spec(self.arena()[root_id]) == n as nat);
                lemma_leaf_binds_key::<K, L, S, TRACK>(self, pos as int);
                assert(ki == L::keys_view(leaf)[pos as int]);
                assert(ki.as_nat() == gkeys[pos as int]);
            }
            if le {
                present = true;  // gkeys[pos] == target
                proof { assert(gkeys[pos as int] == key.id_nat()); }
            }
        }

        if present {
            proof {
                assert(gkeys.contains(key.id_nat()));
                assert(self.model().to_set() =~= old(self).model().to_set().insert(key.id_nat()));
            }
            return false;
        }

        // key is absent. The find-position characterization for sorted-insert:
        //   [0..pos) < k  (loop invariant),
        //   [pos..n)  > k  (boundary gkeys[pos] >= k and absence ⟹ >, lifted by
        //                   sortedness).
        proof {
            lemma_leaf_sorted::<K, L, S, TRACK>(self);  // gkeys strictly sorted
            assert(forall|j: int| 0 <= j < pos ==> gkeys[j] < key.id_nat());
            // boundary: if pos < n then gkeys[pos] >= k; with absence, > k.
            // sortedness lifts gkeys[pos] <= gkeys[j], so k < gkeys[j] for j >= pos.
            assert forall|j: int| pos <= j < n implies key.id_nat() < gkeys[j] by {
                // boundary: k <= gkeys[pos] (find_ge), and gkeys[pos] != k
                // (!present), so k < gkeys[pos] <= gkeys[j] by sortedness.
                if pos < j { assert(gkeys[pos as int] < gkeys[j]); }
            }
            assert(!gkeys.contains(key.id_nat()));
        }

        // Capture the OLD leaf's per-key binding (keys_view projects to gkeys)
        // before mutating — needed to rebuild binds for the new ghost leaf.
        let ghost old_kview = L::keys_view(leaf);
        proof {
            L::lemma_keys_view_len(leaf);  // old_kview.len() == count == n == gkeys.len()
            assert forall|j: int| 0 <= j < gkeys.len() implies old_kview[j].as_nat() == #[trigger] gkeys[j] by {
                lemma_leaf_binds_key::<K, L, S, TRACK>(self, j);
                assert(L::keys_view(self.arena()[root_id])[j] == old_kview[j]);
            }
        }
        // The old single-leaf tree's link is NIL (leaf_links_ok at the lone
        // leaf), and leaf_insert_at preserves the link, so the new leaf's link
        // is still NIL — which is exactly what the new single-leaf chain needs.
        proof {
            let lids = crate::bplus_tree::tree_leaf_ids(self.tree@);
            assert(lids =~= seq![root_id as nat]);  // old tree is Leaf{root_id, ..}
            assert(lids.len() == 1 && lids[0] == root_id as nat);
            // leaf_links_ok at p==0 (trigger on lids[0]): last leaf links NIL.
            assert(L::link_view(self.arena()[lids[0] as int]) == nil_link::<L>());
            assert(self.arena()[lids[0] as int] == self.arena()[root_id]);
            assert(L::link_view(self.arena()[root_id]) == nil_link::<L>());
            assert(L::link_view(leaf) == nil_link::<L>());  // leaf == arena[root_id]
        }

        let leaf_cap = L::leaf_cap();
        if n >= leaf_cap {
            // -- full root leaf: split + grow a new root (height 0 -> 1) -------
            return self.insert_split_root(key, kw, pos, leaf, Ghost(old_kview));
        }

        // key absent and there is room: shift-insert into the leaf, write back.
        L::leaf_insert_at(&mut leaf, pos, kw);
        proof {
            assert(L::count_spec(leaf) == n as nat + 1);
            assert(L::keys_view(leaf) == old_kview.insert(pos as int, kw));
        }
        self.nodes.set_index(self.root, leaf);
        self.nkeys = self.nkeys + 1;

        // Update the ghost tree to the root leaf with `key` inserted at `pos`.
        let ghost new_keys = gkeys.insert(pos as int, key.id_nat());
        self.tree = Ghost(Tree::Leaf { id: root_id as nat, keys: new_keys });

        proof {
            // binds(new_arena, Leaf{root_id, new_keys}): leaf arm, per-key. The
            // new node's keys_view is old_kview.insert(pos, kw); new_keys is
            // gkeys.insert(pos, key.id_nat()); old_kview projects to gkeys and
            // kw.as_nat() == key.id_nat(), so the insert shifts agree index-wise.
            assert(self.arena()[root_id] == leaf);
            assert(L::is_leaf_spec(self.arena()[root_id]));
            assert(L::count_spec(self.arena()[root_id]) == new_keys.len());
            let kvi = L::keys_view(leaf);
            assert(kvi == old_kview.insert(pos as int, kw));   // leaf_insert_at post
            assert(new_keys == gkeys.insert(pos as int, key.id_nat()));
            assert(old_kview.len() == gkeys.len());            // old binding count match
            assert(0 <= pos <= old_kview.len());
            assert(0 <= pos <= gkeys.len());
            assert forall|i: int| 0 <= i < new_keys.len() implies
                (#[trigger] kvi[i]).as_nat() == new_keys[i] by {
                // Seq::insert index identities (auto for both kvi and new_keys).
                if i < pos {
                    assert(kvi[i] == old_kview[i]);
                    assert(new_keys[i] == gkeys[i]);
                    assert(old_kview[i].as_nat() == gkeys[i]);
                } else if i == pos {
                    assert(kvi[i] == kw);
                    assert(new_keys[i] == key.id_nat());
                } else {
                    assert(kvi[i] == old_kview[i - 1]);
                    assert(new_keys[i] == gkeys[i - 1]);
                    assert(old_kview[i - 1].as_nat() == gkeys[i - 1]);
                }
            }
            assert(binds::<L>(self.arena(), self.tree@));

            // leaf_links_ok(new tree): single leaf [root_id], link still NIL.
            assert(crate::bplus_tree::tree_leaf_ids(self.tree@) =~= seq![root_id as nat]);
            assert(L::link_view(leaf) == nil_link::<L>());                   // preserved above
            assert(self.arena()[root_id] == leaf);
            assert(leaf_links_ok::<L>(self.arena(), self.tree@));

            // tree_wf(Leaf{.., new_keys}): h==0, len<=cap (n+1<=leaf_cap), sorted.
            crate::bplus_tree::lemma_sorted_insert(gkeys, key.id_nat(), pos as int);
            assert(crate::bplus_tree::tree_height(self.tree@) == 0);
            assert(crate::bplus_tree::tree_wf(
                self.tree@,
                0,
                L::leaf_cap_spec(),
                L::key_cap_spec(),
                true,
            ));

            // model() == new_keys; set == old ∪ {k}; nkeys cached.
            assert(self.model() == new_keys);
            assert(new_keys.to_set() =~= old(self).model().to_set().insert(key.id_nat()));
            assert(self.nkeys as nat == self.model().len());
            // model_bounded: new_keys == gkeys.insert(pos, key.id_nat()); gkeys
            // (== old model) is bounded by old wf, key.id_nat() < id_bound.
            key.lemma_id_nat_bounded();
            assert(model_bounded::<K>(gkeys));  // old(self).wf() clause (gkeys == old model)
            lemma_model_bounded_insert::<K>(gkeys, pos as int, key.id_nat());
            assert(model_bounded::<K>(self.model()));
        }
        true
    }

    /// **The append fast path** — production `insert`'s first block
    /// (`containers/src/bplus.rs:625`). Appends `key` to the rightmost leaf and
    /// returns `true` when all three of production's conditions hold: the leaf is
    /// non-empty, has room, and `key` is strictly greater than its last key.
    /// Returns `false` having mutated NOTHING, so the caller falls through to the
    /// general descent.
    ///
    /// Cost: two arena reads (the cached leaf) and one write. No descent, no
    /// separator comparisons — which is what makes ascending insertion O(1) per key
    /// rather than O(log n), production's `last_leaf` trick.
    ///
    /// Soundness rests on two facts, both already proved:
    /// - `key > last key of the rightmost leaf` implies `key > EVERY key in the
    ///   tree`, because the model is `tree_keys`, which ends with the rightmost
    ///   leaf's keys (`lemma_last_leaf_binds`'s split) and is strictly sorted.
    ///   That is exactly `lemma_append_last_wf`'s ordering precondition.
    /// - the rightmost leaf's *id* is unchanged by the append
    ///   (`lemma_append_last_wf`), so `last_leaf_ok` survives with no cache write.
    fn fast_append(&mut self, key: K, kw: L::Word) -> (did: bool)
        requires
            old(self).wf(),
            old(self).nkeys_spec() < usize::MAX,
            kw.as_nat() == key.id_nat(),
        ensures
            final(self).wf(),
            // taken: the key was strictly above every existing key, so it is
            // genuinely new and lands at the end of the model.
            did ==> final(self).model() == old(self).model().push(key.id_nat()),
            did ==> !old(self).model().contains(key.id_nat()),
            // declined: nothing was touched at all (the caller's `old(self)` facts
            // all still hold of `self`).
            !did ==> *final(self) == *old(self),
    {
        let ll = self.last_leaf;
        proof {
            lemma_last_leaf_binds::<K, L, S, TRACK>(self);
            L::lemma_arena_capacity();
        }
        let leaf = self.nodes.get_index(ll);
        let n = L::count(&leaf);
        let leaf_cap = L::leaf_cap();
        let ghost lkeys = crate::bplus_tree::last_leaf_keys(self.tree@);
        proof {
            L::lemma_keys_view_len(leaf);
            assert(leaf_word_keys::<L>(self.arena(), ll.as_nat()) == lkeys);
            assert(n as nat == lkeys.len());
        }
        if n == 0 || n >= leaf_cap {
            return false;
        }
        // `key > leaf's last key`. Reading it needs `node_wf`, which
        // `lemma_last_leaf_binds` supplied.
        let last_key: L::Word = L::key(&leaf, n - 1);
        let gt = last_key.lt(kw);
        proof {
            <L::Word as IndexLike>::lemma_order_is_as_nat(last_key, kw);
            assert(last_key == L::keys_view(leaf)[n - 1]);
            assert(last_key.as_nat() == lkeys[n - 1]);
        }
        if !gt {
            return false;
        }

        // All three conditions met. `key` exceeds the rightmost leaf's last key,
        // hence every key in the tree: the model ends with those keys and is
        // strictly sorted, so its greatest element is `lkeys[n - 1]`.
        proof {
            let model = self.model();
            let pre = model.subrange(0, model.len() - lkeys.len() as int);
            assert(model == pre + lkeys);
            crate::bplus_tree::lemma_tree_wf_sorted(
                self.tree@, crate::bplus_tree::tree_height(self.tree@),
                L::leaf_cap_spec(), L::key_cap_spec(), true);
            assert(crate::bplus_tree::strictly_sorted(model));
            assert(model[model.len() - 1] == lkeys[n - 1]);
            assert forall|i: int| 0 <= i < model.len() implies #[trigger] model[i] < key.id_nat() by {
                // every element is <= the last (strict sortedness), which is < key.
                if i < model.len() - 1 {
                    assert(model[i] < model[model.len() - 1]);
                }
            }
            assert(!model.contains(key.id_nat()));
        }

        let ghost old_arena = self.arena();
        let ghost old_tree = self.tree@;
        let mut nleaf = leaf;
        L::leaf_insert_at(&mut nleaf, n, kw);
        self.nodes.set_index(ll, nleaf);
        self.nkeys = self.nkeys + 1;
        self.tree = Ghost(crate::bplus_tree::tree_append_last(old_tree, key.id_nat()));
        proof {
            let lid = ll.as_nat();
            let h = crate::bplus_tree::tree_height(old_tree);
            assert(self.arena() == old_arena.update(lid as int, nleaf));
            // the arena delta: exactly slot `lid`, holding the same leaf grown by
            // one key at the end, with its link untouched (leaf_insert_at's post).
            L::lemma_keys_view_len(nleaf);
            assert(L::keys_view(nleaf) == L::keys_view(leaf).insert(n as int, kw));
            assert(leaf_word_keys::<L>(self.arena(), lid)
                == leaf_word_keys::<L>(old_arena, lid).push(key.id_nat())) by {
                let w1 = leaf_word_keys::<L>(old_arena, lid);
                let w2 = leaf_word_keys::<L>(self.arena(), lid);
                assert(w2.len() == w1.len() + 1);
                assert forall|i: int| #![trigger w2[i]] 0 <= i < w2.len() implies w2[i] == w1.push(key.id_nat())[i] by {
                    // Seq::insert at the END is a push: index i < n reads the old
                    // slot, i == n reads kw.
                    if i < n as int {
                        assert(L::keys_view(nleaf)[i] == L::keys_view(leaf)[i]);
                    } else {
                        assert(L::keys_view(nleaf)[i] == kw);
                    }
                }
                assert(w2 =~= w1.push(key.id_nat()));
            }
            assert(crate::bplus_tree::last_leaf_id(old_tree) == lid);

            // the ghost move (assigned above, in exec position) and its full
            // consequence set.
            crate::bplus_tree::lemma_append_last_wf(
                old_tree, h, L::leaf_cap_spec(), L::key_cap_spec(), true, key.id_nat());
            lemma_binds_append_last::<L>(
                old_arena, self.arena(), old_tree, h, nil_link::<L>(), true, key.id_nat());

            // re-establish each `wf` clause. Height is preserved (append_last_wf
            // states wf at the SAME h), so `tree_state_wf`'s `tree_height` instance
            // matches via lemma_tree_wf_height.
            crate::bplus_tree::lemma_tree_wf_height(
                self.tree@, h, L::leaf_cap_spec(), L::key_cap_spec(), true);
            let okeys = crate::bplus_tree::tree_keys(old_tree);
            assert(self.model() == okeys.push(key.id_nat()));
            assert(self.nkeys as nat == self.model().len());
            key.lemma_id_nat_bounded();
            // `push` is `insert` at the end.
            assert(okeys.push(key.id_nat()) =~= okeys.insert(okeys.len() as int, key.id_nat()));
            lemma_model_bounded_insert::<K>(okeys, okeys.len() as int, key.id_nat());
            // arena length and node count are both unchanged (update, not push).
            assert(self.arena().len() == old_arena.len());
            // `last_leaf` needs NO write: the same node is still rightmost.
            assert(self.last_leaf.as_nat() == crate::bplus_tree::last_leaf_id(self.tree@));
            // Phase 7 archive: `set_index` leaves the snapshot stack alone and the
            // archives are untouched fields, so the (opaque) agreement transfers.
            assert(self.nodes.snapshots_view() == old(self).nodes.snapshots_view());
        }
        true
    }

    /// General multi-level insert (M4c): descend to the target leaf, insert, and
    /// propagate splits up via `insert_rec`; grow a new root if the root itself
    /// splits. Unlike [`insert`] (M4b, leaf-root only), this handles trees of any
    /// height. Now fully proven: the closure (`wf` preserved) + the model
    /// transition (`model' == model ∪ {key}`, never dropping/inventing a key) +
    /// the `added == !contains` characterization. The recursion `insert_rec`
    /// supplies the root's new subtree(s); the `Some` arm grows a fresh root over
    /// the two halves (the M4b new-root move, generalized from leaves to subtrees).
    /// Insert `key` — TOTAL on any wf tree (production `insert` name/shape;
    /// Phase 8.2 renamed the internal `insert_general`). Returns whether the
    /// key was newly added. Arena capacity is discharged internally (M6);
    /// the only caller obligations are the key-count headroom and the static
    /// bit-stealing fact.
    /// Total insert (total-API plan phase 3).
    pub fn try_insert(&mut self, key: K) -> (r: Result<bool, crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Ok(added) ==> added == !old(self).model().contains(key.id_nat())
                && final(self).model().to_set() == old(self).model().to_set().insert(key.id_nat()),
            r is Err ==> final(self).model() == old(self).model(),
    {
        if !K::bit_stealing() {
            return Err(crate::error::ContainerError::UnsupportedKey);
        }
        if !(self.nkeys < usize::MAX) {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        Ok(self.insert(key))
    }

    /// Total bulk load: the ascending-distinct requirement becomes an O(n)
    /// check refusing as `NotSorted` — the cost argument is n against the
    /// build's n log n.
    pub fn try_from_sorted(keys: &[K]) -> (r: Result<Self, crate::error::ContainerError>)
        ensures
            r matches Ok(t) ==> t.wf() && t.model().len() == keys@.len(),
    {
        if !K::bit_stealing() {
            return Err(crate::error::ContainerError::UnsupportedKey);
        }
        if !(keys.len() < usize::MAX) {
            return Err(crate::error::ContainerError::CapacityExhausted);
        }
        if keys.len() > 1 {
            let mut i: usize = 1;
            while i < keys.len()
                invariant
                    1 <= i <= keys@.len(),
                    keys@.len() < usize::MAX,
                    forall|a: int, b: int| 0 <= a < b < i
                        ==> (#[trigger] keys@[a]).id_nat() < (#[trigger] keys@[b]).id_nat(),
                decreases keys@.len() - i,
            {
                if !(keys[i - 1].to_usize() < keys[i].to_usize()) {
                    return Err(crate::error::ContainerError::NotSorted);
                }
                proof {
                    assert forall|a: int, b: int| 0 <= a < b < i + 1
                        implies (#[trigger] keys@[a]).id_nat() < (#[trigger] keys@[b]).id_nat() by {
                        if b == i as int && a < i - 1 {
                            assert(keys@[a].id_nat() < keys@[i - 1].id_nat());
                        }
                    }
                }
                i += 1;
            }
        }
        Ok(Self::from_sorted(keys))
    }

    pub fn insert(&mut self, key: K) -> (added: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            added == !old(self).model().contains(key.id_nat()),
            final(self).model().to_set() == old(self).model().to_set().insert(key.id_nat()),
    {
        // Total-with-documented-panic: the static key-type fact and the nkeys
        // ceiling become refuse branches; ensures bind returning paths only.
        if !K::bit_stealing() {
            crate::guard::refuse("BPlusTreeSet::insert: key type does not steal a bit");
        }
        if !(self.nkeys < usize::MAX) {
            crate::guard::refuse("BPlusTreeSet::insert: key count at usize ceiling");
        }
        // Runtime guard (overflow): a verified caller proves `nkeys < usize::MAX`;
        // an unverified one is trapped before the `nkeys + 1` count would wrap.
        // (The arena cannot overflow — discharged internally — so this key count
        // is the only client-facing capacity bound on insert.)
        crate::guard::check_precondition(
            self.nkeys < usize::MAX,
            "BPlusTreeSet::insert: key count would overflow usize",
        );
        let kw: L::Word = key.to_index();

        // ---- FAST PATH: append to the rightmost leaf (production bplus.rs:625).
        // The common case for id-keyed indexes, where keys arrive ascending. If
        // `key` extends the rightmost leaf and that leaf has room, one slot write
        // finishes the insert — no descent, no comparisons above the leaf, O(1)
        // instead of O(log n). This is what makes ascending insertion flat in `n`.
        //
        // `last_leaf_ok` (a `wf` clause) is what lets the field be trusted without
        // a runtime check; `lemma_append_last_wf` + `lemma_binds_append_last`
        // discharge the model and the arena, and the SAME leaf stays rightmost, so
        // the cache needs no update.
        let ghost entry_model = self.model();
        if self.fast_append(key, kw) {
            proof {
                assert(self.model() == entry_model.push(key.id_nat()));
                lemma_push_to_set(entry_model, key.id_nat());
            }
            return true;
        }
        // fast path declined: `self` is untouched, so everything below still speaks
        // of the entry state (the `ensures` frame carries the field equalities).

        // recover the arena-capacity fact the descent/splits need, from wf.
        proof { self.lemma_arena_never_overflows(); }
        let root = self.root;
        let ghost h = crate::bplus_tree::tree_height(self.tree@);
        let ghost old_model = self.model();
        proof {
            // the whole tree is wf as ROOT; insert_rec consumes the root form.
            assert(Self::subtree_wf(self.arena(), self.tree@, h, nil_link::<L>(), true));
            assert(crate::bplus_tree::tree_root_id(self.tree@) == root.as_nat());
            // old model strictly sorted (tree_keys of a wf tree) — for the nkeys
            // length bookkeeping via set cardinality in both arms below.
            crate::bplus_tree::lemma_tree_wf_sorted(self.tree@, h, L::leaf_cap_spec(), L::key_cap_spec(), true);
            assert(crate::bplus_tree::strictly_sorted(old_model));
        }
        let ghost cur_call = self.tree@;
        let (added, split, nl, nr) =
            self.insert_rec(root, key, kw, self.tree, Ghost(h), Ghost(nil_link::<L>()), Ghost(true));
        // (M6) recursion delta against insert_general's own old(self): nothing
        // mutated self between entry and the call, so the recursion's old-state
        // arena/tree == old(self)'s here.
        let ghost arena_after_rec = self.arena();
        proof {
            assert(cur_call == old(self).tree@);
        }
        match split {
            None => {
                // absorb at the root: insert_rec re-established subtree_wf at is_root.
                self.tree = nl;
                proof {
                    // nl is wf as root at the same height (None ensures, is_root=true).
                    assert(Self::subtree_wf(self.arena(), nl@, h, nil_link::<L>(), true));
                    assert(crate::bplus_tree::tree_root_id(nl@) == root.as_nat());
                    // tree_height(nl) == h: nl is wf at height h, and tree_wf pins height.
                    crate::bplus_tree::lemma_tree_wf_height(nl@, h, L::leaf_cap_spec(), L::key_cap_spec(), true);
                }
                if added {
                    self.nkeys = self.nkeys + 1;
                }
                proof {
                    assert(self.model().to_set() =~= old_model.to_set().insert(key.id_nat()));
                    assert(added == !old_model.contains(key.id_nat()));
                    // nkeys bookkeeping via set cardinality: model' and old_model
                    // are both strictly sorted, so len == |set|; the set grew by
                    // 0 (key present) or 1 (absent), matching the `added` increment.
                    assert(self.tree@ == nl@);
                    crate::bplus_tree::lemma_tree_wf_sorted(nl@, h, L::leaf_cap_spec(), L::key_cap_spec(), true);
                    assert(crate::bplus_tree::strictly_sorted(self.model()));
                    crate::bplus_tree::lemma_strictly_sorted_len_eq_set(self.model());
                    crate::bplus_tree::lemma_strictly_sorted_len_eq_set(old_model);
                    if old_model.contains(key.id_nat()) {
                        assert(old_model.to_set().insert(key.id_nat()) =~= old_model.to_set());
                    }
                    assert(old_model.to_set().contains(key.id_nat()) == old_model.contains(key.id_nat()));
                    assert(self.nkeys as nat == self.model().len());
                    // model_bounded: model'.to_set() == old ∪ {key.id_nat()}, old
                    // bounded (old wf), key.id_nat() < id_bound.
                    key.lemma_id_nat_bounded();
                    lemma_model_bounded_set::<K>(self.model(), old_model, key.id_nat());

                    // (M6) arena.len() == node_count(tree@): old wf gave
                    // old.arena.len() == node_count(cur@); the recursion's None delta
                    // gives self.arena.len() + node_count(cur@) == old.len() + node_count(nl@);
                    // tree@ == nl@.
                    assert(self.tree@ == nl@);
                    assert(self.arena().len() == crate::bplus_tree::node_count(self.tree@));
                }
                // A split BELOW the root may have moved the rightmost leaf
                // (`insert_rec` preserves the leftmost, not the rightmost — see
                // `rightmost_leaf_of`), so recompute the cache. SLOW path only:
                // the fast path returns long before reaching here.
                self.last_leaf = self.rightmost_leaf_of(root, Ghost(self.tree@));
                added
            }
            Some((sep, rid)) => {
                // root split: build a new internal root over the two halves nl, nr.
                let new_root = L::new_internal2(sep, root, rid);
                let new_root_idx = self.nodes.len();
                let ghost arena_pre = self.arena();
                proof {
                    // nothing touched self.nodes between the recursion and here
                    // (new_internal2 is pure, len() is a read), so the arena the M6
                    // delta speaks of (arena_after_rec) is still current.
                    assert(arena_pre == arena_after_rec);
                }
                self.nodes.push(new_root);
                self.root = new_root_idx;
                let ghost new_tree = Tree::Inner {
                    id: new_root_idx.as_nat(),
                    seps: seq![sep.as_nat()],
                    kids: seq![nl@, nr@],
                };
                self.tree = Ghost(new_tree);
                if added {
                    self.nkeys = self.nkeys + 1;
                }
                proof {
                    // nl/nr footprints are real slots in arena_pre (binds in-range),
                    // so all < arena_pre.len() == new_root_idx (the fresh push slot).
                    // arena_pre == the post-recursion arena (new_internal2 / len()
                    // don't mutate self.nodes), where the Some ensures bind nl/nr.
                    assert(new_root_idx.as_nat() == arena_pre.len());
                    assert(binds::<L>(arena_pre, nl@));
                    assert(binds::<L>(arena_pre, nr@));
                    assert forall|id: nat| crate::bplus_tree::tree_ids(nl@).contains(id)
                        implies id < arena_pre.len() by {
                        lemma_tree_id_in_range::<L>(arena_pre, nl@, id);
                    }
                    assert forall|id: nat| crate::bplus_tree::tree_ids(nr@).contains(id)
                        implies id < arena_pre.len() by {
                        lemma_tree_id_in_range::<L>(arena_pre, nr@, id);
                    }
                    assert(self.arena() =~= arena_pre.push(new_root));
                    // nr's leaf-id sequence is non-empty (wf at h non-root ⟹ >= 1 leaf).
                    L::lemma_arena_capacity();
                    crate::bplus_tree::lemma_tree_leaf_ids_nonempty(nr@, h, L::leaf_cap_spec(), L::key_cap_spec(), false);
                    lemma_insert_new_root::<K, L, S, TRACK>(
                        Ghost(arena_pre), Ghost(self.arena()), Ghost(old_model),
                        Ghost(nl@), Ghost(nr@), sep, Ghost(root.as_nat()), rid,
                        Ghost(new_root_idx.as_nat()), Ghost(new_root), Ghost(h), key);
                    assert(self.tree@ == new_tree);
                    assert(self.model().to_set() =~= old_model.to_set().insert(key.id_nat()));
                    assert(added == !old_model.contains(key.id_nat()));
                    // nkeys: lemma_insert_new_root's length ensures gives model'.len()
                    // == old_model.len() + (key present ? 0 : 1), matching `added`.
                    assert(old_model.to_set().contains(key.id_nat()) == old_model.contains(key.id_nat()));
                    assert(self.nkeys as nat == self.model().len());
                    // model_bounded: same as the None arm (set == old ∪ {key}).
                    key.lemma_id_nat_bounded();
                    lemma_model_bounded_set::<K>(self.model(), old_model, key.id_nat());

                    // (M6) arena.len() == node_count(tree@): root split. old wf gave
                    // old.len() == node_count(cur@); recursion's Some delta gives
                    // arena_pre.len() + node_count(cur@) == old.len() + nc(nl) + nc(nr),
                    // so arena_pre.len() == nc(nl)+nc(nr). The new root push (+1) and
                    // new_tree == Inner{_, [sep], [nl, nr]} (node_count 1 + nc(nl) + nc(nr)).
                    assert(self.arena() =~= arena_pre.push(new_root));
                    assert(self.tree@ == new_tree);
                    assert(self.tree@->Inner_kids =~= seq![nl@, nr@]);
                    // node_count(Inner) == 1 + forest_node_count(kids); unfold the 2 kids.
                    assert(crate::bplus_tree::node_count(self.tree@)
                        == 1 + crate::bplus_tree::forest_node_count(seq![nl@, nr@]));
                    assert(seq![nl@, nr@][0] == nl@);
                    assert(seq![nl@, nr@].len() == 2);
                    assert(seq![nl@, nr@].drop_first() =~= seq![nr@]);
                    assert(seq![nr@][0] == nr@);
                    assert(seq![nr@].drop_first() =~= Seq::<Tree>::empty());
                    assert(crate::bplus_tree::forest_node_count(Seq::<Tree>::empty()) == 0);
                    assert(crate::bplus_tree::forest_node_count(seq![nr@])
                        == crate::bplus_tree::node_count(nr@));
                    assert(crate::bplus_tree::forest_node_count(seq![nl@, nr@])
                        == crate::bplus_tree::node_count(nl@) + crate::bplus_tree::node_count(nr@));
                    // chain: old wf => old.len() == node_count(old.tree@). recursion's
                    // Some delta (at the call boundary): arena_after_rec.len() +
                    // node_count(cur_call) == old.len() + nc(nl)+nc(nr), and cur_call
                    // == old.tree@, so arena_after_rec.len() == nc(nl)+nc(nr).
                    assert(old(self).arena().len() == crate::bplus_tree::node_count(old(self).tree@));
                    assert(cur_call == old(self).tree@);
                    assert(arena_after_rec.len()
                        == crate::bplus_tree::node_count(nl@) + crate::bplus_tree::node_count(nr@));
                    // new_internal2 / len() did not mutate the arena: arena_pre == arena_after_rec.
                    assert(arena_pre == arena_after_rec);
                    assert(self.arena().len() == arena_pre.len() + 1);
                    assert(self.arena().len() == crate::bplus_tree::node_count(self.tree@));
                }
                // The root split moved the rightmost leaf into `nr`; recompute from
                // the NEW root (slow path only, as in the `None` arm).
                self.last_leaf = self.rightmost_leaf_of(new_root_idx, Ghost(self.tree@));
                added
            }
        }
    }

    /// The full-root-leaf split branch of [`insert`]. The root is a leaf filled
    /// to `leaf_cap`, `key` is absent, and `pos` is its sorted insert position.
    /// Splits the combined sequence at `split_mid` into a left and right leaf,
    /// allocates the right leaf and a new internal root, and rewires the ghost
    /// tree to the resulting height-1 B+tree. The leaf-link chain becomes
    /// `[root_id, right_id]` (left links to right, right inherits the old NIL).
    ///
    /// Preconditions capture exactly the state `insert` has established at the
    /// branch: leaf root, full, key absent at the found position, link NIL, and
    /// `old_kview` projecting to the model keys.
    fn insert_split_root(
        &mut self,
        key: K,
        kw: L::Word,
        pos: usize,
        leaf: L::Node,
        old_kview: Ghost<Seq<L::Word>>,
    ) -> (added: bool)
        requires
            old(self).wf(),
            L::is_leaf_spec(old(self).arena()[old(self).root.as_nat() as int]),
            leaf == old(self).arena()[old(self).root.as_nat() as int],
            kw.as_nat() == key.id_nat(),
            L::count_spec(leaf) == L::leaf_cap_spec(),
            pos <= L::leaf_cap_spec(),
            old(self).nkeys_spec() < usize::MAX,
            old(self).arena().len() + 2 < <L::ArenaIdx as IndexLike>::max_nat(),
            // pos is the find position over the model keys, key absent.
            old_kview@ == L::keys_view(leaf),
            old_kview@.len() == L::leaf_cap_spec(),
            (forall|j: int| 0 <= j < old_kview@.len() ==>
                #[trigger] old_kview@[j].as_nat()
                    == crate::bplus_tree::tree_keys(old(self).tree@)[j]),
            crate::bplus_tree::tree_keys(old(self).tree@).len() == L::leaf_cap_spec(),
            (forall|j: int| 0 <= j < pos ==>
                crate::bplus_tree::tree_keys(old(self).tree@)[j] < key.id_nat()),
            (forall|j: int| pos <= j < L::leaf_cap_spec() ==>
                key.id_nat() < crate::bplus_tree::tree_keys(old(self).tree@)[j]),
            !crate::bplus_tree::tree_keys(old(self).tree@).contains(key.id_nat()),
            L::link_view(leaf) == nil_link::<L>(),
        ensures
            final(self).wf(),
            added == !old(self).model().contains(key.id_nat()),
            final(self).model().to_set() == old(self).model().to_set().insert(key.id_nat()),
    {
        let ghost root_id = self.root.as_nat();
        let ghost gkeys = crate::bplus_tree::tree_keys(self.tree@);
        let ghost combined = old_kview@.insert(pos as int, kw);

        // Split the full leaf. left keeps low half, right the high half.
        let (mut left, right) = L::leaf_split_at(&leaf, pos, kw);
        let ghost mid = L::split_mid_spec();
        proof {
            // combined facts: length, the split halves, the separator. The
            // split postcondition speaks of keys_view(leaf).insert(pos, kw);
            // old_kview@ == keys_view(leaf), so that equals `combined`.
            assert(old_kview@ == L::keys_view(leaf));
            assert(combined == L::keys_view(leaf).insert(pos as int, kw));
            assert(combined.len() == L::leaf_cap_spec() + 1);
            assert(L::keys_view(left) == combined.subrange(0, mid as int));
            assert(L::keys_view(right) == combined.subrange(mid as int, combined.len() as int));
            assert(L::link_view(right) == nil_link::<L>());  // inherited old NIL
            // mid bounds: 1 <= mid <= cap (cap >= 1), so split is non-degenerate.
            L::lemma_arena_capacity();  // 1 <= leaf_cap, 1 <= key_cap
            L::lemma_split_mid();       // mid == (leaf_cap+1)/2, 1 <= mid <= leaf_cap
            assert(mid == (L::leaf_cap_spec() + 1) / 2);
            assert(L::leaf_cap_spec() >= 1);
            assert(1 <= mid <= L::leaf_cap_spec());
            // right is a non-empty leaf, node_wf — needed for L::key(&right, 0).
            assert(L::is_leaf_spec(right));
            assert(L::node_wf(right));
            assert(L::count_spec(right) == (L::leaf_cap_spec() + 1 - mid) as nat);
            assert(L::count_spec(right) >= 1);
        }

        // Allocate the right leaf at the arena tail. self is untouched so far
        // (leaf_split_at took &leaf, not &mut self), so the arena and its
        // capacity slack are still the precondition's.
        assert(self.arena() == old(self).arena());
        let right_idx = self.nodes.len();
        proof {
            assert(right_idx.as_nat() == self.arena().len());
            assert(self.arena().len() + 2 < <L::ArenaIdx as IndexLike>::max_nat());
            assert(self.arena().len() + 1 < <L::ArenaIdx as IndexLike>::max_nat());
        }
        self.nodes.push(right);

        // Re-point left's forward link to the new right leaf, write left back.
        L::set_link(&mut left, right_idx);
        proof { assert(L::link_view(left) == right_idx.as_nat()); }
        self.nodes.set_index(self.root, left);

        // Build and allocate the new internal root: separator = right[0].
        let sep = L::key(&right, 0);
        let new_root_idx = self.nodes.len();
        let new_root = L::new_internal2(sep, self.root, right_idx);
        self.nodes.push(new_root);

        self.nkeys = self.nkeys + 1;

        // Rewire the ghost tree to the height-1 B+tree. Ghost keys live in
        // nat-space: combined_nat is the model's keys with `key` inserted; the
        // halves are its subranges. The word-space `combined` (from
        // leaf_split_at) bridges to it index-wise (proven below).
        let ghost combined_nat = gkeys.insert(pos as int, key.id_nat());
        let ghost left_keys = combined_nat.subrange(0, mid as int);
        let ghost right_keys = combined_nat.subrange(mid as int, combined_nat.len() as int);
        let ghost lt = Tree::Leaf { id: root_id, keys: left_keys };
        let ghost rt = Tree::Leaf { id: right_idx.as_nat(), keys: right_keys };
        let ghost new_tree = Tree::Inner {
            id: new_root_idx.as_nat(),
            seps: seq![right_keys[0]],
            kids: seq![lt, rt],
        };
        self.root = new_root_idx;
        self.tree = Ghost(new_tree);
        // The old root leaf split in two; the RIGHT half is now the rightmost
        // leaf, so the cache moves to it. (`last_leaf_id(new_tree)` unfolds to
        // `last_leaf_id(rt) == right_idx`, discharged in the proof block below.)
        self.last_leaf = right_idx;

        proof {
            let arena = self.arena();
            // Arena layout after push(right), set(root, left), push(new_root):
            // arena[root_id]==left, arena[right_idx]==right,
            // arena[new_root_idx]==new_root, indices distinct (root_id <
            // right_idx < new_root_idx, the latter two fresh tail pushes).
            assert(arena[root_id as int] == left);
            assert(arena[right_idx.as_nat() as int] == right);
            assert(arena[new_root_idx.as_nat() as int] == new_root);
            assert(root_id < right_idx.as_nat());
            assert(right_idx.as_nat() < new_root_idx.as_nat());

            // combined (words) projects index-wise to combined_nat.
            assert(combined.len() == L::leaf_cap_spec() + 1);
            assert(combined_nat.len() == combined.len());
            assert forall|i: int| 0 <= i < combined.len() implies
                combined[i].as_nat() == #[trigger] combined_nat[i] by {
                if i < pos {
                    assert(combined[i] == old_kview@[i]);
                    assert(combined_nat[i] == gkeys[i]);
                } else if i == pos {
                    assert(combined[i] == kw);
                    assert(combined_nat[i] == key.id_nat());
                } else {
                    assert(combined[i] == old_kview@[i - 1]);
                    assert(combined_nat[i] == gkeys[i - 1]);
                }
            }

            // combined_nat is strictly sorted with set == old ∪ {key} (the
            // sorted-insert step), so lemma_median_split gives the wf halves.
            crate::bplus_tree::lemma_sorted_insert(gkeys, key.id_nat(), pos as int);
            crate::bplus_tree::lemma_median_split(combined_nat, mid as int);

            // Separator: sep word's nat == combined_nat[mid] == right_keys[0].
            assert(sep == L::keys_view(right)[0]);
            assert(L::keys_view(right) == combined.subrange(mid as int, combined.len() as int));
            assert(sep == combined[mid as int]);
            assert(sep.as_nat() == combined_nat[mid as int]);
            assert(right_keys[0] == combined_nat[mid as int]);

            // Per-leaf binds projection: keys_view(left/right)[i].as_nat() ==
            // left_keys/right_keys[i], from keys_view == combined word subrange
            // and the index-wise bridge.
            assert forall|i: int| 0 <= i < left_keys.len() implies
                #[trigger] left_keys[i] == (L::keys_view(left)[i]).as_nat() by {
                assert(L::keys_view(left)[i] == combined[i]);
                assert(left_keys[i] == combined_nat[i]);
            }
            assert forall|i: int| 0 <= i < right_keys.len() implies
                #[trigger] right_keys[i] == (L::keys_view(right)[i]).as_nat() by {
                assert(L::keys_view(right)[i] == combined[mid as int + i]);
                assert(right_keys[i] == combined_nat[mid as int + i]);
            }

            // binds(arena, new_tree).
            self.lemma_split_binds(
                Ghost(root_id), Ghost(right_idx.as_nat()), Ghost(new_root_idx.as_nat()),
                Ghost(left), Ghost(right), Ghost(new_root),
                Ghost(left_keys), Ghost(right_keys), Ghost(sep),
            );

            // tree_wf + height + in-order keys of the height-1 tree.
            L::lemma_arena_capacity();  // key_cap >= 1 (and leaf_cap >= 1)
            crate::bplus_tree::lemma_split_tree_wf(
                new_root_idx.as_nat(), root_id, right_idx.as_nat(),
                left_keys, right_keys, L::leaf_cap_spec(), L::key_cap_spec(),
            );
            assert(crate::bplus_tree::tree_height(self.tree@) == 1);

            // model: left_keys + right_keys == combined_nat (subrange split);
            // its set is old model's set plus key.
            assert(left_keys + right_keys == combined_nat);
            assert(self.model() == combined_nat);

            // tree_leaf_ids(Inner{.., [Leaf lid, Leaf rid]}) == [lid] + [rid].
            let lids = crate::bplus_tree::tree_leaf_ids(self.tree@);
            crate::bplus_tree::lemma_forest_leaf_ids_cons(seq![lt, rt]);
            assert(seq![lt, rt].drop_first() =~= seq![rt]);
            crate::bplus_tree::lemma_forest_leaf_ids_cons(seq![rt]);
            assert(seq![rt].drop_first() =~= Seq::<Tree>::empty());
            assert(lids =~= seq![root_id, right_idx.as_nat()]);

            // leaf-link chain: [root_id, right_idx], left -> right, right -> NIL.
            self.lemma_split_leaf_links(
                Ghost(root_id), Ghost(right_idx.as_nat()), Ghost(new_root_idx.as_nat()),
                Ghost(left), Ghost(right),
            );

            // tree_disjoint(Inner{new_root, [lt, rt]}): new_root_idx not in the
            // children's footprints {root_id, right_idx}, the two leaves'
            // footprints {root_id} / {right_idx} disjoint, leaves trivially
            // disjoint. All three ids distinct (root_id < right_idx <
            // new_root_idx).
            let kids = seq![lt, rt];
            assert(crate::bplus_tree::tree_ids(lt) =~= set![root_id]);
            assert(crate::bplus_tree::tree_ids(rt) =~= set![right_idx.as_nat()]);
            crate::bplus_tree::lemma_forest_ids_cons(kids);
            assert(kids.drop_first() =~= seq![rt]);
            crate::bplus_tree::lemma_forest_ids_cons(seq![rt]);
            assert(seq![rt].drop_first() =~= Seq::<Tree>::empty());
            assert(crate::bplus_tree::forest_ids(kids)
                =~= set![root_id].union(set![right_idx.as_nat()]));
            assert(!crate::bplus_tree::forest_ids(kids).contains(new_root_idx.as_nat()));
            // forest_disjoint([lt, rt]): both leaves tree_disjoint (Leaf arm).
            crate::bplus_tree::lemma_forest_disjoint_cons(kids);
            crate::bplus_tree::lemma_forest_disjoint_cons(seq![rt]);
            assert(crate::bplus_tree::forest_disjoint(Seq::<Tree>::empty()));
            assert(crate::bplus_tree::forest_disjoint(seq![rt]));
            assert(crate::bplus_tree::forest_disjoint(kids));
            assert forall|i: int, j: int| 0 <= i < j < kids.len() implies
                (#[trigger] crate::bplus_tree::tree_ids(kids[i]))
                    .disjoint(#[trigger] crate::bplus_tree::tree_ids(kids[j])) by {
                // only i==0, j==1: {root_id} disjoint {right_idx}, root_id != right_idx.
                assert(crate::bplus_tree::tree_ids(kids[0]) =~= set![root_id]);
                assert(crate::bplus_tree::tree_ids(kids[1]) =~= set![right_idx.as_nat()]);
            }
            assert(crate::bplus_tree::tree_disjoint(self.tree@));

            assert(self.nkeys as nat == self.model().len());
            // model_bounded: model == combined_nat == gkeys.insert(pos, key.id_nat());
            // gkeys (== old model) bounded by old wf, key.id_nat() < id_bound.
            key.lemma_id_nat_bounded();
            assert(model_bounded::<K>(gkeys));
            lemma_model_bounded_insert::<K>(gkeys, pos as int, key.id_nat());
            assert(self.model() == combined_nat);
            assert(model_bounded::<K>(self.model()));

            // node_count == arena.len(): old single-leaf root (node_count 1,
            // arena.len 1) became Inner{new_root, [lt, rt]} (node_count 3) after
            // push(right) + set(root,left) + push(new_root) (arena.len 1+2 == 3).
            assert(crate::bplus_tree::node_count(rt) == 1);   // Leaf
            assert(crate::bplus_tree::node_count(lt) == 1);   // Leaf
            // forest_node_count([lt, rt]) unfolds: nc(lt) + (nc(rt) + fnc([])).
            assert(kids[0] == lt);
            assert(kids.drop_first() =~= seq![rt]);
            assert(seq![rt][0] == rt);
            assert(seq![rt].drop_first() =~= Seq::<Tree>::empty());
            assert(crate::bplus_tree::forest_node_count(Seq::<Tree>::empty()) == 0);
            assert(crate::bplus_tree::forest_node_count(seq![rt]) == 1);
            assert(crate::bplus_tree::forest_node_count(kids) == 2);
            assert(crate::bplus_tree::node_count(self.tree@) == 3);   // 1 + 2
            assert(self.arena().len() == 3);                          // old 1 + 2 pushes

            // last_leaf_ok: last_leaf_id(Inner{_, _, [lt, rt]}) descends to the
            // last child rt, a Leaf, whose id is right_idx.
            assert(kids.len() == 2);
            assert(kids[kids.len() - 1] == rt);
            assert(crate::bplus_tree::last_leaf_id(rt) == right_idx.as_nat());
            assert(crate::bplus_tree::last_leaf_id(self.tree@) == right_idx.as_nat());
            assert(self.last_leaf_ok());
        }
        true
    }

    /// Reconstruct `binds` for the post-split height-1 tree. The two leaves bind
    /// (each subrange word projects to its ghost key), and the new root's two
    /// `child_view`s read back the leaf ids. Pulled out of `insert_split_root`
    /// so the per-key foralls have a clean scope.
    proof fn lemma_split_binds(
        &self,
        lid: Ghost<nat>,
        rid: Ghost<nat>,
        new_root_id: Ghost<nat>,
        left: Ghost<L::Node>,
        right: Ghost<L::Node>,
        new_root: Ghost<L::Node>,
        left_keys: Ghost<Seq<nat>>,
        right_keys: Ghost<Seq<nat>>,
        sep: Ghost<L::Word>,
    )
        requires
            self.arena()[lid@ as int] == left@,
            self.arena()[rid@ as int] == right@,
            self.arena()[new_root_id@ as int] == new_root@,
            lid@ < self.arena().len(),
            rid@ < self.arena().len(),
            new_root_id@ < self.arena().len(),
            lid@ != rid@,
            L::is_leaf_spec(left@),
            L::is_leaf_spec(right@),
            L::count_spec(left@) == left_keys@.len(),
            L::count_spec(right@) == right_keys@.len(),
            right_keys@.len() >= 1,
            !L::is_leaf_spec(new_root@),
            L::count_spec(new_root@) == 1,
            L::keys_view(new_root@) == seq![sep@],
            sep@.as_nat() == right_keys@[0],
            L::child_view(new_root@, 0) == lid@,
            L::child_view(new_root@, 1) == rid@,
            // each leaf's words project to its ghost keys.
            (forall|i: int| 0 <= i < left_keys@.len() ==>
                #[trigger] left_keys@[i] == (L::keys_view(left@)[i]).as_nat()),
            (forall|i: int| 0 <= i < right_keys@.len() ==>
                #[trigger] right_keys@[i] == (L::keys_view(right@)[i]).as_nat()),
            self.tree@ == (Tree::Inner {
                id: new_root_id@,
                seps: seq![right_keys@[0]],
                kids: seq![Tree::Leaf { id: lid@, keys: left_keys@ },
                           Tree::Leaf { id: rid@, keys: right_keys@ }],
            }),
        ensures
            binds::<L>(self.arena(), self.tree@),
    {
        let arena = self.arena();
        let lt = Tree::Leaf { id: lid@, keys: left_keys@ };
        let rt = Tree::Leaf { id: rid@, keys: right_keys@ };
        let kids = seq![lt, rt];
        // each leaf binds (leaf arm: id in range, leaf, count, per-key).
        assert(binds::<L>(arena, lt)) by {
            assert forall|i: int| 0 <= i < left_keys@.len() implies
                (#[trigger] L::keys_view(arena[lid@ as int])[i]).as_nat() == left_keys@[i] by {
                assert(arena[lid@ as int] == left@);
            }
        }
        assert(binds::<L>(arena, rt)) by {
            assert forall|i: int| 0 <= i < right_keys@.len() implies
                (#[trigger] L::keys_view(arena[rid@ as int])[i]).as_nat() == right_keys@[i] by {
                assert(arena[rid@ as int] == right@);
            }
        }
        // forest_binds_l([lt, rt]) = binds(lt) && forest_binds_l([rt])
        //                          = binds(lt) && binds(rt) && forest_binds_l([]).
        assert(kids[0] == lt);
        assert(kids.drop_first() =~= seq![rt]);
        assert(seq![rt][0] == rt);
        assert(seq![rt].drop_first() =~= Seq::<Tree>::empty());
        assert(forest_binds_l::<L>(arena, Seq::<Tree>::empty()));
        assert(forest_binds_l::<L>(arena, seq![rt]));
        assert(forest_binds_l::<L>(arena, kids));
        // root binds (inner arm): !leaf, count == 1 == seps.len(), sep projects,
        // child_view(0/1) == kids[0/1].id, forest binds.
        assert(crate::bplus_tree::tree_root_id(kids[0]) == lid@);
        assert(crate::bplus_tree::tree_root_id(kids[1]) == rid@);
        assert forall|i: int| 0 <= i < 2 implies
            L::child_view(arena[new_root_id@ as int], i)
                == crate::bplus_tree::tree_root_id(#[trigger] kids[i]) by {
            assert(arena[new_root_id@ as int] == new_root@);
        }
        assert(binds::<L>(arena, self.tree@));
    }

    /// Reconstruct `leaf_links_ok` for the post-split tree: the in-order leaf
    /// ids are `[lid, rid]`, `left` links to `rid`, `right` links to NIL.
    proof fn lemma_split_leaf_links(
        &self,
        lid: Ghost<nat>,
        rid: Ghost<nat>,
        new_root_id: Ghost<nat>,
        left: Ghost<L::Node>,
        right: Ghost<L::Node>,
    )
        requires
            self.arena()[lid@ as int] == left@,
            self.arena()[rid@ as int] == right@,
            lid@ < self.arena().len(),
            rid@ < self.arena().len(),
            lid@ != rid@,
            L::link_view(left@) == rid@,
            L::link_view(right@) == nil_link::<L>(),
            self.tree@ == (Tree::Inner {
                id: new_root_id@,
                seps: self.tree@->Inner_seps,
                kids: seq![Tree::Leaf { id: lid@, keys: self.tree@->Inner_kids[0]->Leaf_keys },
                           Tree::Leaf { id: rid@, keys: self.tree@->Inner_kids[1]->Leaf_keys }],
            }),
            crate::bplus_tree::tree_leaf_ids(self.tree@) == seq![lid@, rid@],
        ensures
            leaf_links_ok::<L>(self.arena(), self.tree@),
    {
        let arena = self.arena();
        let lids = crate::bplus_tree::tree_leaf_ids(self.tree@);
        assert(lids == seq![lid@, rid@]);
        assert(lids.len() == 2 && lids[0] == lid@ && lids[1] == rid@);
        assert forall|p: int| 0 <= p < lids.len() implies
            #[trigger] L::link_view(arena[lids[p] as int]) == (
                if p + 1 < lids.len() { lids[p + 1] } else { nil_link::<L>() }
            ) by {
            if p == 0 {
                assert(arena[lids[0] as int] == left@);  // links to rid == lids[1]
            } else {
                assert(arena[lids[1] as int] == right@);  // links to NIL
            }
        }
    }

    /// Recursive insert into the subtree rooted at `idx` (binding ghost `cur`,
    /// height `h`, leaf-link successor `succ`). Mutates only `self.nodes` (the
    /// arena); `self.tree`/`self.root`/`self.nkeys` are the caller's to update.
    ///
    /// Returns `(added, split, new_left, new_right)`:
    ///   - `split == None`: absorbed. The subtree is now `new_left@`, same root
    ///     id, `subtree_wf` at `(h, succ)`, model gained `key` (if `added`).
    ///   - `split == Some((sep, rid))`: the subtree split into `new_left@` (at
    ///     `idx`, successor = first leaf of `new_right@`) and `new_right@` (at
    ///     `rid`, successor `succ`), separated by `sep`, each `subtree_wf` at `h`.
    ///
    /// LEAF BASE CASE ONLY for now (`requires is_leaf`); the internal recursive
    /// case is the next step. The arena only grows (pushes) plus a `set` on
    /// `idx`, so disjoint sibling subtrees frame out via `lemma_subtree_wf_frame`.
    fn insert_rec_leaf(
        &mut self,
        idx: L::ArenaIdx,
        // The node at `idx`, already read by the caller to test `is_leaf`. Passed
        // in rather than re-read: the caller (`insert_rec`) holds it, and reading
        // it again copies the whole 248-byte node a second time for no new
        // information. The `requires` below ties it to the arena slot, so every
        // proof that spoke about the removed local read speaks about this instead,
        // with no weakening.
        node: &L::Node,
        key: K,
        kw: L::Word,
        cur: Ghost<Tree>,
        h: Ghost<nat>,
        succ: Ghost<nat>,
        is_root: Ghost<bool>,
    ) -> (res: (bool, Option<(L::Word, L::ArenaIdx)>, Ghost<Tree>, Ghost<Tree>))
        requires
            old(self).nodes.wf(),
            // `cur` is wf at the caller's root-ness; the absorb (None) output is
            // re-established at the SAME `is_root` (a root leaf stays a root leaf),
            // while a split's two halves are always genuinely non-root.
            Self::subtree_wf(old(self).arena(), cur@, h@, succ@, is_root@),
            idx.as_nat() == crate::bplus_tree::tree_root_id(cur@),
            L::is_leaf_spec(old(self).arena()[idx.as_nat() as int]),
            // `node` IS the arena slot: the caller read it and has not mutated
            // since, so this is the same fact the removed local read established.
            *node == old(self).arena()[idx.as_nat() as int],
            kw.as_nat() == key.id_nat(),
            h@ == 0,
            old(self).arena().len() + 2 < <L::ArenaIdx as IndexLike>::max_nat(),
        ensures
            final(self).nodes.wf(),
            // only the arena (self.nodes) is touched; the cached count, root index,
            // and ghost tree are unchanged (the caller frames its bookkeeping).
            final(self).nkeys == old(self).nkeys,
            final(self).root == old(self).root,
            final(self).tree@ == old(self).tree@,
            // Phase 7 frame: push/set never touch the snapshot stack or the
            // archives, so the (opaque) archive agreement transfers upward.
            final(self).header_archive@ == old(self).header_archive@,
            final(self).tree_snapshots@ == old(self).tree_snapshots@,
            final(self).nodes.snapshots_view() == old(self).nodes.snapshots_view(),
            old(self).arena().len() <= final(self).arena().len(),
            // a leaf insert allocates at most one node (the split's right leaf).
            final(self).arena().len() <= old(self).arena().len() + h@ + 1,
            forall|i: int| 0 <= i < old(self).arena().len()
                && !crate::bplus_tree::tree_ids(cur@).contains(i as nat)
                ==> #[trigger] final(self).arena()[i] == old(self).arena()[i],
            // (M6) ARENA/NODE-COUNT DELTA: the arena grows by exactly the increase
            // in total node count. For a leaf both cur and the result(s) are leaves
            // (node_count 1 each), so None is +0 and a split is +1 == 1+1-1.
            ({
                let (added, split, nl, nr) = res;
                match split {
                    Option::None =>
                        final(self).arena().len() + crate::bplus_tree::node_count(cur@)
                            == old(self).arena().len() + crate::bplus_tree::node_count(nl@),
                    Option::Some(_) =>
                        final(self).arena().len() + crate::bplus_tree::node_count(cur@)
                            == old(self).arena().len()
                                + crate::bplus_tree::node_count(nl@)
                                + crate::bplus_tree::node_count(nr@),
                }
            }),
            ({
                let (added, split, nl, nr) = res;
                match split {
                    Option::None => {
                        &&& Self::subtree_wf(final(self).arena(), nl@, h@, succ@, is_root@)
                        &&& crate::bplus_tree::tree_root_id(nl@) == idx.as_nat()
                        &&& crate::bplus_tree::tree_ids(nl@) == crate::bplus_tree::tree_ids(cur@)
                        &&& crate::bplus_tree::tree_leaf_ids(nl@) == crate::bplus_tree::tree_leaf_ids(cur@)
                        &&& crate::bplus_tree::tree_keys(nl@).to_set()
                                == crate::bplus_tree::tree_keys(cur@).to_set().insert(key.id_nat())
                        &&& added == !crate::bplus_tree::tree_keys(cur@).contains(key.id_nat())
                        // (weakening) min-key-preservation ensures clause REMOVED.
                    }
                    Option::Some((sep, rid)) => {
                        // a split happens only on a genuinely new key (a full node
                        // with key absent), so `added` carries the SAME membership
                        // characterization as the None arm — the caller needs it
                        // to discharge `added == !contains` uniformly.
                        &&& added == !crate::bplus_tree::tree_keys(cur@).contains(key.id_nat())
                        &&& Self::subtree_wf(final(self).arena(), nl@, h@,
                                crate::bplus_tree::tree_leaf_ids(nr@)[0], false)
                        &&& Self::subtree_wf(final(self).arena(), nr@, h@, succ@, false)
                        &&& crate::bplus_tree::tree_root_id(nl@) == idx.as_nat()
                        &&& crate::bplus_tree::tree_root_id(nr@) == rid.as_nat()
                        &&& crate::bplus_tree::tree_keys(nr@).len() >= 1
                        // (second weakening) both `sep == tree_keys(nr)[0]` and the
                        // weaker `sep ∈ nl+nr` membership are REMOVED. Only the
                        // ordering below survives — it is all the parent splice needs.
                        &&& (crate::bplus_tree::tree_keys(nl@) + crate::bplus_tree::tree_keys(nr@)).to_set()
                                == crate::bplus_tree::tree_keys(cur@).to_set().insert(key.id_nat())
                        // cross-node ordering of the two halves around `sep`: the
                        // left half is all `< sep`, the right half all `>= sep`.
                        // (The split's median property.) The caller needs this to
                        // re-establish `tree_wf`'s ordering clause when it slots
                        // (nl, sep, nr) back into the parent's children.
                        &&& crate::bplus_tree::keys_all_lt(nl@, sep.as_nat())
                        &&& crate::bplus_tree::keys_all_ge(nr@, sep.as_nat())
                        // (F1) footprint: every id of the two halves is either an
                        // old id of `cur` or a freshly-pushed tail id. Lets the
                        // caller frame siblings (new ids disjoint from old ones).
                        &&& (forall|id: nat| crate::bplus_tree::tree_ids(nl@).contains(id)
                                ==> crate::bplus_tree::tree_ids(cur@).contains(id)
                                    || id >= old(self).arena().len())
                        &&& (forall|id: nat| crate::bplus_tree::tree_ids(nr@).contains(id)
                                ==> crate::bplus_tree::tree_ids(cur@).contains(id)
                                    || id >= old(self).arena().len())
                        // the two halves have disjoint footprints (a split puts
                        // them in separate arena regions); the parent reconstruction
                        // needs this to re-establish tree_disjoint over the splice.
                        &&& crate::bplus_tree::tree_ids(nl@).disjoint(crate::bplus_tree::tree_ids(nr@))
                        // the old subtree's ids are retained across the two halves
                        // (a split distributes them, never drops one).
                        &&& (forall|id: nat| crate::bplus_tree::tree_ids(cur@).contains(id)
                                ==> crate::bplus_tree::tree_ids(nl@).contains(id)
                                    || crate::bplus_tree::tree_ids(nr@).contains(id))
                        // nl (the left half) keeps the subtree's leftmost leaf.
                        &&& crate::bplus_tree::tree_leaf_ids(nl@).len() >= 1
                        &&& crate::bplus_tree::tree_leaf_ids(nl@)[0] == crate::bplus_tree::tree_leaf_ids(cur@)[0]
                        // (weakening) min-key-preservation ensures clause REMOVED.
                    }
                }
            }),
    {
        let ghost gkeys = crate::bplus_tree::tree_keys(cur@);
        let ghost lid = idx.as_nat();
        // cur is a Leaf (arena node at idx is a leaf, binds consistent).
        proof {
            match cur@ {
                Tree::Leaf { id, keys } => {
                    assert(id == lid);
                    assert(gkeys == keys);
                    // binds leaf arm: count == keys.len, node_wf via the iff.
                    assert(L::count_spec(self.arena()[lid as int]) == keys.len());
                    L::lemma_node_wf_iff(self.arena()[lid as int]);
                }
                Tree::Inner { id, .. } => {
                    assert(id == lid);
                    assert(!L::is_leaf_spec(self.arena()[lid as int]));
                    assert(false);
                }
            }
        }

        // cur@ is exactly Leaf{lid, gkeys} (established above) — name it for the
        // per-key binds projection and the sortedness fact.
        proof { assert(cur@ == Tree::Leaf { id: lid, keys: gkeys }); }

        // `leaf` is the node the CALLER already read to test `is_leaf`; binding it
        // by reference makes the leaf level read the 248-byte node once instead of
        // twice (measured ~6 ns/insert on this layout -- the largest single item
        // left in the mutation path once frame size was falsified).
        let leaf: &L::Node = node;
        let n = L::count(leaf);
        proof {
            assert(self.arena()[lid as int] == *leaf);
            assert(gkeys.len() == n as nat);
            assert(L::node_wf(*leaf));
        }

        // pos = find_ge(keys, key): the O(log cap) verified binary search.
        // Production: `S::find_ge` at bplus.rs:661. Its postcondition gives the
        // two-sided split directly, so presence reduces to one probe at `pos`.
        proof { lemma_tree_wf_sorted_seps_view::<L>(self.arena(), cur@, lid, *leaf); }
        let pos = self.leaf_find_ge(leaf, kw);
        proof {
            assert(pos as nat <= gkeys.len());
            assert forall|j: int| 0 <= j < pos implies gkeys[j] < key.id_nat() by {
                lemma_leaf_binds_key_at::<K, L, S, TRACK>(self.arena(), cur@, lid, j);
            }
            assert forall|j: int| pos <= j < n implies key.id_nat() <= gkeys[j] by {
                lemma_leaf_binds_key_at::<K, L, S, TRACK>(self.arena(), cur@, lid, j);
            }
        }

        // presence at the boundary: keys[pos] >= key already, so the key is
        // present iff keys[pos] <= key too (i.e. equal), and only there —
        // everything left of pos is strictly smaller, everything right strictly
        // larger (sortedness + the >= arm).
        let mut present = false;
        if pos < n {
            let ki: L::Word = L::key(leaf, pos);
            let le = ki.le(kw);
            proof {
                <L::Word as IndexLike>::lemma_order_is_as_nat(ki, kw);
                lemma_leaf_binds_key_at::<K, L, S, TRACK>(self.arena(), cur@, lid, pos as int);
                assert(ki == L::keys_view(*leaf)[pos as int]);
                assert(ki.as_nat() == gkeys[pos as int]);
            }
            if le {
                present = true;
                proof { assert(gkeys[pos as int] == key.id_nat()); }
            }
        }

        if present {
            proof { assert(gkeys.contains(key.id_nat())); }
            return (false, None, cur, cur);
        }

        // absent: establish the find-position characterization.
        proof {
            assert(crate::bplus_tree::strictly_sorted(gkeys));  // leaf tree_wf
            assert forall|j: int| pos <= j < n implies key.id_nat() < gkeys[j] by {
                // key <= gkeys[pos] <= gkeys[j], and gkeys[pos] != key (!present).
                if pos < j { assert(gkeys[pos as int] < gkeys[j]); }
            }
            assert(!gkeys.contains(key.id_nat()));
        }

        // capture old key view + the NIL/successor link before mutating.
        let ghost old_kview = L::keys_view(*leaf);
        proof {
            L::lemma_keys_view_len(*leaf);
            assert forall|j: int| 0 <= j < gkeys.len() implies old_kview[j].as_nat() == #[trigger] gkeys[j] by {
                lemma_leaf_binds_key_at::<K, L, S, TRACK>(self.arena(), cur@, lid, j);
            }
            // subtree leaf-link: this leaf's link is `succ` (single-leaf chain).
            let lids = crate::bplus_tree::tree_leaf_ids(cur@);
            assert(lids =~= seq![lid]);
            assert(lids.len() == 1 && lids[0] == lid);
            // leaf_links_to at p==0: p+1==1 not < len 1, so link == succ.
            assert(L::link_view(self.arena()[lids[0] as int]) == succ@);
            assert(L::link_view(self.arena()[lid as int]) == succ@);
        }

        let leaf_cap = L::leaf_cap();
        if n < leaf_cap {
            // -- absorb: shift-insert, write back, return None --------------
            let mut nleaf = *leaf;
            L::leaf_insert_at(&mut nleaf, pos, kw);
            proof {
                assert(L::count_spec(nleaf) == n as nat + 1);
                assert(L::keys_view(nleaf) == old_kview.insert(pos as int, kw));
                assert(L::link_view(nleaf) == succ@);  // leaf_insert_at preserves link
            }
            self.nodes.set_index(idx, nleaf);
            let ghost new_keys = gkeys.insert(pos as int, key.id_nat());
            let ghost nl = Tree::Leaf { id: lid, keys: new_keys };
            proof {
                // arena[lid] == nleaf now; binds(nl): per-key projection from the
                // insert shift (old_kview projects to gkeys, kw to key).
                assert(self.arena()[lid as int] == nleaf);
                let kvi = L::keys_view(nleaf);
                assert(kvi == old_kview.insert(pos as int, kw));
                assert(old_kview.len() == gkeys.len());
                assert forall|i: int| 0 <= i < new_keys.len() implies
                    (#[trigger] kvi[i]).as_nat() == new_keys[i] by {
                    if i < pos {
                        assert(kvi[i] == old_kview[i]); assert(new_keys[i] == gkeys[i]);
                    } else if i == pos {
                        assert(kvi[i] == kw); assert(new_keys[i] == key.id_nat());
                    } else {
                        assert(kvi[i] == old_kview[i - 1]); assert(new_keys[i] == gkeys[i - 1]);
                    }
                }
                assert(binds::<L>(self.arena(), nl));
                // tree_wf(nl, h==0) at the caller's is_root: sorted + count, and
                // occupancy when non-root (nl has n+1 keys, n was the input count
                // which already met the non-root bound when is_root@ was false).
                crate::bplus_tree::lemma_sorted_insert(gkeys, key.id_nat(), pos as int);
                assert(new_keys.len() == gkeys.len() + 1);
                assert(crate::bplus_tree::tree_wf(nl, h@, L::leaf_cap_spec(), L::key_cap_spec(), is_root@));
                // leaf_links_to(nl, succ): single leaf [lid], link == succ.
                assert(crate::bplus_tree::tree_leaf_ids(nl) =~= seq![lid]);
                assert(leaf_links_to::<L>(self.arena(), nl, succ@));
                // tree_disjoint(nl): single leaf, trivial.
                assert(crate::bplus_tree::tree_disjoint(nl));
                // model set: new_keys.to_set() == gkeys.to_set() ∪ {key}.
                assert(new_keys.to_set() =~= gkeys.to_set().insert(key.id_nat()));
            }
            return (true, None, Ghost(nl), cur);
        }

        // -- split: full leaf, allocate a right sibling, return Some ---------
        let ghost combined = old_kview.insert(pos as int, kw);
        let (mut nleft, right) = L::leaf_split_at(leaf, pos, kw);
        let ghost mid = L::split_mid_spec();
        proof {
            assert(combined == L::keys_view(*leaf).insert(pos as int, kw));
            assert(combined.len() == L::leaf_cap_spec() + 1);
            assert(L::keys_view(nleft) == combined.subrange(0, mid as int));
            assert(L::keys_view(right) == combined.subrange(mid as int, combined.len() as int));
            assert(L::link_view(right) == succ@);  // right inherits the old leaf's link
            L::lemma_arena_capacity();
            L::lemma_split_mid();
            assert(1 <= mid <= L::leaf_cap_spec());
            assert(L::is_leaf_spec(right) && L::node_wf(right));
            assert(L::count_spec(right) == (L::leaf_cap_spec() + 1 - mid) as nat);
            assert(L::count_spec(right) >= 1);
        }

        // allocate the right leaf at the tail.
        let right_idx = self.nodes.len();
        proof {
            assert(right_idx.as_nat() == self.arena().len());
            assert(self.arena().len() + 1 < <L::ArenaIdx as IndexLike>::max_nat());
        }
        self.nodes.push(right);
        // re-point left's link to the new right id, write left back at idx.
        L::set_link(&mut nleft, right_idx);
        proof { assert(L::link_view(nleft) == right_idx.as_nat()); }
        self.nodes.set_index(idx, nleft);

        let sep = L::key(&right, 0);

        // ghost halves: left keys / right keys (nat projections of the subranges).
        let ghost combined_nat = gkeys.insert(pos as int, key.id_nat());
        let ghost left_keys = combined_nat.subrange(0, mid as int);
        let ghost right_keys = combined_nat.subrange(mid as int, combined_nat.len() as int);
        let ghost nl = Tree::Leaf { id: lid, keys: left_keys };
        let ghost nr = Tree::Leaf { id: right_idx.as_nat(), keys: right_keys };

        proof {
            let arena = self.arena();
            // arena[lid] == nleft, arena[right_idx] == right, lid != right_idx.
            assert(arena[lid as int] == nleft);
            assert(arena[right_idx.as_nat() as int] == right);
            assert(lid < right_idx.as_nat());

            // combined (words) projects to combined_nat index-wise.
            assert(combined.len() == combined_nat.len());
            assert forall|i: int| 0 <= i < combined.len() implies combined[i].as_nat() == #[trigger] combined_nat[i] by {
                if i < pos {
                    assert(combined[i] == old_kview[i]); assert(combined_nat[i] == gkeys[i]);
                } else if i == pos {
                    assert(combined[i] == kw); assert(combined_nat[i] == key.id_nat());
                } else {
                    assert(combined[i] == old_kview[i - 1]); assert(combined_nat[i] == gkeys[i - 1]);
                }
            }
            crate::bplus_tree::lemma_sorted_insert(gkeys, key.id_nat(), pos as int);
            crate::bplus_tree::lemma_median_split(combined_nat, mid as int);

            // separator: sep word's nat == combined_nat[mid] == right_keys[0].
            assert(sep == L::keys_view(right)[0]);
            assert(sep == combined[mid as int]);
            assert(sep.as_nat() == combined_nat[mid as int]);
            assert(right_keys[0] == combined_nat[mid as int]);

            // binds(nl), binds(nr): per-key projections from the word subranges.
            assert forall|i: int| 0 <= i < left_keys.len() implies
                (#[trigger] L::keys_view(nleft)[i]).as_nat() == left_keys[i] by {
                assert(L::keys_view(nleft)[i] == combined[i]);
                assert(left_keys[i] == combined_nat[i]);
            }
            assert(binds::<L>(arena, nl));
            assert forall|i: int| 0 <= i < right_keys.len() implies
                (#[trigger] L::keys_view(right)[i]).as_nat() == right_keys[i] by {
                assert(L::keys_view(right)[i] == combined[mid as int + i]);
                assert(right_keys[i] == combined_nat[mid as int + i]);
            }
            assert(binds::<L>(arena, nr));

            // tree_wf both halves (h, non-root): sorted + count bounds + occupancy.
            assert(crate::bplus_tree::strictly_sorted(left_keys));
            assert(crate::bplus_tree::strictly_sorted(right_keys));
            assert(left_keys.len() == mid);          // == (cap+1)/2 >= 1
            assert(right_keys.len() == (L::leaf_cap_spec() + 1 - mid) as nat);
            assert(crate::bplus_tree::tree_wf(nl, h@, L::leaf_cap_spec(), L::key_cap_spec(), false));
            assert(crate::bplus_tree::tree_wf(nr, h@, L::leaf_cap_spec(), L::key_cap_spec(), false));

            // leaf-links: nl -> right_idx (== nr's first leaf), nr -> succ.
            assert(crate::bplus_tree::tree_leaf_ids(nl) =~= seq![lid]);
            assert(crate::bplus_tree::tree_leaf_ids(nr) =~= seq![right_idx.as_nat()]);
            assert(crate::bplus_tree::tree_keys(nr) == right_keys);
            assert(leaf_links_to::<L>(arena, nl, right_idx.as_nat()));
            assert(leaf_links_to::<L>(arena, nr, succ@));

            // tree_disjoint both (single leaves).
            assert(crate::bplus_tree::tree_disjoint(nl));
            assert(crate::bplus_tree::tree_disjoint(nr));

            // model: left_keys + right_keys == combined_nat == gkeys ∪ {key}.
            assert(left_keys + right_keys == combined_nat);
            assert((left_keys + right_keys).to_set() =~= gkeys.to_set().insert(key.id_nat()));
            assert(crate::bplus_tree::tree_keys(nr)[0] == right_keys[0]);

            // (F1) footprint: nl == Leaf{lid} (lid ∈ tree_ids(cur)); nr ==
            // Leaf{right_idx}, right_idx == old arena len (fresh).
            assert(crate::bplus_tree::tree_ids(nl) =~= set![lid]);
            assert(crate::bplus_tree::tree_ids(cur@).contains(lid));   // cur == Leaf{lid}
            assert(crate::bplus_tree::tree_ids(nr) =~= set![right_idx.as_nat()]);
            assert(right_idx.as_nat() == old(self).arena().len());
            // (second weakening) the `sep ∈ (nl+nr)` membership proof block REMOVED
            // (the postcondition no longer carries it; only the ordering survives).
            assert(crate::bplus_tree::tree_keys(nl) == left_keys);
        }
        (true, Some((sep, right_idx)), Ghost(nl), Ghost(nr))
    }

    /// Recursive insert into the subtree at `idx` (ghost `cur`, height `h`,
    /// leaf-link successor `succ`). General over leaf/internal; `decreases h`.
    /// Same contract as [`insert_rec_leaf`] but without the leaf restriction.
    /// Mutates only `self.nodes`. The internal case descends to child `cp =
    /// find_gt(seps, key)`, recurses, then absorbs (`internal_insert_at`) or
    /// splits (`internal_split_at`), framing the untouched siblings.
    fn insert_rec(
        &mut self,
        idx: L::ArenaIdx,
        key: K,
        kw: L::Word,
        cur: Ghost<Tree>,
        h: Ghost<nat>,
        succ: Ghost<nat>,
        is_root: Ghost<bool>,
    ) -> (res: (bool, Option<(L::Word, L::ArenaIdx)>, Ghost<Tree>, Ghost<Tree>))
        requires
            old(self).nodes.wf(),
            // `cur` is wf at the caller's root-ness. The absorb (None) output is
            // re-established at the SAME `is_root` (the node's id is unchanged, so a
            // root stays the root); a split's two halves are always non-root, and
            // the recursive descent into a child always passes is_root=false (a
            // child of any node is genuinely non-root). The split branch needs only
            // `cur` FULL (its guard), which meets the non-root bound regardless.
            Self::subtree_wf(old(self).arena(), cur@, h@, succ@, is_root@),
            idx.as_nat() == crate::bplus_tree::tree_root_id(cur@),
            h@ == crate::bplus_tree::tree_height(cur@),
            kw.as_nat() == key.id_nat(),
            // arena headroom for the WHOLE descent path: a B+tree insert allocates
            // at most one node per level (a split per level), so `h + 1` plus
            // slack. The recursive call below gets `h - 1`, and after it returns
            // the parent's own push still fits. (Spec strengthened from `+2`,
            // which only covered a single non-recursive level — the recursion
            // exposed it: by the time a deep parent splits, the arena has already
            // grown past `old + 2`.)
            old(self).arena().len() + h@ + 2 < <L::ArenaIdx as IndexLike>::max_nat(),
        ensures
            final(self).nodes.wf(),
            // only the arena (self.nodes) is touched; the cached count, root index,
            // and ghost tree are unchanged (the caller frames its bookkeeping).
            final(self).nkeys == old(self).nkeys,
            final(self).root == old(self).root,
            final(self).tree@ == old(self).tree@,
            // Phase 7 frame: push/set never touch the snapshot stack or the
            // archives, so the (opaque) archive agreement transfers upward.
            final(self).header_archive@ == old(self).header_archive@,
            final(self).tree_snapshots@ == old(self).tree_snapshots@,
            final(self).nodes.snapshots_view() == old(self).nodes.snapshots_view(),
            // arena grows by at most h + 1 (one allocation per level + new root
            // is the caller's; here, at most one per level of this subtree).
            old(self).arena().len() <= final(self).arena().len(),
            final(self).arena().len() <= old(self).arena().len() + h@ + 1,
            // FRAME: every arena slot outside cur's footprint is unchanged. Lets
            // the caller (the level above) frame this subtree's siblings.
            forall|i: int| 0 <= i < old(self).arena().len()
                && !crate::bplus_tree::tree_ids(cur@).contains(i as nat)
                ==> #[trigger] final(self).arena()[i] == old(self).arena()[i],
            // (M6) ARENA/NODE-COUNT DELTA: arena growth == total node-count increase.
            // None: new subtree nl replaces cur (delta == nc(nl) - nc(cur)); Some: cur
            // becomes the two halves nl+nr (delta == nc(nl)+nc(nr) - nc(cur)). This is
            // what makes `arena.len() == node_count(tree@)` a standing wf invariant,
            // hence M6 (arena never overflows).
            ({
                let (added, split, nl, nr) = res;
                match split {
                    Option::None =>
                        final(self).arena().len() + crate::bplus_tree::node_count(cur@)
                            == old(self).arena().len() + crate::bplus_tree::node_count(nl@),
                    Option::Some(_) =>
                        final(self).arena().len() + crate::bplus_tree::node_count(cur@)
                            == old(self).arena().len()
                                + crate::bplus_tree::node_count(nl@)
                                + crate::bplus_tree::node_count(nr@),
                }
            }),
            ({
                let (added, split, nl, nr) = res;
                match split {
                    Option::None => {
                        &&& Self::subtree_wf(final(self).arena(), nl@, h@, succ@, is_root@)
                        &&& crate::bplus_tree::tree_root_id(nl@) == idx.as_nat()
                        // (F0) footprint: `None` means "this node's root id is
                        // unchanged", NOT "the footprint is unchanged" — a node
                        // BELOW may have split and been absorbed, allocating
                        // fresh leaf + internal slots. So the honest contract is
                        // the same subset+freshness the `Some` arm uses: every
                        // retained id stays, every NEW id is a fresh tail slot.
                        // (Validated at runtime by `footprint_contract_holds`:
                        // ~10% of `None` inserts grow `tree_ids`. The old
                        // `tree_ids(nl) == tree_ids(cur)` claim was a spec bug.)
                        &&& crate::bplus_tree::tree_ids(cur@).subset_of(
                                crate::bplus_tree::tree_ids(nl@))
                        &&& (forall|id: nat| crate::bplus_tree::tree_ids(nl@).contains(id)
                                ==> crate::bplus_tree::tree_ids(cur@).contains(id)
                                    || id >= old(self).arena().len())
                        // first-leaf preservation: a split only ever splices a
                        // fresh leaf to the RIGHT, so a subtree's LEFTMOST leaf
                        // never moves. This (not full leaf-id-seq equality) is
                        // exactly what the leaf-link chain needs at the left
                        // child boundary; the leaf-id SET is a subset of
                        // tree_ids, so its disjointness rides on tree_ids above.
                        // (Runtime-validated by `footprint_contract_holds`.)
                        &&& crate::bplus_tree::tree_leaf_ids(nl@)[0]
                                == crate::bplus_tree::tree_leaf_ids(cur@)[0]
                        // min-key preservation when the inserted key is not a new
                        // minimum (key >= cur's min): the leftmost key is unchanged.
                        // (weakening) min-key-preservation ensures clause REMOVED.
                        &&& crate::bplus_tree::tree_keys(nl@).to_set()
                                == crate::bplus_tree::tree_keys(cur@).to_set().insert(key.id_nat())
                        &&& added == !crate::bplus_tree::tree_keys(cur@).contains(key.id_nat())
                    }
                    Option::Some((sep, rid)) => {
                        // a split happens only on a genuinely new key (a full node
                        // with key absent), so `added` carries the SAME membership
                        // characterization as the None arm — the caller needs it
                        // to discharge `added == !contains` uniformly.
                        &&& added == !crate::bplus_tree::tree_keys(cur@).contains(key.id_nat())
                        &&& Self::subtree_wf(final(self).arena(), nl@, h@,
                                crate::bplus_tree::tree_leaf_ids(nr@)[0], false)
                        &&& Self::subtree_wf(final(self).arena(), nr@, h@, succ@, false)
                        &&& crate::bplus_tree::tree_root_id(nl@) == idx.as_nat()
                        &&& crate::bplus_tree::tree_root_id(nr@) == rid.as_nat()
                        &&& crate::bplus_tree::tree_keys(nr@).len() >= 1
                        // (second weakening) both `sep == tree_keys(nr)[0]` and the
                        // weaker `sep ∈ nl+nr` membership are REMOVED. Only the
                        // ordering below survives — it is all the parent splice needs.
                        &&& (crate::bplus_tree::tree_keys(nl@) + crate::bplus_tree::tree_keys(nr@)).to_set()
                                == crate::bplus_tree::tree_keys(cur@).to_set().insert(key.id_nat())
                        // cross-node ordering of the two halves around `sep`: the
                        // left half is all `< sep`, the right half all `>= sep`.
                        // (The split's median property.) The caller needs this to
                        // re-establish `tree_wf`'s ordering clause when it slots
                        // (nl, sep, nr) back into the parent's children.
                        &&& crate::bplus_tree::keys_all_lt(nl@, sep.as_nat())
                        &&& crate::bplus_tree::keys_all_ge(nr@, sep.as_nat())
                        // (F1) footprint: every id of the two halves is either an
                        // old id of `cur` or a freshly-pushed tail id. Lets the
                        // caller frame siblings (new ids disjoint from old ones).
                        &&& (forall|id: nat| crate::bplus_tree::tree_ids(nl@).contains(id)
                                ==> crate::bplus_tree::tree_ids(cur@).contains(id)
                                    || id >= old(self).arena().len())
                        &&& (forall|id: nat| crate::bplus_tree::tree_ids(nr@).contains(id)
                                ==> crate::bplus_tree::tree_ids(cur@).contains(id)
                                    || id >= old(self).arena().len())
                        // the two halves have disjoint footprints (a split puts
                        // them in separate arena regions); the parent reconstruction
                        // needs this to re-establish tree_disjoint over the splice.
                        &&& crate::bplus_tree::tree_ids(nl@).disjoint(crate::bplus_tree::tree_ids(nr@))
                        // the old subtree's ids are retained across the two halves
                        // (a split distributes them, never drops one).
                        &&& (forall|id: nat| crate::bplus_tree::tree_ids(cur@).contains(id)
                                ==> crate::bplus_tree::tree_ids(nl@).contains(id)
                                    || crate::bplus_tree::tree_ids(nr@).contains(id))
                        // nl (the left half) keeps the subtree's leftmost leaf.
                        &&& crate::bplus_tree::tree_leaf_ids(nl@).len() >= 1
                        &&& crate::bplus_tree::tree_leaf_ids(nl@)[0] == crate::bplus_tree::tree_leaf_ids(cur@)[0]
                        // (weakening) min-key-preservation ensures clause REMOVED.
                    }
                }
            }),
        decreases h@,
    {
        let node = self.nodes.get_index(idx);
        proof { assert(self.arena()[idx.as_nat() as int] == node); }

        if L::is_leaf(&node) {
            // leaf base case: delegate (cur is a Leaf here, so h == 0).
            proof {
                // arena[idx] is a leaf and binds cur@ ⟹ cur@ is a Leaf ⟹ height 0.
                match cur@ {
                    Tree::Leaf { .. } => {}
                    Tree::Inner { .. } => {
                        assert(!L::is_leaf_spec(self.arena()[idx.as_nat() as int]));  // binds Inner arm
                        assert(false);
                    }
                }
                assert(h@ == 0);  // tree_height(Leaf) == 0
            }
            return self.insert_rec_leaf(idx, &node, key, kw, cur, h, succ, is_root);
        }

        // -- internal node: descend, recurse, absorb/split ------------------
        let ghost gseps = match cur@ { Tree::Inner { seps, .. } => seps, _ => Seq::empty() };
        let ghost gkids = match cur@ { Tree::Inner { kids, .. } => kids, _ => Seq::empty() };
        let ghost gid = idx.as_nat();
        proof {
            match cur@ {
                Tree::Inner { id, seps, kids } => { assert(id == gid && seps == gseps && kids == gkids); }
                Tree::Leaf { .. } => { assert(false); }
            }
            // relax cur's wf to root-form for lemma_inner_facts (needs is_root=true);
            // the non-root form (is_root@==false) is strictly stronger.
            if !is_root@ {
                crate::bplus_tree::lemma_tree_wf_relax_root(cur@, h@, L::leaf_cap_spec(), L::key_cap_spec());
            }
            lemma_inner_facts::<L>(self.arena(), gid, gseps, gkids, h@);
        }
        let n = L::count(&node);
        proof { assert(n as nat == gseps.len()); }

        // cp = find_gt(seps, key): the O(log n) verified binary search, whose
        // `ensures` IS the separator characterization the descent step needs.
        // (`lemma_inner_facts` above already gave node_wf + !is_leaf; this adds
        // the sorted-view precondition. Production: `S::find_gt` at bplus.rs:653.)
        proof { lemma_tree_wf_sorted_seps_view::<L>(self.arena(), cur@, gid, node); }
        let cp = self.find_child(&node, kw);
        // find_gt characterization: [0..cp) <= key, [cp..) > key, lifted from
        // find_child's key-view postcondition onto the ghost separators.
        proof {
            assert(cp as nat <= gseps.len());
            assert forall|j: int| 0 <= j < cp implies gseps[j] <= key.id_nat() by {
                assert(L::keys_view(node)[j].as_nat() == gseps[j]);
            }
            assert forall|i: int| cp <= i < gseps.len() implies key.id_nat() < gseps[i] by {
                assert(L::keys_view(node)[i].as_nat() == gseps[i]);
            }
            crate::bplus_tree::lemma_descent_step(gid, gseps, gkids, key.id_nat(), cp as int, h@,
                L::leaf_cap_spec(), L::key_cap_spec(), is_root@);
            lemma_inner_binds_child::<L>(self.arena(), gid, gseps, gkids, cp as int);
        }

        let child_idx = L::child(&node, cp);
        let ghost gc = gkids[cp as int];
        // child's successor: first leaf of next child, or this node's succ.
        let ghost child_succ = if cp + 1 < gkids.len() {
            crate::bplus_tree::tree_leaf_ids(gkids[cp as int + 1])[0]
        } else {
            succ@
        };
        proof {
            assert(child_idx.as_nat() == L::child_view(node, cp as int));
            assert(child_idx.as_nat() == crate::bplus_tree::tree_root_id(gc));
            // child subtree_wf at h-1, succ = child_succ: from cur's subtree_wf.
            // relax cur to root-form (the child projection is is_root-independent).
            if !is_root@ {
                crate::bplus_tree::lemma_tree_wf_relax_root(cur@, h@, L::leaf_cap_spec(), L::key_cap_spec());
            }
            lemma_inner_child_subtree_wf::<K, L, S, TRACK>(self.arena(), cur@, h@, succ@, cp as int);
            // tree_height(gc) == h-1 (child wf at h-1 ⟹ its height is h-1).
            crate::bplus_tree::lemma_forest_wf_at(gkids, (h@ - 1) as nat,
                L::leaf_cap_spec(), L::key_cap_spec(), cp as int);
            crate::bplus_tree::lemma_tree_wf_height(gc, (h@ - 1) as nat,
                L::leaf_cap_spec(), L::key_cap_spec(), false);
        }

        let ghost arena1 = self.arena();
        proof {
            // budget for the child: self.arena() unchanged so far, and
            // len + (h-1) + 2 == old.len + h + 1 < old.len + h + 2 < max_nat.
            assert(arena1 == old(self).arena());  // nothing mutated before the recursion
            assert(self.arena().len() == old(self).arena().len());
            assert(h@ >= 1);  // internal node ⟹ height >= 1
        }
        // the child is genuinely non-root, so it carries the stronger non-root wf.
        let (added, csplit, ncl, ncr) = self.insert_rec(child_idx, key, kw,
            Ghost(gc), Ghost((h@ - 1) as nat), Ghost(child_succ), Ghost(false));
        let ghost arena2 = self.arena();
        proof {
            // child grew the arena by at most (h-1)+1 == h.
            assert(arena2.len() <= arena1.len() + h@);
        }

        // The recursion mutated only inside tree_ids(gc); the parent node and the
        // sibling subtrees are untouched in arena2 vs arena1. Frame facts shared
        // by both branches:
        proof {
            // the parent node `node` at gid is unchanged (gid not in tree_ids(gc),
            // since tree_disjoint(cur) puts gid outside every child footprint).
            crate::bplus_tree::lemma_node_id_not_in_child::<>(cur@, cp as int);
            assert(self.arena()[gid as int] == node);  // arena grew + gid < arena1.len()
        }

        match csplit {
            None => {
                // -- absorb: child became ncl@ (same root id) ---------------
                let ghost nkids = gkids.update(cp as int, ncl@);
                let ghost nt = Tree::Inner { id: gid, seps: gseps, kids: nkids };
                proof {
                    // bridge the recursion's frame ensures to reconstruct_absorb's
                    // agreement precondition (outside tree_ids(gc)). gc == gkids[cp].
                    assert(gc == gkids[cp as int]);
                    assert forall|id: nat| #![trigger crate::bplus_tree::tree_ids(cur@).contains(id)] #![trigger arena1[id as int]] #![trigger arena2[id as int]] crate::bplus_tree::tree_ids(cur@).contains(id)
                        && !crate::bplus_tree::tree_ids(gkids[cp as int]).contains(id)
                        implies arena1[id as int] == arena2[id as int] by {
                        // id in tree_ids(cur) ⟹ id < arena1.len() (binds in-range);
                        // recursion frame: outside tree_ids(gc) ⟹ unchanged.
                        lemma_tree_id_in_range::<L>(arena1, cur@, id);
                    }
                    // (weakening) ncl min-preservation bridge REMOVED.
                    reconstruct_absorb::<K, L, S, TRACK>(
                        Ghost(arena1), Ghost(arena2), Ghost(cur@), Ghost(ncl@),
                        Ghost(gid), Ghost(gseps), Ghost(gkids), Ghost(cp as int),
                        Ghost(h@), Ghost(succ@), Ghost(child_succ), key, Ghost(node), is_root);
                    // frame ensures of insert_rec: slots outside tree_ids(cur)
                    // unchanged. arena2 == final; outside tree_ids(cur) ⊇ outside
                    // tree_ids(gc) handled by recursion; the parent node gid is in
                    // tree_ids(cur) so it's allowed to be touched (it wasn't).
                    assert(self.arena() == arena2);
                    assert(self.arena().len() <= old(self).arena().len() + h@ + 1);
                    assert forall|i: int| 0 <= i < arena1.len()
                        && !crate::bplus_tree::tree_ids(cur@).contains(i as nat)
                        implies self.arena()[i] == #[trigger] arena1[i] by {
                        // contrapositive of subset: i outside tree_ids(cur) ⟹ outside
                        // tree_ids(gc); then the recursion's frame ensures unchanged.
                        if crate::bplus_tree::tree_ids(gc).contains(i as nat) {
                            lemma_child_ids_subset_tree::<L>(cur@, cp as int, i as nat);
                            assert(crate::bplus_tree::tree_ids(cur@).contains(i as nat));  // contradiction
                        }
                        assert(!crate::bplus_tree::tree_ids(gc).contains(i as nat));
                        // recursion frame ensures: arena2[i] == arena1[i].
                    }
                    // (F0) the None-arm postcondition for nt, from reconstruct_absorb's
                    // ensures (footprint subset+freshness + first-leaf preservation).
                    // arena1 == old(self).arena() here (nothing mutated pre-recursion),
                    // so the freshness bound matches the outer postcondition's.
                    assert(arena1 == old(self).arena());
                    assert(crate::bplus_tree::tree_ids(cur@).subset_of(crate::bplus_tree::tree_ids(nt)));
                    assert(crate::bplus_tree::tree_leaf_ids(nt)[0] == crate::bplus_tree::tree_leaf_ids(cur@)[0]);
                    // (weakening) min-key bridge assert REMOVED.
                    // `added`: recursion gives added == !tree_keys(gc).contains(key);
                    // descent (key ∈ cur ⟺ key ∈ gc, via lemma_descent_step at the
                    // top) lifts it to !tree_keys(cur).contains(key).
                    assert(crate::bplus_tree::tree_contains(cur@, key.id_nat())
                        == crate::bplus_tree::tree_contains(gc, key.id_nat()));
                    assert(added == !crate::bplus_tree::tree_keys(cur@).contains(key.id_nat()));

                    // (M6) delta: child cp absorbed (gc -> ncl), siblings frame.
                    // recursion gave: arena2.len() + nc(gc) == arena1.len() + nc(ncl).
                    // nt == Inner{gid, gseps, gkids.update(cp, ncl)}, cur == Inner{..gkids}.
                    // node_count(Inner) == 1 + forest_node_count(kids); the update
                    // lemma shifts the forest count by exactly nc(ncl) - nc(gc).
                    crate::bplus_tree::lemma_forest_node_count_update(gkids, cp as int, ncl@);
                    assert(gc == gkids[cp as int]);
                    assert(nkids == gkids.update(cp as int, ncl@));
                    assert(crate::bplus_tree::node_count(nt)
                        == 1 + crate::bplus_tree::forest_node_count(nkids));
                    assert(crate::bplus_tree::node_count(cur@)
                        == 1 + crate::bplus_tree::forest_node_count(gkids));
                    assert(self.arena().len() + crate::bplus_tree::node_count(cur@)
                        == old(self).arena().len() + crate::bplus_tree::node_count(nt));
                }
                (added, None, Ghost(nt), cur)
            }
            Some((sep, rid)) => {
                // child cp split into (ncl@ at idx, ncr@ at rid), separated by
                // `sep`. Insert (sep, rid) into this parent at child-pos cp+1.
                let mut pnode = self.nodes.get_index(idx);
                let kc = L::key_cap();
                proof {
                    assert(self.arena()[gid as int] == pnode);
                    assert(n as nat == L::count_spec(pnode));   // == gseps.len()
                    assert(!L::is_leaf_spec(pnode));
                    assert(L::node_wf(pnode));
                }
                if n < kc {
                    // parent has room: insert (sep, rid) at (cp, cp+1).
                    let ghost pre = pnode;  // == arena1[gid] (the node read by get)
                    proof { assert(pre == arena1[gid as int]); }
                    crate::bplus_layout::internal_insert_at::<L>(&mut pnode, cp, sep, rid);
                    proof {
                        // internal_insert_at ensures relate pnode to `pre`.
                        assert(L::keys_view(pnode) == L::keys_view(pre).insert(cp as int, sep));
                        assert(!L::is_leaf_spec(pnode));
                        assert(L::count_spec(pnode) == L::count_spec(pre) + 1);
                        assert(L::count_spec(pre) == gseps.len());
                    }
                    let ghost arena_rec = self.arena();  // after recursion, before parent set
                    let ghost rid_nat = rid.as_nat();
                    self.nodes.set_index(idx, pnode);
                    proof {
                        assert(self.arena()[gid as int] == pnode);
                        // self.arena() == arena_rec.update(gid, pnode): only gid changed.
                        assert(self.arena() =~= arena_rec.update(gid as int, pnode));
                        // gid ∉ tree_ids(ncl)/tree_ids(ncr): gid is the parent id, not in
                        // child cp's footprint (tree_disjoint), and ncl/ncr old ids ⊆
                        // child cp's footprint while their fresh ids are >= arena1.len() > gid.
                        crate::bplus_tree::lemma_node_id_not_in_child::<>(cur@, cp as int);
                        // gid is an existing node and ∉ child cp's footprint.
                        lemma_tree_id_in_range::<L>(arena1, cur@, gid);
                        assert(crate::bplus_tree::tree_ids(cur@).contains(gid));  // gid is cur's root
                        assert(gid < arena1.len());
                        assert(!crate::bplus_tree::tree_ids(gkids[cp as int]).contains(gid));
                        // F1 (recursion's Some ensures) contrapositive: gid ∉ child cp's
                        // ids and gid < arena1.len() ⟹ gid ∉ tree_ids(ncl), ∉ tree_ids(ncr).
                        if crate::bplus_tree::tree_ids(ncl@).contains(gid) {
                            assert(crate::bplus_tree::tree_ids(gkids[cp as int]).contains(gid)
                                || gid >= arena1.len());  // F1 at id==gid
                            assert(false);
                        }
                        if crate::bplus_tree::tree_ids(ncr@).contains(gid) {
                            assert(crate::bplus_tree::tree_ids(gkids[cp as int]).contains(gid)
                                || gid >= arena1.len());
                            assert(false);
                        }
                        assert(!crate::bplus_tree::tree_ids(ncl@).contains(gid));
                        assert(!crate::bplus_tree::tree_ids(ncr@).contains(gid));
                        // frame ncl/ncr's subtree_wf across the single-slot set
                        // (gid ∉ their footprints), via the dedicated update-frame lemma.
                        lemma_subtree_wf_frame_update::<K, L, S, TRACK>(arena_rec, ncl@, gid, pnode,
                            (h@ - 1) as nat, crate::bplus_tree::tree_leaf_ids(ncr@)[0]);
                        lemma_subtree_wf_frame_update::<K, L, S, TRACK>(arena_rec, ncr@, gid, pnode,
                            (h@ - 1) as nat, child_succ);
                        assert(self.arena() =~= arena_rec.update(gid as int, pnode));
                    }
                    let ghost nseps = gseps.insert(cp as int, sep.as_nat());
                    let ghost nkids = gkids.update(cp as int, ncl@).insert(cp as int + 1, ncr@);
                    let ghost nt = Tree::Inner { id: gid, seps: nseps, kids: nkids };
                    proof {
                        // ncl wf at h-1 non-root ⟹ it carries >= 1 key (the split's
                        // left half is non-empty), needed for the splice's strict
                        // separator sortedness.
                        L::lemma_arena_capacity();  // 1 <= leaf_cap
                        crate::bplus_tree::lemma_tree_keys_nonempty(ncl@, (h@ - 1) as nat,
                            L::leaf_cap_spec(), L::key_cap_spec());
                        // (weakening) gc min bridge REMOVED.
                        reconstruct_child_split_absorb::<K, L, S, TRACK>(
                            Ghost(arena1), Ghost(self.arena()), Ghost(cur@),
                            Ghost(ncl@), Ghost(ncr@), Ghost(gid), Ghost(gseps), Ghost(gkids),
                            Ghost(cp as int), Ghost(h@), Ghost(succ@), Ghost(child_succ),
                            key, sep, rid, Ghost(pnode), is_root);
                        // frame: slots outside tree_ids(cur) unchanged. The recursion
                        // touched only inside tree_ids(gkids[cp]) ⊆ tree_ids(cur) plus
                        // the fresh rid (>= old len, outside the i<old.len guard).
                        reconstruct_split_frame::<K, L, S, TRACK>(
                            Ghost(arena1), Ghost(self.arena()), Ghost(cur@), Ghost(gkids), Ghost(cp as int));
                        assert(self.arena().len() <= old(self).arena().len() + h@ + 1);
                        // (F0) None-arm postcondition for nt, from
                        // reconstruct_child_split_absorb's ensures. arena1 ==
                        // old(self).arena() (nothing mutated pre-recursion).
                        assert(arena1 == old(self).arena());
                        assert(crate::bplus_tree::tree_ids(cur@).subset_of(crate::bplus_tree::tree_ids(nt)));
                        assert(crate::bplus_tree::tree_leaf_ids(nt)[0] == crate::bplus_tree::tree_leaf_ids(cur@)[0]);
                        // (weakening) min-key bridge assert REMOVED.
                        // `added`: recursion's Some result carries `added`; descent
                        // (key ∈ cur ⟺ key ∈ gc) lifts the membership to cur.
                        assert(crate::bplus_tree::tree_contains(cur@, key.id_nat())
                            == crate::bplus_tree::tree_contains(gc, key.id_nat()));
                        assert(added == !crate::bplus_tree::tree_keys(cur@).contains(key.id_nat()));

                        // (M6) delta: child cp split (gc -> ncl + ncr), absorbed into
                        // this parent with room (set in place, no parent-level push).
                        // recursion (Some): arena_rec.len() + nc(gc) == arena1.len()
                        //   + nc(ncl) + nc(ncr); the parent set keeps arena len.
                        // nkids == gkids.update(cp, ncl).insert(cp+1, ncr): update
                        // shifts by nc(ncl)-nc(gc), insert adds nc(ncr).
                        crate::bplus_tree::lemma_forest_node_count_update(gkids, cp as int, ncl@);
                        crate::bplus_tree::lemma_forest_node_count_insert(
                            gkids.update(cp as int, ncl@), cp as int + 1, ncr@);
                        assert(gc == gkids[cp as int]);
                        assert(crate::bplus_tree::node_count(nt)
                            == 1 + crate::bplus_tree::forest_node_count(nkids));
                        assert(crate::bplus_tree::node_count(cur@)
                            == 1 + crate::bplus_tree::forest_node_count(gkids));
                        assert(self.arena().len() + crate::bplus_tree::node_count(cur@)
                            == old(self).arena().len() + crate::bplus_tree::node_count(nt));
                    }
                    (added, None, Ghost(nt), cur)
                } else {
                    // parent full: split it. internal_split_at distributes the
                    // combined (seps+sep, children with ncl@cp replaced & ncr at
                    // cp+1) into a left half (kept at idx) and a right half (a
                    // freshly-allocated internal node), promoting the median.
                    let ghost arena_rec = self.arena();  // post-recursion, pre-mutation
                    let ghost pnode_g = pnode;
                    proof {
                        // gid unchanged by the recursion (stayed in child cp's subtree):
                        // arena_rec[gid] == arena1[gid] == pnode (the node read at `get`).
                        assert(arena_rec[gid as int] == pnode);
                        // pnode == arena1[gid]: the recursion didn't touch gid (gid ∉
                        // tree_ids(gc) by tree_disjoint, and gc is where it mutated).
                        crate::bplus_tree::lemma_node_id_not_in_child::<>(cur@, cp as int);
                        lemma_tree_id_in_range::<L>(arena1, cur@, gid);
                        assert(crate::bplus_tree::tree_ids(cur@).contains(gid));
                        assert(!crate::bplus_tree::tree_ids(gkids[cp as int]).contains(gid));
                        assert(arena1[gid as int] == pnode);  // frame: gid outside gc
                    }
                    let (pl, pr, promoted) = L::internal_split_at(&pnode, cp, sep, rid);
                    self.nodes.set_index(idx, pl);
                    let new_int = self.nodes.len();
                    proof {
                        // new_int == arena_rec.len() == rid for the push (the fresh slot).
                        assert(new_int.as_nat() == arena_rec.len());
                    }
                    self.nodes.push(pr);

                    // ghost halves of the parent split. cseps/ckids are the
                    // combined arrangement; imid the split point.
                    let ghost cseps = gseps.insert(cp as int, sep.as_nat());
                    let ghost ckids = gkids.update(cp as int, ncl@).insert(cp as int + 1, ncr@);
                    let ghost imid = L::isplit_mid_spec();
                    let ghost lt = Tree::Inner {
                        id: gid,
                        seps: cseps.subrange(0, imid as int),
                        kids: ckids.subrange(0, imid as int + 1),
                    };
                    let ghost rt = Tree::Inner {
                        id: new_int.as_nat(),
                        seps: cseps.subrange(imid as int + 1, cseps.len() as int),
                        kids: ckids.subrange(imid as int + 1, ckids.len() as int),
                    };
                    proof {
                        // arena2 == arena_rec.update(gid, pl).push(pr).
                        assert(self.arena() =~= arena_rec.update(gid as int, pl).push(pr));
                        // ncl/ncr non-empty (wf at h-1 non-root carry >= 1 key); the
                        // recursion's Some ensures only states it for ncr, so derive ncl.
                        L::lemma_arena_capacity();
                        crate::bplus_tree::lemma_tree_keys_nonempty(ncl@, (h@ - 1) as nat,
                            L::leaf_cap_spec(), L::key_cap_spec());
                        // ncl's leftmost leaf is non-empty (the half_links / footprint need it).
                        crate::bplus_tree::lemma_tree_leaf_ids_nonempty(ncl@, (h@ - 1) as nat,
                            L::leaf_cap_spec(), L::key_cap_spec(), false);
                        // pnode_g == arena1[gid] (recursion left gid untouched; shown above)
                        // and == arena_rec[gid]; internal_split_at read &pnode == pnode_g.
                        assert(pnode_g == arena1[gid as int]);
                        assert(L::node_wf(pnode_g));
                        // internal_split_at's tuple ensures relate pl/pr to keys_view(pnode).
                        // insert(cp, sep) — restate the count/keys/child views the lemma wants.
                        L::lemma_isplit_mid();
                        reconstruct_parent_split::<K, L, S, TRACK>(
                            Ghost(arena1), Ghost(arena_rec), Ghost(self.arena()), Ghost(cur@),
                            Ghost(gseps), Ghost(gkids), Ghost(cp as int), Ghost(ncl@), Ghost(ncr@),
                            Ghost(child_succ), Ghost(lt), Ghost(rt), sep, rid,
                            Ghost(gid), Ghost(h@), Ghost(succ@), key, new_int,
                            Ghost(pnode_g), Ghost(pl), Ghost(pr));
                        assert(self.arena().len() <= old(self).arena().len() + h@ + 1);
                        // `added`: recursion's Some carries `added == !contains(gc)`;
                        // descent lifts the membership to cur.
                        assert(crate::bplus_tree::tree_contains(cur@, key.id_nat())
                            == crate::bplus_tree::tree_contains(gc, key.id_nat()));
                        assert(added == !crate::bplus_tree::tree_keys(cur@).contains(key.id_nat()));

                        // (M6) delta: child cp split (gc -> ncl+ncr) AND this parent
                        // then split (cur -> lt + rt). arena: set(gid,pl) in place +
                        // push(pr) == +1 over arena_rec; child's Some delta gives
                        // arena_rec.len() + nc(gc) == old.len() + nc(ncl) + nc(ncr).
                        // node counts: ckids == gkids.update(cp,ncl).insert(cp+1,ncr);
                        // lt+rt partition ckids at imid+1 (+2 roots).
                        crate::bplus_tree::lemma_forest_node_count_update(gkids, cp as int, ncl@);
                        crate::bplus_tree::lemma_forest_node_count_insert(
                            gkids.update(cp as int, ncl@), cp as int + 1, ncr@);
                        crate::bplus_tree::lemma_forest_node_count_split(ckids, imid as int + 1);
                        assert(ckids.subrange(0, imid as int + 1) == lt->Inner_kids);
                        assert(ckids.subrange(imid as int + 1, ckids.len() as int) == rt->Inner_kids);
                        assert(crate::bplus_tree::node_count(lt)
                            == 1 + crate::bplus_tree::forest_node_count(lt->Inner_kids));
                        assert(crate::bplus_tree::node_count(rt)
                            == 1 + crate::bplus_tree::forest_node_count(rt->Inner_kids));
                        assert(crate::bplus_tree::node_count(cur@)
                            == 1 + crate::bplus_tree::forest_node_count(gkids));
                        assert(gc == gkids[cp as int]);
                        assert(self.arena().len() == arena_rec.len() + 1);
                        assert(self.arena().len() + crate::bplus_tree::node_count(cur@)
                            == old(self).arena().len()
                                + crate::bplus_tree::node_count(lt)
                                + crate::bplus_tree::node_count(rt));
                    }
                    (added, Some((promoted, new_int)), Ghost(lt), Ghost(rt))
                }
            }
        }
    }
}

// ===== LAYER 3: cursor + seek + traversal soundness =====


/// For a strictly-sorted model, `seek_target_idx(model, t)` is exactly the split
/// point: `model[i] < t` for `i < idx` and `t <= model[i]` for `idx <= i`. The
/// characterization `seek` and `seek_leaf` are specified against.
pub(crate) proof fn lemma_seek_target_idx_split(model: Seq<nat>, t: nat)
    requires crate::bplus_tree::strictly_sorted(model),
    ensures
        ({
            let idx = seek_target_idx(model, t);
            &&& 0 <= idx <= model.len()
            &&& (forall|i: int| 0 <= i < idx ==> #[trigger] model[i] < t)
            &&& (forall|i: int| idx <= i < model.len() ==> t <= #[trigger] model[i])
        }),
    decreases model.len(),
{
    if model.len() == 0 {
    } else if model[0] < t {
        let df = model.drop_first();
        assert(crate::bplus_tree::strictly_sorted(df)) by {
            assert forall|i: int, j: int| 0 <= i < j < df.len() implies #[trigger] df[i] < #[trigger] df[j] by {
                assert(df[i] == model[i + 1] && df[j] == model[j + 1]);
            }
        }
        lemma_seek_target_idx_split(df, t);
        let idx = seek_target_idx(model, t);
        assert(idx == 1 + seek_target_idx(df, t));
        assert forall|i: int| 0 <= i < idx implies #[trigger] model[i] < t by {
            if i == 0 {} else { assert(df[i - 1] == model[i]); }
        }
        assert forall|i: int| idx <= i < model.len() implies t <= #[trigger] model[i] by {
            assert(df[i - 1] == model[i]);
        }
    } else {
        // model[0] >= t; strictly-sorted ⟹ model[i] >= model[0] >= t for all i.
        assert forall|i: int| 0 <= i < model.len() implies t <= #[trigger] model[i] by {
            if i > 0 { assert(model[0] < model[i]); }
        }
    }
}

/// A split point of a strictly-sorted model is unique: if `r` satisfies the same
/// "left `< t`, right `>= t`" characterization as `seek_target_idx`, then `r ==
/// seek_target_idx(model, t)`. Lets seek/seek_leaf prove they reach the target
/// index by exhibiting ANY split point (e.g. chain_offset(m) + leaf_find_ge).
pub(crate) proof fn lemma_seek_target_idx_unique(model: Seq<nat>, t: nat, r: int)
    requires
        crate::bplus_tree::strictly_sorted(model),
        0 <= r <= model.len(),
        forall|i: int| 0 <= i < r ==> #[trigger] model[i] < t,
        forall|i: int| r <= i < model.len() ==> t <= #[trigger] model[i],
    ensures r == seek_target_idx(model, t),
{
    lemma_seek_target_idx_split(model, t);
    let idx = seek_target_idx(model, t);
    // both r and idx split the sorted seq; if r < idx then model[r] < t (idx side)
    // AND t <= model[r] (r side at r, since r < idx <= len) — contradiction; sym.
    if r < idx {
        assert(model[r] < t);       // idx's left side at r (r < idx)
        assert(t <= model[r]);      // r's right side at r (r <= r < len)
    } else if idx < r {
        assert(model[idx] < t);     // r's left side at idx (idx < r)
        assert(t <= model[idx]);    // idx's right side at idx
    }
}

/// Incremental sorted cursor over the leaf-link chain — the leapfrog-join
/// iterator. `seek(target)` positions at the first key `>= target`; `key()`
/// reads the current key (or `None` past the end); `step()` advances. This is
/// production's `BPlusCursor`, fast path included: a `seek` to a key in the
/// current or the immediately-next leaf is O(log leaf) along the chain, with a
/// full root descent only as the fallback — the whole reason the leaf-link
/// chain exists. `node == NIL` marks "exhausted". TEST-FIRST exec; the
/// in-order-enumeration theorem (sound for leapfrog) is proven once the insert
/// proof lands.
pub struct BPlusCursor<'a, K, L, S, const TRACK: bool>
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
{
    pub(crate) tree: &'a BPlusTreeSet<K, L, S, TRACK>,
    /// Current leaf arena index, or NIL (`max_nat - 1`) when exhausted.
    pub(crate) node: L::ArenaIdx,
    /// Position within the current leaf.
    pub(crate) pos: usize,
    /// Ghost: the cursor's position in the IN-ORDER MODEL. `(node, pos)` is the
    /// executable realization of model index `gidx`; `gidx == model.len()` marks
    /// "exhausted" (`node == NIL`). The cursor's `wf` ties the two together, so
    /// `key()`/`step()` can be specified against the model rather than the arena.
    /// (Read only by spec code, which plain builds erase.)
    #[allow(dead_code)]
    pub(crate) gidx: Ghost<int>,
    /// Ghost: which chain leaf `node` is — its position in `tree_leaf_ids`. Pins
    /// `node == tree_leaf_ids(tree@)[gleaf]` so we needn't `choose` it.
    #[allow(dead_code)]
    pub(crate) gleaf: Ghost<int>,
    pub(crate) _k: core::marker::PhantomData<K>,
}

/// `chain_keys` distributes over `++` of leaf-id lists.
pub(crate) proof fn lemma_chain_keys_concat<L: NodeLayout>(arena: Seq<L::Node>, a: Seq<nat>, b: Seq<nat>)
    ensures chain_keys::<L>(arena, a + b) == chain_keys::<L>(arena, a) + chain_keys::<L>(arena, b),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + b =~= b);
        assert(chain_keys::<L>(arena, a) =~= Seq::<nat>::empty());
    } else {
        // peel a[0]: (a+b).drop_first() == a.drop_first() + b, (a+b)[0] == a[0].
        assert((a + b)[0] == a[0]);
        assert((a + b).drop_first() =~= a.drop_first() + b);
        lemma_chain_keys_concat::<L>(arena, a.drop_first(), b);
    }
}

/// B2 (subtree form): for a `binds`-ing subtree `t`, the chain-key reading over
/// `t`'s in-order leaf ids equals `t`'s in-order model `tree_keys(t)`. Structural
/// induction: a leaf reads its own keys (binds leaf arm); an internal node's
/// leaf-ids and model both split child-by-child, and `chain_keys` /
/// `forest_keys` distribute over the per-child concatenation identically.
pub(crate) proof fn lemma_chain_keys_eq_model<L: NodeLayout>(arena: Seq<L::Node>, t: Tree)
    requires binds::<L>(arena, t),
    ensures chain_keys::<L>(arena, crate::bplus_tree::tree_leaf_ids(t)) == crate::bplus_tree::tree_keys(t),
    decreases t,
{
    match t {
        Tree::Leaf { id, keys } => {
            // tree_leaf_ids == [id]; chain_keys([id]) == leaf_word_keys(id) ++ [].
            assert(crate::bplus_tree::tree_leaf_ids(t) =~= seq![id]);
            assert(seq![id].drop_first() =~= Seq::<nat>::empty());
            // leaf_word_keys(id) == keys: binds leaf arm gives count == keys.len()
            // and keys_view[i].as_nat() == keys[i].
            assert(L::count_spec(arena[id as int]) == keys.len());
            L::lemma_keys_view_len(arena[id as int]);
            let lwk = leaf_word_keys::<L>(arena, id);
            assert(lwk.len() == keys.len());
            assert forall|i: int| 0 <= i < keys.len() implies lwk[i] == keys[i] by {
                assert(L::keys_view(arena[id as int])[i].as_nat() == keys[i]);  // binds
            }
            assert(lwk =~= keys);
            // chain_keys([id]) unfolds: leaf_word_keys(id) ++ chain_keys([]).
            assert(seq![id][0] == id);
            assert(chain_keys::<L>(arena, Seq::<nat>::empty()) =~= Seq::<nat>::empty());
            assert(chain_keys::<L>(arena, seq![id]) == lwk + chain_keys::<L>(arena, seq![id].drop_first()));
            assert(chain_keys::<L>(arena, seq![id]) =~= lwk);
            assert(crate::bplus_tree::tree_keys(t) == keys);
        }
        Tree::Inner { id, seps, kids } => {
            lemma_chain_keys_eq_model_forest::<L>(arena, kids);
            assert(crate::bplus_tree::tree_leaf_ids(t) == crate::bplus_tree::forest_leaf_ids(kids));
            assert(crate::bplus_tree::tree_keys(t) == crate::bplus_tree::forest_keys(kids));
        }
    }
}

/// Forest companion: `chain_keys(forest_leaf_ids(kids)) == forest_keys(kids)`,
/// given every child binds. Induction on `kids`, using `lemma_chain_keys_concat`
/// to split the head child's chain off the tail (mirroring how both
/// `forest_leaf_ids` and `forest_keys` cons).
pub(crate) proof fn lemma_chain_keys_eq_model_forest<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>)
    requires forest_binds_l::<L>(arena, kids),
    ensures chain_keys::<L>(arena, crate::bplus_tree::forest_leaf_ids(kids)) == crate::bplus_tree::forest_keys(kids),
    // mutually recursive with lemma_chain_keys_eq_model (decreases t); the pair
    // must use type-compatible datatype measures, so `decreases kids` (Verus
    // orders the Seq<Tree> by element height), NOT `kids.len()` (an int).
    decreases kids,
{
    if kids.len() == 0 {
        assert(crate::bplus_tree::forest_leaf_ids(kids) =~= Seq::<nat>::empty());
        assert(crate::bplus_tree::forest_keys(kids) =~= Seq::<nat>::empty());
    } else {
        let df = kids.drop_first();
        // forest_leaf_ids(kids) == tree_leaf_ids(kids[0]) ++ forest_leaf_ids(df).
        crate::bplus_tree::lemma_forest_leaf_ids_cons(kids);
        crate::bplus_tree::lemma_forest_keys_cons(kids);
        // head binds, tail binds (forest_binds_l cons).
        assert(binds::<L>(arena, kids[0]));
        assert(forest_binds_l::<L>(arena, df));
        // chain_keys distributes over the head/tail leaf-id split.
        lemma_chain_keys_concat::<L>(arena, crate::bplus_tree::tree_leaf_ids(kids[0]),
            crate::bplus_tree::forest_leaf_ids(df));
        lemma_chain_keys_eq_model::<L>(arena, kids[0]);   // head: chain == tree_keys(kids[0])
        lemma_chain_keys_eq_model_forest::<L>(arena, df); // tail: by IH
    }
}

/// B2 (whole-tree): for a `wf` tree, walking the leaf-link chain from the
/// leftmost leaf reads exactly the sorted model. Combines `lemma_chain_keys_eq_
/// model` (chain reading == `tree_keys`) with B1 (`tree_wf ⟹ strictly_sorted`),
/// so the enumerated key sequence is the set in ascending order, no gaps/dups.
/// The first leaf is `tree_leaf_ids(tree@)[0]` and the chain is NIL-terminated
/// (`leaf_links_ok`), so a client walk reproduces this exact sequence.
pub(crate) proof fn lemma_chain_yields_sorted_model<K, L, S, const TRACK: bool>(t: &BPlusTreeSet<K, L, S, TRACK>)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires t.wf(),
    ensures
        chain_keys::<L>(t.arena(), crate::bplus_tree::tree_leaf_ids(t.tree@)) == crate::bplus_tree::tree_keys(t.tree@),
        crate::bplus_tree::strictly_sorted(crate::bplus_tree::tree_keys(t.tree@)),
        leaf_links_ok::<L>(t.arena(), t.tree@),
{
    lemma_chain_keys_eq_model::<L>(t.arena(), t.tree@);  // binds(arena, tree@) from wf
    crate::bplus_tree::lemma_tree_wf_sorted(t.tree@,
        crate::bplus_tree::tree_height(t.tree@), L::leaf_cap_spec(), L::key_cap_spec(), true);
}

/// `chain_keys(lids)` at the slice for leaf `m` projects to that leaf's keys:
/// for `0 <= p < |leaf m|`, `chain_keys(lids)[chain_offset(m) + p] ==
/// leaf_word_keys(lids[m])[p]`, and the offset+len stays in range. The model
/// analogue of `lemma_forest_leaf_ids_slice`; induction on `m` peeling the head.
pub(crate) proof fn lemma_chain_keys_slice<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>, m: int)
    requires 0 <= m < lids.len(),
    ensures
        chain_offset::<L>(arena, lids, m) + leaf_word_keys::<L>(arena, lids[m]).len()
            <= chain_keys::<L>(arena, lids).len(),
        forall|p: int| 0 <= p < leaf_word_keys::<L>(arena, lids[m]).len() ==>
            (#[trigger] chain_keys::<L>(arena, lids)[chain_offset::<L>(arena, lids, m) + p])
                == leaf_word_keys::<L>(arena, lids[m])[p],
    decreases m,
{
    let ck = chain_keys::<L>(arena, lids);
    let head = leaf_word_keys::<L>(arena, lids[0]);
    let df = lids.drop_first();
    // ck == head ++ chain_keys(df)  (the chain_keys cons).
    assert(ck == head + chain_keys::<L>(arena, df));
    if m == 0 {
        assert(chain_offset::<L>(arena, lids, 0) == 0);
        assert forall|p: int| 0 <= p < leaf_word_keys::<L>(arena, lids[0]).len() implies
            ck[0 + p] == leaf_word_keys::<L>(arena, lids[0])[p] by {
            assert(ck[p] == head[p]);
        }
    } else {
        // recurse on df at m-1; df[m-1] == lids[m], and df's chain is ck's tail.
        assert(df[m - 1] == lids[m]);
        lemma_chain_keys_slice::<L>(arena, df, m - 1);
        let cdf = chain_keys::<L>(arena, df);
        // chain_offset(lids, m) == head.len() + chain_offset(df, m-1).
        lemma_chain_offset_cons::<L>(arena, lids, m);
        let off_df = chain_offset::<L>(arena, df, m - 1);
        assert forall|p: int| 0 <= p < leaf_word_keys::<L>(arena, lids[m]).len() implies
            ck[chain_offset::<L>(arena, lids, m) + p] == leaf_word_keys::<L>(arena, lids[m])[p] by {
            // ck[head.len() + (off_df + p)] == cdf[off_df + p] == leaf m's p-th key.
            assert(cdf[off_df + p] == leaf_word_keys::<L>(arena, df[m - 1])[p]);  // IH
            assert(ck[head.len() + (off_df + p)] == cdf[off_df + p]);            // ck == head ++ cdf
            assert(chain_offset::<L>(arena, lids, m) == head.len() + off_df);
        }
    }
}

/// `chain_offset(lids, m) == |leaf 0| + chain_offset(lids.drop_first(), m-1)`
/// for `m >= 1`: the offset peels its head leaf the same way `chain_keys` does.
pub(crate) proof fn lemma_chain_offset_cons<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>, m: int)
    requires 1 <= m, m <= lids.len(),
    ensures
        chain_offset::<L>(arena, lids, m)
            == leaf_word_keys::<L>(arena, lids[0]).len()
                + chain_offset::<L>(arena, lids.drop_first(), m - 1),
    decreases m,
{
    let df = lids.drop_first();
    if m == 1 {
        assert(chain_offset::<L>(arena, df, 0) == 0);
        assert(chain_offset::<L>(arena, lids, 1)
            == chain_offset::<L>(arena, lids, 0) + leaf_word_keys::<L>(arena, lids[0]).len());
    } else {
        lemma_chain_offset_cons::<L>(arena, lids, m - 1);
        assert(df[m - 2] == lids[m - 1]);  // peeled-head index shift
    }
}

/// `chain_offset(lids, len) == chain_keys(arena, lids).len()`: summing all leaves'
/// key counts gives the full chain length. Induction peeling the head.
pub(crate) proof fn lemma_chain_offset_full<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>)
    ensures chain_offset::<L>(arena, lids, lids.len() as int) == chain_keys::<L>(arena, lids).len(),
    decreases lids.len(),
{
    if lids.len() == 0 {
        assert(chain_keys::<L>(arena, lids) =~= Seq::<nat>::empty());
    } else {
        let df = lids.drop_first();
        // chain_keys(lids) == leaf 0 ++ chain_keys(df); chain_offset(lids, len) ==
        // |leaf 0| + chain_offset(df, len-1)  (offset cons).
        lemma_chain_offset_cons::<L>(arena, lids, lids.len() as int);
        lemma_chain_offset_full::<L>(arena, df);
        assert(df.len() == lids.len() - 1);
    }
}

/// `chain_offset(lids, k) == chain_keys(lids.subrange(0, k)).len()` for any
/// prefix `k`: the offset counts exactly the model keys of the first `k` leaves.
/// Generalizes `lemma_chain_offset_full` (k == len); induction on `k`.
pub(crate) proof fn lemma_chain_offset_prefix<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>, k: int)
    requires 0 <= k <= lids.len(),
    ensures chain_offset::<L>(arena, lids, k) == chain_keys::<L>(arena, lids.subrange(0, k)).len(),
    decreases k,
{
    if k == 0 {
        assert(lids.subrange(0, 0) =~= Seq::<nat>::empty());
        assert(chain_keys::<L>(arena, lids.subrange(0, 0)) =~= Seq::<nat>::empty());
    } else {
        // chain_offset(k) == chain_offset(k-1) + |leaf (k-1)|  (offset def);
        // chain_keys(lids[0..k]) == chain_keys(lids[0..k-1]) ++ leaf_word_keys(lids[k-1]).
        lemma_chain_offset_prefix::<L>(arena, lids, k - 1);
        let pk = lids.subrange(0, k);
        let pk1 = lids.subrange(0, k - 1);
        assert(pk1 == pk.drop_last());
        assert(pk[k - 1] == lids[k - 1]);
        lemma_chain_keys_drop_last::<L>(arena, pk);
        assert(chain_offset::<L>(arena, lids, k)
            == chain_offset::<L>(arena, lids, k - 1) + leaf_word_keys::<L>(arena, lids[k - 1]).len());
    }
}

/// `chain_keys(s) == chain_keys(s.drop_last()) ++ leaf_word_keys(s.last())`: the
/// chain reading peels its LAST leaf (the dual of the cons def, peeling head).
pub(crate) proof fn lemma_chain_keys_drop_last<L: NodeLayout>(arena: Seq<L::Node>, s: Seq<nat>)
    requires s.len() >= 1,
    ensures chain_keys::<L>(arena, s)
        == chain_keys::<L>(arena, s.drop_last()) + leaf_word_keys::<L>(arena, s[s.len() - 1]),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s.drop_last() =~= Seq::<nat>::empty());
        assert(s.drop_first() =~= Seq::<nat>::empty());
        assert(chain_keys::<L>(arena, s) == leaf_word_keys::<L>(arena, s[0]) + chain_keys::<L>(arena, s.drop_first()));
    } else {
        let df = s.drop_first();
        // chain_keys(s) == leaf(s[0]) ++ chain_keys(df); recurse on df.
        lemma_chain_keys_drop_last::<L>(arena, df);
        assert(df.drop_last() =~= s.drop_last().drop_first());
        assert(df[df.len() - 1] == s[s.len() - 1]);
        assert(s.drop_last()[0] == s[0]);
        // chain_keys(s.drop_last()) == leaf(s[0]) ++ chain_keys(s.drop_last().drop_first()).
        assert(chain_keys::<L>(arena, s.drop_last())
            == leaf_word_keys::<L>(arena, s.drop_last()[0]) + chain_keys::<L>(arena, s.drop_last().drop_first()));
    }
}

/// The descent bridge: for an Inner tree `t`, the chain offset to child `cp`'s
/// region equals the model keys of the first `cp` children:
/// `chain_offset(tree_leaf_ids(t), leaf_id_offset(kids, cp)) ==
/// forest_keys(kids.subrange(0, cp)).len()`. Combines lemma_chain_offset_prefix
/// (offset == chain_keys prefix length), lemma_forest_leaf_ids_prefix (those
/// leaf ids ARE the sub-forest's), and B2 on the sub-forest kids[0..cp]
/// (chain_keys of its leaves == forest_keys). The accumulator law seek_leaf needs.
pub(crate) proof fn lemma_chain_offset_child<L: NodeLayout>(arena: Seq<L::Node>, t: Tree, cp: int)
    requires
        t is Inner,
        binds::<L>(arena, t),
        0 <= cp <= t->Inner_kids.len(),
    ensures
        chain_offset::<L>(arena, crate::bplus_tree::tree_leaf_ids(t),
            crate::bplus_tree::leaf_id_offset(t->Inner_kids, cp) as int)
            == crate::bplus_tree::forest_keys(t->Inner_kids.subrange(0, cp)).len(),
{
    let kids = t->Inner_kids;
    let lids = crate::bplus_tree::tree_leaf_ids(t);
    let off = crate::bplus_tree::leaf_id_offset(kids, cp) as int;
    assert(lids == crate::bplus_tree::forest_leaf_ids(kids));
    crate::bplus_tree::lemma_leaf_id_offset_bound(kids, cp);   // off <= |lids|
    lemma_chain_offset_prefix::<L>(arena, lids, off);          // offset == chain_keys(lids[0..off]).len
    crate::bplus_tree::lemma_forest_leaf_ids_prefix(kids, cp); // lids[0..off] == forest_leaf_ids(kids[0..cp])
    // B2 on the sub-forest: chain_keys(forest_leaf_ids(kids[0..cp])) == forest_keys(kids[0..cp]).
    assert(forest_binds_l::<L>(arena, kids));                  // binds(t) Inner arm
    lemma_forest_binds_subrange::<L>(arena, kids, 0, cp);      // sub-forest binds
    lemma_chain_keys_eq_model_forest::<L>(arena, kids.subrange(0, cp));
}

/// The arena node `node` at `t`'s root has a strictly-sorted projected key view —
/// what `find_child` / `leaf_find_ge` require. From `binds` (keys_view[i].as_nat()
/// == keys/seps[i]) + `tree_wf` (keys/seps strictly_sorted). Takes `node`
/// explicitly (== arena[id]) so the ensures' `Seq::new(|node keys|, ...)` closure
/// matches the callers' `requires` syntactically.
pub(crate) proof fn lemma_tree_wf_sorted_seps_view<L: NodeLayout>(arena: Seq<L::Node>, t: Tree, id: nat, node: L::Node)
    requires
        binds::<L>(arena, t),
        crate::bplus_tree::tree_wf(t, crate::bplus_tree::tree_height(t), L::leaf_cap_spec(), L::key_cap_spec(), true),
        crate::bplus_tree::tree_root_id(t) == id,
        node == arena[id as int],
    ensures
        crate::bplus_tree::strictly_sorted(
            Seq::new(L::keys_view(node).len(), |i: int| L::keys_view(node)[i].as_nat())),
{
    let ks = Seq::new(L::keys_view(node).len(), |i: int| L::keys_view(node)[i].as_nat());
    L::lemma_keys_view_len(node);
    match t {
        Tree::Leaf { id: lid, keys } => {
            // binds: count == keys.len, keys_view[i].as_nat == keys[i]; tree_wf: keys sorted.
            assert(L::count_spec(node) == keys.len());
            assert(ks.len() == keys.len());
            assert forall|i: int, j: int| 0 <= i < j < ks.len() implies #[trigger] ks[i] < #[trigger] ks[j] by {
                assert(ks[i] == keys[i] && ks[j] == keys[j]);   // binds leaf arm
                assert(keys[i] < keys[j]);                       // strictly_sorted(keys)
            }
        }
        Tree::Inner { id: iid, seps, kids } => {
            assert(L::count_spec(node) == seps.len());
            assert(ks.len() == seps.len());
            assert forall|i: int, j: int| 0 <= i < j < ks.len() implies #[trigger] ks[i] < #[trigger] ks[j] by {
                assert(ks[i] == seps[i] && ks[j] == seps[j]);   // binds Inner arm
                assert(seps[i] < seps[j]);                       // strictly_sorted(seps)
            }
        }
    }
}

/// One descent step of `seek_leaf`: given the loop state (cur Inner, alignment,
/// acc == chain_offset(gm), acc + seek_target_idx(tree_keys(cur)) ==
/// seek_target_idx(model)) and `cp == find_child` (find_gt on the node's keys),
/// re-establish the invariant for the child cur' == kids[cp] at gm' == gm +
/// leaf_id_offset(kids,cp), acc' == acc + forest_keys(kids[0..cp]).len(). Composes
/// lemma_seek_idx_descent (model split) + lemma_chain_offset_child (acc law) +
/// the pointwise alignment carry via lemma_forest_leaf_ids_slice.
pub(crate) proof fn seek_descend_step<K, L, S, const TRACK: bool>(
    t: &BPlusTreeSet<K, L, S, TRACK>, cur: Tree, node: L::Node, word: L::Word,
    cp: int, gm: int, acc: int, lids: Ghost<Seq<nat>>,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        t.wf(),
        lids@ == crate::bplus_tree::tree_leaf_ids(t.tree@),
        cur is Inner,
        binds::<L>(t.arena(), cur),
        node == t.arena()[crate::bplus_tree::tree_root_id(cur) as int],
        crate::bplus_tree::tree_wf(cur, crate::bplus_tree::tree_height(cur),
            L::leaf_cap_spec(), L::key_cap_spec(), true),
        0 <= cp <= cur->Inner_seps.len(),
        // find_child characterization, on the node's projected key view.
        forall|j: int| 0 <= j < cp ==> (#[trigger] L::keys_view(node)[j]).as_nat() <= word.as_nat(),
        forall|j: int| cp <= j < L::count_spec(node) ==> word.as_nat() < (#[trigger] L::keys_view(node)[j]).as_nat(),
        0 <= gm,
        gm + crate::bplus_tree::tree_leaf_ids(cur).len() <= lids@.len(),
        crate::bplus_tree::tree_leaf_ids(cur).len() >= 1,
        forall|q: int| 0 <= q < crate::bplus_tree::tree_leaf_ids(cur).len()
            ==> lids@[gm + q] == #[trigger] crate::bplus_tree::tree_leaf_ids(cur)[q],
        acc == chain_offset::<L>(t.arena(), lids@, gm),
        acc + seek_target_idx(crate::bplus_tree::tree_keys(cur), word.as_nat())
            == seek_target_idx(t.model(), word.as_nat()),
    ensures
        ({
            let kids = cur->Inner_kids;
            let gm2 = gm + crate::bplus_tree::leaf_id_offset(kids, cp) as int;
            let acc2 = acc + crate::bplus_tree::forest_keys(kids.subrange(0, cp)).len() as int;
            let cur2 = kids[cp];
            &&& 0 <= cp < kids.len()
            &&& 0 <= gm2
            &&& gm2 + crate::bplus_tree::tree_leaf_ids(cur2).len() <= lids@.len()
            &&& crate::bplus_tree::tree_leaf_ids(cur2).len() >= 1
            &&& (forall|q: int| 0 <= q < crate::bplus_tree::tree_leaf_ids(cur2).len()
                    ==> lids@[gm2 + q] == #[trigger] crate::bplus_tree::tree_leaf_ids(cur2)[q])
            &&& acc2 == chain_offset::<L>(t.arena(), lids@, gm2)
            &&& acc2 + seek_target_idx(crate::bplus_tree::tree_keys(cur2), word.as_nat())
                    == seek_target_idx(t.model(), word.as_nat())
            &&& binds::<L>(t.arena(), cur2)
            &&& crate::bplus_tree::tree_root_id(cur2)
                    == L::child_view(node, cp)
            &&& crate::bplus_tree::tree_wf(cur2, crate::bplus_tree::tree_height(cur2),
                    L::leaf_cap_spec(), L::key_cap_spec(), true)
        }),
{
    let arena = t.arena();
    let kids = cur->Inner_kids;
    let seps = cur->Inner_seps;
    let h = crate::bplus_tree::tree_height(cur);
    let id = crate::bplus_tree::tree_root_id(cur);
    L::lemma_arena_capacity();
    // cp valid child index: cp <= seps.len() == kids.len() - 1 < kids.len().
    assert(kids.len() == seps.len() + 1);             // tree_wf Inner arm
    assert(0 <= cp < kids.len());
    // ghost seps projection: keys_view(node)[j].as_nat() == seps[j] (binds Inner arm).
    assert forall|j: int| 0 <= j < seps.len() implies (#[trigger] L::keys_view(node)[j]).as_nat() == seps[j] by {}
    L::lemma_keys_view_len(node);
    assert(L::count_spec(node) == seps.len());
    // find_child characterization lifted to ghost seps: seps[j] <= tgt for j<cp,
    // tgt < seps[j] for cp<=j (the lemma_seek_idx_descent precondition).
    assert forall|j: int| 0 <= j < cp implies #[trigger] seps[j] <= word.as_nat() by {
        assert(L::keys_view(node)[j].as_nat() == seps[j]);
    }
    assert forall|j: int| cp <= j < seps.len() implies word.as_nat() < #[trigger] seps[j] by {
        assert(L::keys_view(node)[j].as_nat() == seps[j]);
    }
    // model split at child cp.
    crate::bplus_tree::lemma_seek_idx_descent(cur, h, L::leaf_cap_spec(), L::key_cap_spec(), cp, word.as_nat());
    // child binds + wf + root id.
    lemma_inner_binds_child::<L>(arena, id, seps, kids, cp);
    crate::bplus_tree::lemma_forest_wf_at(kids, (h - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), cp);
    crate::bplus_tree::lemma_tree_wf_height(kids[cp], (h - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    crate::bplus_tree::lemma_tree_wf_relax_root(kids[cp], (h - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec());
    // child non-empty leaf seq.
    crate::bplus_tree::lemma_tree_leaf_ids_nonempty(kids[cp], (h - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    // acc law: chain_offset(gm + leaf_id_offset(kids,cp)) == acc + forest_keys(kids[0..cp]).len().
    seek_acc_step::<L>(arena, cur, lids@, gm, cp);
    // alignment carry: lids[gm2 + q] == tree_leaf_ids(kids[cp])[q].
    let off = crate::bplus_tree::leaf_id_offset(kids, cp) as int;
    crate::bplus_tree::lemma_forest_leaf_ids_slice(kids, cp);   // forest_leaf_ids(kids)[off+q] == tlids(kids[cp])[q]
    assert(crate::bplus_tree::tree_leaf_ids(cur) == crate::bplus_tree::forest_leaf_ids(kids));
    assert forall|q: int| 0 <= q < crate::bplus_tree::tree_leaf_ids(kids[cp]).len()
        implies lids@[(gm + off) + q] == #[trigger] crate::bplus_tree::tree_leaf_ids(kids[cp])[q] by {
        // lids[gm + (off+q)] == tree_leaf_ids(cur)[off+q] (parent align, off+q in range)
        //   == forest_leaf_ids(kids)[off+q] == tree_leaf_ids(kids[cp])[q] (slice).
        assert(off + q < crate::bplus_tree::tree_leaf_ids(cur).len());
        assert(lids@[gm + (off + q)] == crate::bplus_tree::tree_leaf_ids(cur)[off + q]);
    }
}

/// The accumulator step: `chain_offset(lids, gm + leaf_id_offset(kids,cp)) ==
/// chain_offset(lids, gm) + forest_keys(kids[0..cp]).len()`, given cur's leaves
/// align with `lids` at `gm`. Splits chain_offset additively at gm, then uses
/// lemma_chain_offset_child on the aligned sub-block.
pub(crate) proof fn seek_acc_step<L: NodeLayout>(arena: Seq<L::Node>, cur: Tree, lids: Seq<nat>, gm: int, cp: int)
    requires
        cur is Inner,
        binds::<L>(arena, cur),
        0 <= cp <= cur->Inner_kids.len(),
        0 <= gm,
        gm + crate::bplus_tree::tree_leaf_ids(cur).len() <= lids.len(),
        forall|q: int| 0 <= q < crate::bplus_tree::tree_leaf_ids(cur).len()
            ==> lids[gm + q] == #[trigger] crate::bplus_tree::tree_leaf_ids(cur)[q],
    ensures
        chain_offset::<L>(arena, lids, gm + crate::bplus_tree::leaf_id_offset(cur->Inner_kids, cp) as int)
            == chain_offset::<L>(arena, lids, gm)
                + crate::bplus_tree::forest_keys(cur->Inner_kids.subrange(0, cp)).len() as int,
{
    let kids = cur->Inner_kids;
    let off = crate::bplus_tree::leaf_id_offset(kids, cp) as int;
    crate::bplus_tree::lemma_leaf_id_offset_bound(kids, cp);
    // chain_offset additive at gm: offset(gm + off) == offset(gm) + (keys in lids[gm..gm+off]).
    lemma_chain_offset_add::<L>(arena, lids, gm, off);
    // the aligned sub-block lids[gm..gm+off] reads the same keys as cur's first
    // `off` leaves; chain_offset_child on cur gives forest_keys(kids[0..cp]).len.
    lemma_chain_offset_aligned_block::<L>(arena, lids, cur, gm, off);
    lemma_chain_offset_child::<L>(arena, cur, cp);
}

/// `chain_offset(lids, a + b) == chain_offset(lids, a) + (sum of leaf-key counts
/// of lids[a .. a+b])`. The additive split of chain_offset at an arbitrary point.
pub(crate) proof fn lemma_chain_offset_add<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>, a: int, b: int)
    requires 0 <= a, 0 <= b, a + b <= lids.len(),
    ensures
        chain_offset::<L>(arena, lids, a + b)
            == chain_offset::<L>(arena, lids, a)
                + chain_offset::<L>(arena, lids.subrange(a, lids.len() as int), b),
    decreases b,
{
    if b == 0 {
        assert(chain_offset::<L>(arena, lids.subrange(a, lids.len() as int), 0) == 0);
    } else {
        // offset(a+b) == offset(a+b-1) + |leaf lids[a+b-1]| (def); recurse at b-1.
        lemma_chain_offset_add::<L>(arena, lids, a, b - 1);
        let suf = lids.subrange(a, lids.len() as int);
        // offset(suf, b) == offset(suf, b-1) + |leaf suf[b-1]|, suf[b-1] == lids[a+b-1].
        assert(suf[b - 1] == lids[a + b - 1]);
    }
}

/// `chain_offset(lids.subrange(gm, _), off) == forest_keys(cur's first off
/// leaves)` when `lids` aligns with `cur`'s leaves at `gm`. Bridges the aligned
/// sub-block's key count to `chain_offset(tree_leaf_ids(cur), off)`.
pub(crate) proof fn lemma_chain_offset_aligned_block<L: NodeLayout>(
    arena: Seq<L::Node>, lids: Seq<nat>, cur: Tree, gm: int, off: int,
)
    requires
        0 <= gm,
        0 <= off,
        gm + crate::bplus_tree::tree_leaf_ids(cur).len() <= lids.len(),
        off <= crate::bplus_tree::tree_leaf_ids(cur).len(),
        forall|q: int| 0 <= q < crate::bplus_tree::tree_leaf_ids(cur).len()
            ==> lids[gm + q] == #[trigger] crate::bplus_tree::tree_leaf_ids(cur)[q],
    ensures
        chain_offset::<L>(arena, lids.subrange(gm, lids.len() as int), off)
            == chain_offset::<L>(arena, crate::bplus_tree::tree_leaf_ids(cur), off),
    decreases off,
{
    let suf = lids.subrange(gm, lids.len() as int);
    let cl = crate::bplus_tree::tree_leaf_ids(cur);
    if off == 0 {
    } else {
        lemma_chain_offset_aligned_block::<L>(arena, lids, cur, gm, off - 1);
        // offset(suf, off) == offset(suf, off-1) + |leaf suf[off-1]|;
        // suf[off-1] == lids[gm + off-1] == cl[off-1] (alignment); same for cl side.
        assert(suf[off - 1] == lids[gm + (off - 1)]);
        assert(lids[gm + (off - 1)] == cl[off - 1]);
    }
}

/// The leaf case of `seek_leaf`: at a leaf `cur` reached by the descent, the
/// local `leaf_find_ge` result `p` plus `chain_offset(gm)` (== acc) equals the
/// global `seek_target_idx(model, word)`, and `cur`'s leaf id is `lids[gm]`.
/// Uses leaf_find_ge's split (== seek_target_idx(tree_keys(cur)) by uniqueness)
/// and the loop's `acc + seek_target_idx(tree_keys(cur)) == seek_target_idx(model)`.
pub(crate) proof fn seek_leaf_finish<K, L, S, const TRACK: bool>(
    t: &BPlusTreeSet<K, L, S, TRACK>, cur: Tree, node: L::Node, word: L::Word,
    p: usize, gm: int, acc: int, lids: Ghost<Seq<nat>>,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        t.wf(),
        lids@ == crate::bplus_tree::tree_leaf_ids(t.tree@),
        cur is Leaf,
        binds::<L>(t.arena(), cur),
        node == t.arena()[crate::bplus_tree::tree_root_id(cur) as int],
        crate::bplus_tree::tree_wf(cur, crate::bplus_tree::tree_height(cur),
            L::leaf_cap_spec(), L::key_cap_spec(), true),
        0 <= gm,
        gm + crate::bplus_tree::tree_leaf_ids(cur).len() <= lids@.len(),
        crate::bplus_tree::tree_leaf_ids(cur).len() >= 1,
        forall|q: int| 0 <= q < crate::bplus_tree::tree_leaf_ids(cur).len()
            ==> lids@[gm + q] == #[trigger] crate::bplus_tree::tree_leaf_ids(cur)[q],
        acc == chain_offset::<L>(t.arena(), lids@, gm),
        acc + seek_target_idx(crate::bplus_tree::tree_keys(cur), word.as_nat())
            == seek_target_idx(t.model(), word.as_nat()),
        // leaf_find_ge's split-point ensures on `node`:
        p <= L::count_spec(node),
        forall|i: int| 0 <= i < p ==> (#[trigger] L::keys_view(node)[i]).as_nat() < word.as_nat(),
        forall|i: int| p <= i < L::count_spec(node) ==> word.as_nat() <= (#[trigger] L::keys_view(node)[i]).as_nat(),
    ensures
        0 <= gm < lids@.len(),
        crate::bplus_tree::tree_root_id(cur) == lids@[gm],
        p <= leaf_word_keys::<L>(t.arena(), lids@[gm]).len(),
        (chain_offset::<L>(t.arena(), lids@, gm) + p as int)
            == seek_target_idx(t.model(), word.as_nat()),
{
    let arena = t.arena();
    let id = crate::bplus_tree::tree_root_id(cur);
    L::lemma_keys_view_len(node);
    // cur == Leaf{id, keys}; tree_leaf_ids(cur) == [id], so lids[gm] == id; cur's
    // model is keys; leaf_word_keys(arena, id) == projected keys_view(node).
    match cur {
        Tree::Leaf { id: lid, keys } => {
            assert(crate::bplus_tree::tree_leaf_ids(cur) =~= seq![lid]);
            assert(crate::bplus_tree::tree_leaf_ids(cur).len() == 1);
            assert(crate::bplus_tree::tree_leaf_ids(cur)[0] == lid);
            assert(lids@[gm + 0] == crate::bplus_tree::tree_leaf_ids(cur)[0]);  // alignment forall at q=0
            assert(lids@[gm] == lid);
            assert(crate::bplus_tree::tree_keys(cur) == keys);
            assert(L::count_spec(node) == keys.len());         // binds leaf arm
            // leaf_word_keys(arena, id)[i] == keys_view(node)[i].as_nat() == keys[i].
            assert(leaf_word_keys::<L>(arena, lid).len() == keys.len());
            assert forall|i: int| 0 <= i < keys.len() implies
                leaf_word_keys::<L>(arena, lid)[i] == #[trigger] keys[i] by {
                assert(L::keys_view(node)[i].as_nat() == keys[i]);  // binds
            }
            // p is the split point of keys (projected): p == seek_target_idx(keys, word).
            assert forall|i: int| 0 <= i < p implies #[trigger] keys[i] < word.as_nat() by {
                assert(L::keys_view(node)[i].as_nat() == keys[i]);
            }
            assert forall|i: int| p <= i < keys.len() implies word.as_nat() <= #[trigger] keys[i] by {
                assert(L::keys_view(node)[i].as_nat() == keys[i]);
            }
            crate::bplus_tree::lemma_tree_wf_sorted(cur, crate::bplus_tree::tree_height(cur),
                L::leaf_cap_spec(), L::key_cap_spec(), true);
            seek_target_idx_unique_call(keys, word.as_nat(), p as int);
            assert(p as int == seek_target_idx(keys, word.as_nat()));
            // chain_offset(gm) + p == acc + seek_target_idx(tree_keys(cur)) == seek_target_idx(model).
        }
        Tree::Inner { .. } => { assert(false); }
    }
}

/// thin caller of lemma_seek_target_idx_unique (keeps the seek_leaf_finish match
/// arm tidy; `r == seek_target_idx` from the split characterization).
pub(crate) proof fn seek_target_idx_unique_call(model: Seq<nat>, t: nat, r: int)
    requires
        crate::bplus_tree::strictly_sorted(model),
        0 <= r <= model.len(),
        forall|i: int| 0 <= i < r ==> #[trigger] model[i] < t,
        forall|i: int| r <= i < model.len() ==> t <= #[trigger] model[i],
    ensures r == seek_target_idx(model, t),
{
    lemma_seek_target_idx_unique(model, t, r);
}


/// Every in-order leaf of a `wf` MULTI-leaf tree is non-empty: when
/// `tree_leaf_ids(tree@).len() >= 2`, the tree is an Inner node, so every leaf is
/// non-root and `tree_wf` forces `>= ceil(cap/2) >= 1` keys. (Bridges to
/// `leaf_word_keys` via `lemma_chain_leaf_binds`'s binding + the keys count.)
pub(crate) proof fn lemma_cursor_next_leaf_nonempty<K, L, S, const TRACK: bool>(
    t: &BPlusTreeSet<K, L, S, TRACK>, m: int,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        t.wf(),
        0 <= m < crate::bplus_tree::tree_leaf_ids(t.tree@).len(),
        crate::bplus_tree::tree_leaf_ids(t.tree@).len() >= 2,
    ensures
        leaf_word_keys::<L>(t.arena(), crate::bplus_tree::tree_leaf_ids(t.tree@)[m]).len() >= 1,
        // the leaf id is a real arena slot, hence < nil_link (the NIL sentinel ==
        // max_nat - 1): wf's arena-length bound puts every id < max_nat - 1.
        crate::bplus_tree::tree_leaf_ids(t.tree@)[m] != nil_link::<L>(),
{
    let arena = t.arena();
    let lids = crate::bplus_tree::tree_leaf_ids(t.tree@);
    // lids[m] < arena.len() < max_nat (wf) ⟹ lids[m] <= max_nat - 2 < nil_link.
    lemma_chain_leaf_binds::<L>(arena, t.tree@, crate::bplus_tree::tree_height(t.tree@), true, m);
    assert(lids[m] < arena.len());
    assert(arena.len() < <L::ArenaIdx as IndexLike>::max_nat());  // wf clause
    // len >= 2 ⟹ tree@ is Inner (a Leaf has exactly one leaf id).
    match t.tree@ {
        Tree::Leaf { .. } => { assert(lids.len() == 1); assert(false); }
        Tree::Inner { kids, .. } => {
            // the m-th in-order leaf is a non-root leaf of a forest_wf forest, so
            // its key count >= ceil(cap/2) >= 1. lemma_chain_leaf_binds_keys gives it.
            lemma_chain_leaf_keys_nonempty::<L>(arena, t.tree@,
                crate::bplus_tree::tree_height(t.tree@), true, m);
        }
    }
}

/// The in-order leaf at chain position `m` of a `wf` tree, when the tree is NOT a
/// bare (possibly-empty) root leaf, carries `>= 1` key. For an Inner tree every
/// leaf is non-root (`tree_wf` min-occupancy); for a Leaf tree the single leaf is
/// the root, so we require `is_root ==> it's the only position` — captured by the
/// caller (`len >= 2` rules the Leaf case out). Mirrors `lemma_chain_leaf_binds`.
pub(crate) proof fn lemma_chain_leaf_keys_nonempty<L: NodeLayout>(arena: Seq<L::Node>, t: Tree, h: nat, is_root: bool, m: int)
    requires
        binds::<L>(arena, t),
        crate::bplus_tree::tree_wf(t, h, L::leaf_cap_spec(), L::key_cap_spec(), is_root),
        0 <= m < crate::bplus_tree::tree_leaf_ids(t).len(),
        t is Inner,  // Inner ⟹ every leaf is non-root, hence non-empty
    ensures
        leaf_word_keys::<L>(arena, crate::bplus_tree::tree_leaf_ids(t)[m]).len() >= 1,
    decreases t,
{
    let kids = t->Inner_kids;
    assert(crate::bplus_tree::tree_leaf_ids(t) == crate::bplus_tree::forest_leaf_ids(kids));
    lemma_chain_leaf_keys_nonempty_forest::<L>(arena, kids, (h - 1) as nat, m);
}

/// Forest companion of `lemma_chain_leaf_keys_nonempty`: every leaf in a
/// `forest_wf` forest (children non-root) is non-empty. Peels the head, recursing
/// into the child (Leaf: non-root min-occupancy; Inner: recurse).
pub(crate) proof fn lemma_chain_leaf_keys_nonempty_forest<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>, ch: nat, m: int)
    requires
        forest_binds_l::<L>(arena, kids),
        crate::bplus_tree::forest_wf(kids, ch, L::leaf_cap_spec(), L::key_cap_spec()),
        0 <= m < crate::bplus_tree::forest_leaf_ids(kids).len(),
    ensures
        leaf_word_keys::<L>(arena, crate::bplus_tree::forest_leaf_ids(kids)[m]).len() >= 1,
    decreases kids,
{
    crate::bplus_tree::lemma_forest_leaf_ids_cons(kids);
    crate::bplus_tree::lemma_forest_wf_cons(kids, ch, L::leaf_cap_spec(), L::key_cap_spec());
    let head = crate::bplus_tree::tree_leaf_ids(kids[0]);
    let df = kids.drop_first();
    assert(binds::<L>(arena, kids[0]));
    assert(forest_binds_l::<L>(arena, df));
    assert(crate::bplus_tree::tree_wf(kids[0], ch, L::leaf_cap_spec(), L::key_cap_spec(), false));  // non-root!
    L::lemma_arena_capacity();
    if m < head.len() {
        assert(crate::bplus_tree::forest_leaf_ids(kids)[m] == head[m]);
        match kids[0] {
            Tree::Leaf { id, keys } => {
                // non-root leaf: keys.len() >= ceil(cap/2) >= 1; leaf_word_keys len == keys.len().
                assert(head =~= seq![id]);
                assert(m == 0);
                assert(keys.len() >= (L::leaf_cap_spec() + 1) / 2);  // tree_wf non-root leaf
                L::lemma_keys_view_len(arena[id as int]);
                assert(L::count_spec(arena[id as int]) == keys.len());  // binds
            }
            Tree::Inner { .. } => {
                lemma_chain_leaf_keys_nonempty::<L>(arena, kids[0], ch, false, m);
            }
        }
    } else {
        assert(crate::bplus_tree::forest_leaf_ids(kids)[m]
            == crate::bplus_tree::forest_leaf_ids(df)[m - head.len()]);
        lemma_chain_leaf_keys_nonempty_forest::<L>(arena, df, ch, m - head.len() as int);
    }
}

/// The in-order leaf at chain position `m` binds as a `Leaf` node: for a
/// `binds`-ing tree, `arena[tree_leaf_ids(t)[m]]` is a well-formed leaf whose
/// key count is `leaf_word_keys(arena, that id).len()`. Structural induction
/// (the leaf-id list and the leaf nodes recurse together); the forest companion
/// peels children using `leaf_id_offset` to locate which child holds position m.
/// **The append fast path's bridge.** For a `wf` tree, the arena node at
/// `last_leaf` is a well-formed leaf whose keys are exactly `last_leaf_keys` of
/// the ghost tree, and the model ends with those keys. So the exec check "`kw`
/// exceeds this leaf's last key, and the leaf has room" establishes both
/// `lemma_append_last_wf`'s preconditions: `k` above every model key (the model
/// is sorted, so exceeding its last element suffices) and `last_leaf_keys.len() <
/// cap`.
///
/// Recursing on the rightmost spine would duplicate `lemma_chain_leaf_binds`;
/// instead this composes it at the chain's last position, which
/// `lemma_last_leaf_id` identifies with `last_leaf`.
pub(crate) proof fn lemma_last_leaf_binds<K, L, S, const TRACK: bool>(
    t: &BPlusTreeSet<K, L, S, TRACK>,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires t.wf(),
    ensures
        t.last_leaf.as_nat() < t.arena().len(),
        L::is_leaf_spec(t.arena()[t.last_leaf.as_nat() as int]),
        L::node_wf(t.arena()[t.last_leaf.as_nat() as int]),
        leaf_word_keys::<L>(t.arena(), t.last_leaf.as_nat())
            == crate::bplus_tree::last_leaf_keys(t.tree@),
        // the model ends with the last leaf's keys, so the model's last key (when
        // the leaf is non-empty) is that leaf's last key.
        t.model() == t.model().subrange(
                0, t.model().len() - crate::bplus_tree::last_leaf_keys(t.tree@).len() as int)
            + crate::bplus_tree::last_leaf_keys(t.tree@),
{
    let arena = t.arena();
    let lids = crate::bplus_tree::tree_leaf_ids(t.tree@);
    let h = crate::bplus_tree::tree_height(t.tree@);
    L::lemma_arena_capacity();
    L::lemma_geometry();
    crate::bplus_tree::lemma_last_leaf_id(t.tree@, h, L::leaf_cap_spec(), L::key_cap_spec(), true);
    let last = lids.len() - 1;
    assert(lids[last] == t.last_leaf.as_nat());
    lemma_chain_leaf_binds::<L>(arena, t.tree@, h, true, last);
    // chain reading == model, and the chain's last slice is the last leaf's keys.
    lemma_chain_keys_eq_model::<L>(arena, t.tree@);
    lemma_last_leaf_keys_chain::<L>(arena, t.tree@, h, true);
    lemma_chain_keys_split_last::<L>(arena, lids);
}

/// `last_leaf_keys(t)` is what the arena's last chain leaf reads: the ghost
/// rightmost-leaf keys and the exec ones coincide, by the same `binds` recursion
/// that relates the whole chain to the model.
/// `tree_wf` is needed, not just `binds`: it is what forces the rightmost child
/// to have at least one leaf (`kids.len() == seps.len() + 1 >= 1`, recursively).
/// Without it a spine node with no children would put the chain's last entry in
/// an *earlier* child, while `last_leaf_keys` still descends rightward.
pub(crate) proof fn lemma_last_leaf_keys_chain<L: NodeLayout>(
    arena: Seq<L::Node>, t: Tree, h: nat, is_root: bool,
)
    requires
        binds::<L>(arena, t),
        crate::bplus_tree::tree_wf(t, h, L::leaf_cap_spec(), L::key_cap_spec(), is_root),
        L::leaf_cap_spec() >= 1,
    ensures
        crate::bplus_tree::tree_leaf_ids(t).len() >= 1,
        leaf_word_keys::<L>(arena, crate::bplus_tree::tree_leaf_ids(t)[
            crate::bplus_tree::tree_leaf_ids(t).len() - 1])
            == crate::bplus_tree::last_leaf_keys(t),
    decreases t,
{
    crate::bplus_tree::lemma_tree_leaf_ids_nonempty(
        t, h, L::leaf_cap_spec(), L::key_cap_spec(), is_root);
    match t {
        Tree::Leaf { id, keys } => {
            // tree_leaf_ids == [id]; binds' leaf arm says arena[id] reads `keys`
            // (count == keys.len() and keys_view[i].as_nat() == keys[i]).
            assert(crate::bplus_tree::tree_leaf_ids(t) =~= seq![id]);
            assert(L::count_spec(arena[id as int]) == keys.len());
            L::lemma_keys_view_len(arena[id as int]);
            let lwk = leaf_word_keys::<L>(arena, id);
            assert(lwk.len() == keys.len());
            assert(lwk =~= keys);
        }
        Tree::Inner { seps, kids, .. } => {
            // tree_wf: kids.len() == seps.len() + 1 >= 1, so the rightmost child
            // exists and is itself wf at h-1.
            let m = kids.len() - 1;
            lemma_forest_binds_at::<L>(arena, kids, m);
            crate::bplus_tree::lemma_forest_wf_at(
                kids, (h - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), m);
            lemma_last_leaf_keys_chain::<L>(arena, kids[m], (h - 1) as nat, false);
            crate::bplus_tree::lemma_forest_leaf_ids_last(kids, m);
        }
    }
}

/// **The arena bridge for the append fast path.** Writing the grown leaf into the
/// single arena slot `last_leaf_id(t)` re-establishes `binds` and the leaf-link
/// chain for `tree_append_last(t, k)`.
///
/// The recursion is over the rightmost spine only. At an internal node, `nleaf`
/// lands inside the LAST child's region, so the earlier children are framed by
/// `lemma_forest_binds_update`'s agreement clause and the node's own slot is
/// untouched (`tree_disjoint` says `id ∉ forest_ids(kids)`, and the appended slot
/// is in `tree_ids(kids[m])`). The leaf-link view is preserved by
/// `leaf_insert_at`, which is why the chain transfers unchanged: the ONE slot that
/// differs holds the same link, and the leaf-id sequence is identical.
pub(crate) proof fn lemma_binds_append_last<L: NodeLayout>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    t: Tree,
    h: nat,
    succ: nat,
    is_root: bool,
    k: nat,
)
    requires
        binds::<L>(a1, t),
        crate::bplus_tree::tree_wf(t, h, L::leaf_cap_spec(), L::key_cap_spec(), is_root),
        crate::bplus_tree::tree_disjoint(t),
        leaf_links_to::<L>(a1, t, succ),
        L::leaf_cap_spec() >= 1,
        // exactly one slot differs — the rightmost leaf's — and it holds the same
        // leaf with `k` appended (what `leaf_insert_at` at `count` produces).
        a1.len() == a2.len(),
        ({
            let lid = crate::bplus_tree::last_leaf_id(t);
            &&& (forall|i: int| 0 <= i < a1.len() && i != lid as int
                    ==> #[trigger] a2[i] == a1[i])
            &&& L::is_leaf_spec(a2[lid as int])
            &&& L::link_view(a2[lid as int]) == L::link_view(a1[lid as int])
            &&& L::count_spec(a2[lid as int]) == L::count_spec(a1[lid as int]) + 1
            &&& leaf_word_keys::<L>(a2, lid)
                    == leaf_word_keys::<L>(a1, lid).push(k)
        }),
    ensures
        binds::<L>(a2, crate::bplus_tree::tree_append_last(t, k)),
        leaf_links_to::<L>(a2, crate::bplus_tree::tree_append_last(t, k), succ),
    decreases t,
{
    let lid = crate::bplus_tree::last_leaf_id(t);
    let nt = crate::bplus_tree::tree_append_last(t, k);
    crate::bplus_tree::lemma_append_last_shape(t, k);
    match t {
        Tree::Leaf { id, keys } => {
            // the tree IS the last leaf: lid == id, nt == Leaf{id, keys.push(k)}.
            assert(lid == id);
            assert(nt == Tree::Leaf { id, keys: keys.push(k) });
            L::lemma_keys_view_len(a1[id as int]);
            L::lemma_keys_view_len(a2[id as int]);
            let w1 = leaf_word_keys::<L>(a1, id);
            let w2 = leaf_word_keys::<L>(a2, id);
            assert(w1.len() == keys.len());
            assert(w1 =~= keys);
            assert(w2 =~= keys.push(k));
            assert(L::count_spec(a2[id as int]) == keys.push(k).len());
            assert forall|i: int| 0 <= i < keys.push(k).len() implies
                (#[trigger] L::keys_view(a2[id as int])[i]).as_nat() == keys.push(k)[i] by {
                assert(w2[i] == keys.push(k)[i]);
            }
            // leaf-link: the chain is the single leaf, whose link is unchanged.
            assert(crate::bplus_tree::tree_leaf_ids(nt) =~= seq![id]);
        }
        Tree::Inner { id, seps, kids } => {
            // tree_wf forces kids.len() == seps.len() + 1 >= 1.
            let m = kids.len() - 1;
            let nc = crate::bplus_tree::tree_append_last(kids[m], k);
            let u = kids.update(m, nc);
            assert(nt == Tree::Inner { id, seps, kids: u });
            // the appended slot lies in the last child's footprint...
            crate::bplus_tree::lemma_forest_wf_at(
                kids, (h - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), m);
            crate::bplus_tree::lemma_forest_disjoint_at(kids, m);
            crate::bplus_tree::lemma_last_leaf_id_in_ids(
                kids[m], (h - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
            assert(crate::bplus_tree::last_leaf_id(kids[m]) == lid);
            assert(crate::bplus_tree::tree_ids(kids[m]).contains(lid));
            // ...so it is not this node's own slot (tree_disjoint: id ∉ forest_ids).
            crate::bplus_tree::lemma_forest_ids_cons(kids);
            assert(crate::bplus_tree::forest_ids(kids).contains(lid)) by {
                crate::bplus_tree::lemma_forest_id_at_child(kids, m, lid);
            }
            assert(id != lid);
            assert(a2[id as int] == a1[id as int]);

            // recurse into the last child (its link target is whatever follows it,
            // but `leaf_links_to` on a subtree only needs SOME succ — take the one
            // the parent's chain assigns, which the decomposition supplies).
            lemma_forest_binds_at::<L>(a1, kids, m);
            let csucc = L::link_view(a1[lid as int]);
            assert(leaf_links_to::<L>(a1, kids[m], csucc)) by {
                lemma_last_child_links::<L>(a1, t, h, is_root, succ, m);
            }
            lemma_binds_append_last::<L>(a1, a2, kids[m], (h - 1) as nat, csucc, false, k);

            // the forest re-binds: only child m changed; every other child's
            // region is untouched (the one differing slot is inside child m).
            assert forall|jd: nat| (#[trigger] crate::bplus_tree::forest_ids(kids).contains(jd))
                && !crate::bplus_tree::tree_ids(kids[m]).contains(jd)
                implies a1[jd as int] == a2[jd as int] by {
                assert(jd != lid);
                // the single-slot agreement is stated over in-range indices, and
                // every footprint id is in range by `binds`.
                assert(crate::bplus_tree::tree_ids(t).contains(jd));
                lemma_tree_id_in_range::<L>(a1, t, jd);
            }
            // `forest_binds_update`'s two disjointness hypotheses are literally
            // `tree_disjoint(t)`'s Inner clauses.
            lemma_forest_binds_update::<L>(a1, a2, kids, m, nc);
            // the child-pointer array is in this node's (unchanged) slot, and
            // tree_root_id(nc) == tree_root_id(kids[m]) by the shape lemma.
            crate::bplus_tree::lemma_append_last_shape(kids[m], k);
            assert forall|i: int| 0 <= i < u.len() implies
                L::child_view(a2[id as int], i)
                    == crate::bplus_tree::tree_root_id(#[trigger] u[i]) by {
                if i == m {
                    assert(u[m] == nc);
                } else {
                    assert(u[i] == kids[i]);
                }
            }
            // links: the leaf-id sequence is unchanged (shape lemma) and every
            // link slot reads the same as in a1 (the one differing slot keeps its
            // link), so the parent's chain predicate transfers verbatim.
            assert(crate::bplus_tree::tree_leaf_ids(nt)
                == crate::bplus_tree::tree_leaf_ids(t));
            let lids = crate::bplus_tree::tree_leaf_ids(t);
            assert forall|p: int| 0 <= p < lids.len() implies
                #[trigger] L::link_view(a2[lids[p] as int])
                    == (if p + 1 < lids.len() { lids[p + 1] } else { succ }) by {
                assert(L::link_view(a1[lids[p] as int])
                    == (if p + 1 < lids.len() { lids[p + 1] } else { succ }));
                if lids[p] != lid {
                    crate::bplus_tree::lemma_leaf_id_in_tree_ids(t, p);
                    lemma_tree_id_in_range::<L>(a1, t, lids[p]);
                    assert(a2[lids[p] as int] == a1[lids[p] as int]);
                }
            }
        }
    }
}

/// The last child's leaf chain ends at whatever the parent's last leaf links to.
/// The one-sided (rightmost) instance of the forest-link decomposition: the last
/// child's leaf-id sequence is a suffix of the parent's, so its own `succ` is the
/// link stored in the parent's last leaf.
pub(crate) proof fn lemma_last_child_links<L: NodeLayout>(
    arena: Seq<L::Node>, t: Tree, h: nat, is_root: bool, succ: nat, m: int,
)
    requires
        crate::bplus_tree::tree_wf(t, h, L::leaf_cap_spec(), L::key_cap_spec(), is_root),
        L::leaf_cap_spec() >= 1,
        leaf_links_to::<L>(arena, t, succ),
        t is Inner,
        m == t->Inner_kids.len() - 1,
        m >= 0,
    ensures
        leaf_links_to::<L>(arena, t->Inner_kids[m],
            L::link_view(arena[crate::bplus_tree::last_leaf_id(t) as int])),
{
    let kids = t->Inner_kids;
    let lids = crate::bplus_tree::tree_leaf_ids(t);
    let clids = crate::bplus_tree::tree_leaf_ids(kids[m]);
    crate::bplus_tree::lemma_forest_wf_at(
        kids, (h - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), m);
    crate::bplus_tree::lemma_last_leaf_id(
        kids[m], (h - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
    crate::bplus_tree::lemma_last_leaf_id(t, h, L::leaf_cap_spec(), L::key_cap_spec(), is_root);
    // the child's chain is the parent's tail: lids[off + q] == clids[q].
    let off = crate::bplus_tree::leaf_id_offset(kids, m);
    crate::bplus_tree::lemma_forest_leaf_ids_slice(kids, m);
    assert(lids == crate::bplus_tree::forest_leaf_ids(kids));
    crate::bplus_tree::lemma_forest_leaf_ids_last(kids, m);
    crate::bplus_tree::lemma_leaf_id_offset_last(kids, m);
    assert(off + clids.len() == lids.len());
    let csucc = L::link_view(arena[crate::bplus_tree::last_leaf_id(t) as int]);
    assert forall|q: int| 0 <= q < clids.len() implies
        #[trigger] L::link_view(arena[clids[q] as int])
            == (if q + 1 < clids.len() { clids[q + 1] } else { csucc }) by {
        assert(clids[q] == lids[off + q]);
        assert(L::link_view(arena[lids[off + q] as int])
            == (if off + q + 1 < lids.len() { lids[off + q + 1] } else { succ }));
        if q + 1 < clids.len() {
            // instantiate the slice lemma at `q + 1`: bound the index to a `let` so
            // the `forest_leaf_ids(kids)[off + _]` trigger matches syntactically
            // (`off + q + 1` does not, being parsed as `(off + q) + 1`).
            let q1 = q + 1;
            assert(clids[q1] == lids[off + q1]);
            assert(clids[q + 1] == lids[off + q + 1]);
        } else {
            // q is the child's last leaf == the parent's last leaf == last_leaf_id(t).
            assert(clids[q] == lids[lids.len() - 1]);
            assert(lids[lids.len() - 1] == crate::bplus_tree::last_leaf_id(t));
        }
    }
}

/// The chain reading splits as "everything before the last leaf" ++ "the last
/// leaf's keys". The `lemma_chain_keys_slice` companion at the tail end.
pub(crate) proof fn lemma_chain_keys_split_last<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>)
    requires lids.len() >= 1,
    ensures
        chain_keys::<L>(arena, lids)
            == chain_keys::<L>(arena, lids.subrange(0, lids.len() - 1))
                + leaf_word_keys::<L>(arena, lids[lids.len() - 1]),
    decreases lids,
{
    if lids.len() == 1 {
        assert(lids.subrange(0, 0) =~= Seq::<nat>::empty());
        assert(lids.drop_first() =~= Seq::<nat>::empty());
    } else {
        let df = lids.drop_first();
        lemma_chain_keys_split_last::<L>(arena, df);
        assert(df[df.len() - 1] == lids[lids.len() - 1]);
        assert(df.subrange(0, df.len() - 1) =~= lids.subrange(0, lids.len() - 1).drop_first());
    }
}

pub(crate) proof fn lemma_chain_leaf_binds<L: NodeLayout>(arena: Seq<L::Node>, t: Tree, h: nat, is_root: bool, m: int)
    requires
        binds::<L>(arena, t),
        crate::bplus_tree::tree_wf(t, h, L::leaf_cap_spec(), L::key_cap_spec(), is_root),
        0 <= m < crate::bplus_tree::tree_leaf_ids(t).len(),
    ensures
        (crate::bplus_tree::tree_leaf_ids(t)[m] as int) < arena.len(),
        L::is_leaf_spec(arena[crate::bplus_tree::tree_leaf_ids(t)[m] as int]),
        L::node_wf(arena[crate::bplus_tree::tree_leaf_ids(t)[m] as int]),
    decreases t,
{
    match t {
        Tree::Leaf { id, keys } => {
            // tree_leaf_ids == [id], m == 0; binds (count==keys.len) + tree_wf
            // (keys.len <= leaf_cap) ⟹ node_wf via the iff.
            assert(crate::bplus_tree::tree_leaf_ids(t) =~= seq![id]);
            assert(L::count_spec(arena[id as int]) == keys.len());  // binds leaf arm
            assert(keys.len() <= L::leaf_cap_spec());               // tree_wf leaf arm
            L::lemma_node_wf_iff(arena[id as int]);
        }
        Tree::Inner { id, seps, kids } => {
            assert(crate::bplus_tree::tree_leaf_ids(t) == crate::bplus_tree::forest_leaf_ids(kids));
            // children are wf at h-1 (forest_wf, tree_wf Inner arm).
            lemma_chain_leaf_binds_forest::<L>(arena, kids, (h - 1) as nat, m);
        }
    }
}

/// Forest companion: position `m` of `forest_leaf_ids(kids)` lands in some child;
/// peel the head and recurse, locating `m` via the head child's leaf count. The
/// children are wf at `ch` (= parent height - 1) via the parent's `forest_wf`.
pub(crate) proof fn lemma_chain_leaf_binds_forest<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>, ch: nat, m: int)
    requires
        forest_binds_l::<L>(arena, kids),
        crate::bplus_tree::forest_wf(kids, ch, L::leaf_cap_spec(), L::key_cap_spec()),
        0 <= m < crate::bplus_tree::forest_leaf_ids(kids).len(),
    ensures
        (crate::bplus_tree::forest_leaf_ids(kids)[m] as int) < arena.len(),
        L::is_leaf_spec(arena[crate::bplus_tree::forest_leaf_ids(kids)[m] as int]),
        L::node_wf(arena[crate::bplus_tree::forest_leaf_ids(kids)[m] as int]),
    decreases kids,
{
    crate::bplus_tree::lemma_forest_leaf_ids_cons(kids);
    crate::bplus_tree::lemma_forest_wf_cons(kids, ch, L::leaf_cap_spec(), L::key_cap_spec());
    let head = crate::bplus_tree::tree_leaf_ids(kids[0]);
    let df = kids.drop_first();
    // forest_leaf_ids(kids) == head ++ forest_leaf_ids(df); both children wf at ch.
    assert(binds::<L>(arena, kids[0]));            // forest_binds cons
    assert(forest_binds_l::<L>(arena, df));
    assert(crate::bplus_tree::tree_wf(kids[0], ch, L::leaf_cap_spec(), L::key_cap_spec(), false));  // forest_wf cons
    if m < head.len() {
        // position m is in the head child; recurse on the tree.
        assert(crate::bplus_tree::forest_leaf_ids(kids)[m] == head[m]);
        lemma_chain_leaf_binds::<L>(arena, kids[0], ch, false, m);
    } else {
        // position m is in the tail; recurse on df at m - head.len().
        assert(crate::bplus_tree::forest_leaf_ids(kids)[m]
            == crate::bplus_tree::forest_leaf_ids(df)[m - head.len()]);
        lemma_chain_leaf_binds_forest::<L>(arena, df, ch, m - head.len() as int);
    }
}

/// A positioned cursor's leaf node is well-formed and in arena range. From
/// `cursor_wf`: `node == lids[gleaf]` is the in-order leaf at position `gleaf`,
/// so `lemma_chain_leaf_binds` gives `is_leaf` + `node_wf` + in-range. Lets the
/// cursor call `L::key`/`L::count` (which require `node_wf`).
pub(crate) proof fn lemma_cursor_node_wf<K, L, S, const TRACK: bool>(c: &BPlusCursor<K, L, S, TRACK>)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        c.cursor_wf(),
        c.node.as_nat() != nil_link::<L>(),
    ensures
        c.node.as_nat() < c.tree.arena().len(),
        L::node_wf(c.tree.arena()[c.node.as_nat() as int]),
        L::is_leaf_spec(c.tree.arena()[c.node.as_nat() as int]),
        L::count_spec(c.tree.arena()[c.node.as_nat() as int])
            == leaf_word_keys::<L>(c.tree.arena(), c.node.as_nat()).len(),
{
    let arena = c.tree.arena();
    let lids = crate::bplus_tree::tree_leaf_ids(c.tree.tree@);
    let m = c.gleaf@;
    assert(c.node.as_nat() == lids[m]);  // cursor_wf positioned arm
    // tree wf at root form (from c.tree.wf()); chain-leaf at m binds as a leaf.
    lemma_chain_leaf_binds::<L>(arena, c.tree.tree@,
        crate::bplus_tree::tree_height(c.tree.tree@), true, m);
    L::lemma_keys_view_len(arena[c.node.as_nat() as int]);
}

/// Leaf-at-chain-index `gm` facts for `seek`: from `t.wf()` and a valid chain
/// index, `arena[lids[gm]]` is a wf leaf in range with `count == |leaf gm|`. The
/// `gm`-parameterized analogue of `lemma_cursor_node_wf` (which reads `c.gleaf`).
pub(crate) proof fn lemma_cursor_node_wf_at<K, L, S, const TRACK: bool>(
    t: &BPlusTreeSet<K, L, S, TRACK>, gm: int,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        t.wf(),
        0 <= gm < crate::bplus_tree::tree_leaf_ids(t.tree@).len(),
    ensures
        (crate::bplus_tree::tree_leaf_ids(t.tree@)[gm] as int) < t.arena().len(),
        L::node_wf(t.arena()[crate::bplus_tree::tree_leaf_ids(t.tree@)[gm] as int]),
        L::is_leaf_spec(t.arena()[crate::bplus_tree::tree_leaf_ids(t.tree@)[gm] as int]),
        L::count_spec(t.arena()[crate::bplus_tree::tree_leaf_ids(t.tree@)[gm] as int])
            == leaf_word_keys::<L>(t.arena(), crate::bplus_tree::tree_leaf_ids(t.tree@)[gm]).len(),
{
    let arena = t.arena();
    let lids = crate::bplus_tree::tree_leaf_ids(t.tree@);
    lemma_chain_leaf_binds::<L>(arena, t.tree@,
        crate::bplus_tree::tree_height(t.tree@), true, gm);
    L::lemma_keys_view_len(arena[lids[gm] as int]);
}

/// `seek`'s in-leaf finish: after `seek_leaf` returns `(lids[gm], pos, gm)` with
/// `pos < |leaf gm|` and `chain_offset(gm) + pos == ti == seek_target_idx`, and
/// the cursor set to `(node := lids[gm], pos, gleaf := gm, gidx := ti)`,
/// `cursor_wf` holds and `idx == ti`. The positioned arm, with the node != NIL
/// fact from the real-id bound.
pub(crate) proof fn seek_finish_in_leaf<K, L, S, const TRACK: bool>(
    c: &BPlusCursor<K, L, S, TRACK>, oldc: &BPlusCursor<K, L, S, TRACK>, gm: int, pos: usize, tgt: nat,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        oldc.cursor_wf(),
        c.tree == oldc.tree,
        0 <= gm < crate::bplus_tree::tree_leaf_ids(c.tree.tree@).len(),
        c.node.as_nat() == crate::bplus_tree::tree_leaf_ids(c.tree.tree@)[gm],
        c.gleaf@ == gm,
        c.pos == pos,
        pos < leaf_word_keys::<L>(c.tree.arena(), crate::bplus_tree::tree_leaf_ids(c.tree.tree@)[gm]).len(),
        c.gidx@ == seek_target_idx(c.model(), tgt),
        chain_offset::<L>(c.tree.arena(), crate::bplus_tree::tree_leaf_ids(c.tree.tree@), gm) + pos
            == seek_target_idx(c.model(), tgt),
    ensures
        c.cursor_wf(),
        c.idx() == seek_target_idx(c.model(), tgt),
{
    let arena = c.tree.arena();
    let lids = crate::bplus_tree::tree_leaf_ids(c.tree.tree@);
    // node != nil_link: lids[gm] is a real leaf id (< arena.len() < max_nat).
    lemma_cursor_node_wf_at::<K, L, S, TRACK>(c.tree, gm);
    assert(c.node.as_nat() < arena.len());
    assert(c.node.as_nat() != nil_link::<L>());     // wf arena bound
    // gidx in range: ti == chain_offset(gm)+pos < chain_offset(gm)+|leaf gm| ==
    // a valid chain_keys index <= |model|; and >= 0.
    lemma_chain_keys_slice::<L>(arena, lids, gm);
    lemma_chain_keys_eq_model::<L>(arena, c.tree.tree@);
    assert(0 <= c.gidx@ < c.model().len());
}

/// `seek`'s over-the-end finish: `seek_leaf` returned `pos == |leaf gm|` (target
/// past leaf gm's keys), so we set `node := link(arena[lids[gm]])`, `pos := 0`.
/// By `leaf_links_ok`, `link == lids[gm+1]` (then positioned at gm+1, since
/// chain_offset(gm)+|leaf gm| == chain_offset(gm+1)) or NIL (exhausted, ti ==
/// |model|). Either way `cursor_wf` holds with `idx == ti`. Mirrors `step`'s
/// link-follow.
pub(crate) proof fn seek_finish_over_end<K, L, S, const TRACK: bool>(
    c: &BPlusCursor<K, L, S, TRACK>, oldc: &BPlusCursor<K, L, S, TRACK>, node: L::Node, gm: int, tgt: nat,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        oldc.cursor_wf(),
        c.tree == oldc.tree,
        0 <= gm < crate::bplus_tree::tree_leaf_ids(c.tree.tree@).len(),
        node == c.tree.arena()[crate::bplus_tree::tree_leaf_ids(c.tree.tree@)[gm] as int],
        c.node.as_nat() == L::link_view(node),
        c.pos == 0,
        c.gidx@ == seek_target_idx(c.model(), tgt),
        // when the link goes to a real next leaf, the caller set gleaf := gm+1.
        c.node.as_nat() != nil_link::<L>() ==> c.gleaf@ == gm + 1,
        // seek_leaf gave pos == |leaf gm| with chain_offset(gm)+|leaf gm| == ti.
        chain_offset::<L>(c.tree.arena(), crate::bplus_tree::tree_leaf_ids(c.tree.tree@), gm)
            + leaf_word_keys::<L>(c.tree.arena(), crate::bplus_tree::tree_leaf_ids(c.tree.tree@)[gm]).len()
            == seek_target_idx(c.model(), tgt),
    ensures
        c.cursor_wf(),
        c.idx() == seek_target_idx(c.model(), tgt),
{
    let arena = c.tree.arena();
    let lids = crate::bplus_tree::tree_leaf_ids(c.tree.tree@);
    // chain_offset(gm+1) == chain_offset(gm) + |leaf gm| == ti  (offset def).
    assert(chain_offset::<L>(arena, lids, gm + 1)
        == chain_offset::<L>(arena, lids, gm) + leaf_word_keys::<L>(arena, lids[gm]).len());
    assert(c.gidx@ == chain_offset::<L>(arena, lids, gm + 1));
    // leaf_links_ok: link(arena[lids[gm]]) == lids[gm+1] (m+1<len) | nil_link (last).
    assert(leaf_links_ok::<L>(arena, c.tree.tree@));
    lemma_cursor_node_wf_at::<K, L, S, TRACK>(c.tree, gm);
    assert(L::link_view(arena[lids[gm] as int])
        == (if gm + 1 < lids.len() { lids[gm + 1] } else { nil_link::<L>() }));
    if gm + 1 < lids.len() {
        // positioned at leaf gm+1, pos 0. node == lids[gm+1] (real id), non-empty.
        assert(c.node.as_nat() == lids[gm + 1]);
        assert(lids.len() >= 2);
        lemma_cursor_next_leaf_nonempty::<K, L, S, TRACK>(c.tree, gm + 1);
        assert(c.node.as_nat() != nil_link::<L>());
        assert(c.gleaf@ == gm + 1);   // caller set it
        lemma_chain_keys_slice::<L>(arena, lids, gm + 1);
        lemma_chain_keys_eq_model::<L>(arena, c.tree.tree@);
        assert(0 <= c.gidx@ < c.model().len());
    } else {
        // exhausted: node == nil_link, ti == chain_offset(len) == |model|.
        assert(c.node.as_nat() == nil_link::<L>());
        lemma_chain_offset_full::<L>(arena, lids);
        lemma_chain_keys_eq_model::<L>(arena, c.tree.tree@);
        assert(c.gidx@ == c.model().len());
    }
}

/// A positioned cursor reads the model: `keys_view(arena[node])[pos].as_nat() ==
/// model[gidx]`. Composes `lemma_chain_keys_slice` (chain reading at the leaf's
/// slice == that leaf's pos-th key) with B2 (`chain_keys == tree_keys == model`).
pub(crate) proof fn lemma_cursor_key_at<K, L, S, const TRACK: bool>(c: &BPlusCursor<K, L, S, TRACK>)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        c.cursor_wf(),
        c.node.as_nat() != nil_link::<L>(),
    ensures
        L::keys_view(c.tree.arena()[c.node.as_nat() as int])[c.pos as int].as_nat()
            == c.model()[c.gidx@],
{
    let arena = c.tree.arena();
    let lids = crate::bplus_tree::tree_leaf_ids(c.tree.tree@);
    let m = c.gleaf@;
    let lwk = leaf_word_keys::<L>(arena, lids[m]);
    // chain reading at the leaf's slice: chain_keys[chain_offset(m) + pos] == lwk[pos].
    lemma_chain_keys_slice::<L>(arena, lids, m);
    assert(chain_keys::<L>(arena, lids)[chain_offset::<L>(arena, lids, m) + c.pos as int] == lwk[c.pos as int]);
    // B2: chain_keys(lids) == tree_keys(tree@) == model.
    lemma_chain_keys_eq_model::<L>(arena, c.tree.tree@);
    assert(chain_keys::<L>(arena, lids) == c.model());
    // gidx == chain_offset(m) + pos (cursor_wf positioned arm).
    assert(c.gidx@ == chain_offset::<L>(arena, lids, m) + c.pos);
    // lwk[pos] == keys_view(arena[node])[pos] (node == lids[m], lwk def).
    assert(lwk[c.pos as int] == L::keys_view(arena[lids[m] as int])[c.pos as int].as_nat());
    assert(c.node.as_nat() == lids[m]);
}

/// Every model value is within `K::id_bound` — directly from `wf`'s
/// `model_bounded` clause (the refinement re-asserted there). This is what lets
/// the cursor's `from_usize(word.as_usize())` reconstruct the exact `K`.
pub(crate) proof fn lemma_model_value_bounded<K, L, S, const TRACK: bool>(
    t: &BPlusTreeSet<K, L, S, TRACK>, i: int,
)
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
    requires
        t.wf(),
        0 <= i < crate::bplus_tree::tree_keys(t.tree@).len(),
    ensures
        crate::bplus_tree::tree_keys(t.tree@)[i] < K::id_bound(),
{
    // wf's model_bounded clause, instantiated at i.
    assert(model_bounded::<K>(t.model()));
}


impl<K, L, S, const TRACK: bool> BPlusTreeSet<K, L, S, TRACK>
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
{

    // OVERFLOW-SAFETY of the seek path (audit, 2026-06):
    //
    // Verus's exec verification includes a built-in no-arithmetic-overflow check
    // on every `+`/`-`/`*` over machine integers, so the fact that `leaf_find_ge`,
    // `find_child`, `seek_leaf`, `seek` and `step` all verify already MEANS no
    // operation in the seek path can overflow. Concretely:
    //   - In-node search arithmetic lives in bplus_search.rs (`leaf_find_ge` /
    //     `find_child` dispatch to `S::find_ge` / `S::find_gt`). The bisection
    //     midpoint there is `base + size / 2` with `base + size <= len`, the
    //     canonical overflow-safe form. The naive `(lo + hi) / 2` (which overflows
    //     once `lo + hi` exceeds `usize::MAX`) appears NOWHERE in the crate;
    //     operands are bounded by `count <= cap` anyway.
    //   - Within-leaf / next-leaf advance (`pos + 1`, `step`'s `self.pos + 1`) is
    //     bounded by leaf capacity; the model-index bumps (`gidx + 1`, `gm + 1`,
    //     `acc + forest_keys(..)`) are GHOST `int` (unbounded — overflow is not even
    //     a category there).
    //   - Pivot/key values are never arithmetic operands: separators and keys are
    //     read from `L::keys(node)` and only COMPARED (`km.le(word)`), never
    //     added/subtracted. The single value cast on the path is `key()`'s
    //     `K::from_usize(w.as_usize())`, proven to round-trip exactly because
    //     `model_bounded` keeps every stored word `< K::id_bound()`.
    // So the seek path is overflow-safe both structurally (bounds) and by machine
    // proof (Verus's overflow check on the verifying exec bodies).

    /// Walk the rightmost spine and return the rightmost leaf's arena index —
    /// i.e. recompute `last_leaf` from scratch, in O(depth).
    ///
    /// Needed because `insert_rec`'s contract preserves a subtree's *leftmost*
    /// leaf (a split always splices the new node to the RIGHT) but not its
    /// rightmost, which moves whenever the split lands on the rightmost spine.
    /// Strengthening `insert_rec` to track the last leaf would mean threading a
    /// new clause through ~1500 lines of split/absorb proof; recomputing costs one
    /// extra descent on a path that already performed one — and only on the SLOW
    /// path, since the fast path returns before ever reaching it. Production sets
    /// the field incrementally instead (`if old_link == nil { set_last_leaf(...) }`
    /// at `containers/src/bplus.rs:706`), which is cheaper but is exactly the
    /// bookkeeping the proof would have to mirror.
    ///
    /// Stated over an explicit subtree rather than `self.wf()`: the callers invoke
    /// it precisely when `last_leaf_ok` is the one `wf` clause not yet
    /// re-established (they are computing the value that will restore it).
    fn rightmost_leaf_of(&self, idx0: L::ArenaIdx, t: Ghost<Tree>) -> (r: L::ArenaIdx)
        requires
            self.nodes.wf(),
            binds::<L>(self.arena(), t@),
            crate::bplus_tree::tree_wf(t@, crate::bplus_tree::tree_height(t@),
                L::leaf_cap_spec(), L::key_cap_spec(), true),
            idx0.as_nat() == crate::bplus_tree::tree_root_id(t@),
        ensures r.as_nat() == crate::bplus_tree::last_leaf_id(t@),
    {
        let mut idx = idx0;
        let ghost mut cur = t@;
        let ghost mut is_root = true;
        proof {
            L::lemma_arena_capacity();
            L::lemma_geometry();
        }
        loop
            invariant
                self.nodes.wf(),
                binds::<L>(self.arena(), cur),
                crate::bplus_tree::tree_wf(cur, crate::bplus_tree::tree_height(cur),
                    L::leaf_cap_spec(), L::key_cap_spec(), is_root),
                idx.as_nat() == crate::bplus_tree::tree_root_id(cur),
                // the answer for the whole tree is the answer for the current
                // spine node: descending rightward never changes it.
                crate::bplus_tree::last_leaf_id(cur) == crate::bplus_tree::last_leaf_id(t@),
                L::leaf_cap_spec() >= 1,
            decreases crate::bplus_tree::tree_height(cur),
        {
            let ghost hc = crate::bplus_tree::tree_height(cur);
            // `lemma_inner_facts` wants the root form, which is the WEAKER one (it
            // drops the minimum-occupancy bound); lift a descended child into it.
            proof {
                if !is_root {
                    crate::bplus_tree::lemma_tree_wf_relax_root(
                        cur, hc, L::leaf_cap_spec(), L::key_cap_spec());
                }
            }
            // in range: `binds` states `id < arena.len()` in both arms, and
            // `idx == tree_root_id(cur)`.
            proof { assert(idx.as_nat() < self.arena().len()); }
            let node = self.nodes.get_index(idx);
            if L::is_leaf(&node) {
                // a leaf IS its own rightmost leaf.
                proof {
                    match cur {
                        Tree::Leaf { id, .. } => { assert(id == idx.as_nat()); }
                        Tree::Inner { id, .. } => {
                            // binds' Inner arm says arena[id] is NOT a leaf.
                            assert(!L::is_leaf_spec(self.arena()[id as int]));
                            assert(false);
                        }
                    }
                }
                return idx;
            }
            // internal: descend to the LAST child (index `count`, one past the
            // last separator — the child with no upper separator bound).
            let n = L::count(&node);
            proof {
                match cur {
                    Tree::Leaf { id, .. } => {
                        assert(L::is_leaf_spec(self.arena()[id as int]));
                        assert(false);
                    }
                    Tree::Inner { id, seps, kids } => {
                        lemma_inner_facts::<L>(self.arena(), id, seps, kids, hc);
                        assert(n as nat == seps.len());
                        assert(kids.len() == seps.len() + 1);
                        lemma_inner_binds_child::<L>(self.arena(), id, seps, kids, n as int);
                        crate::bplus_tree::lemma_forest_wf_at(
                            kids, (hc - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), n as int);
                        crate::bplus_tree::lemma_tree_wf_height(
                            kids[n as int], (hc - 1) as nat, L::leaf_cap_spec(), L::key_cap_spec(), false);
                    }
                }
            }
            let child = L::child(&node, n);
            proof {
                let kids = cur->Inner_kids;
                // last_leaf_id(Inner) is definitionally last_leaf_id of the LAST
                // child, which is kids[seps.len()] == kids[n].
                assert(kids.len() - 1 == n as int);
                cur = kids[n as int];
                is_root = false;
            }
            idx = child;
        }
    }

    /// `find_ge` over a leaf node's keys: first index `r` with `keys[r] >= word`.
    /// Dispatches to `S::find_ge` on the node's live key prefix (production's
    /// `S::find_ge(&L::data(&leaf)[..n], word)`), then lifts the split point onto
    /// the ghost key view: everything left of `r` is `< word`, everything from
    /// `r` on is `>= word`. `r <= count`.
    fn leaf_find_ge(&self, node: &L::Node, word: L::Word) -> (r: usize)
        requires
            L::node_wf(*node),
            L::is_leaf_spec(*node),
            // the leaf's keys are strictly sorted (its tree_wf leaf arm); implies
            // the non-strict `sorted_le` that `S::find_ge` requires.
            crate::bplus_tree::strictly_sorted(
                Seq::new(L::keys_view(*node).len(), |i: int| L::keys_view(*node)[i].as_nat())),
        ensures
            r <= L::count_spec(*node),
            forall|i: int| 0 <= i < r ==> (#[trigger] L::keys_view(*node)[i]).as_nat() < word.as_nat(),
            forall|i: int| r <= i < L::count_spec(*node) ==> word.as_nat() <= (#[trigger] L::keys_view(*node)[i]).as_nat(),
    {
        let ghost ks = Seq::new(L::keys_view(*node).len(), |i: int| L::keys_view(*node)[i].as_nat());
        let keys = L::keys(node);
        proof {
            L::lemma_keys_view_len(*node);
            // strict order (over as_nat) weakens to the sorted_le precondition.
            assert forall|i: int, j: int| 0 <= i <= j < keys@.len() implies
                (#[trigger] keys@[i].as_nat()) <= (#[trigger] keys@[j].as_nat()) by {
                if i < j { assert(ks[i] < ks[j]); }  // strictly_sorted
            }
            assert(crate::bplus_search::sorted_le(keys@));
        }
        let r = S::find_ge(keys, word);
        proof {
            // `keys@ == keys_view(node)` (L::keys ensures), so S::find_ge's
            // split-point ensures transfer to the ghost key view verbatim.
            assert forall|i: int| 0 <= i < r implies
                (#[trigger] L::keys_view(*node)[i]).as_nat() < word.as_nat() by {
                assert(keys@[i].as_nat() < word.as_nat());
            }
            assert forall|i: int| r <= i < L::count_spec(*node) implies
                word.as_nat() <= (#[trigger] L::keys_view(*node)[i]).as_nat() by {
                assert(word.as_nat() <= keys@[i].as_nat());
            }
        }
        r
    }

    /// `find_gt` over an internal node's separators: first child index `cp` such
    /// that `word < seps[cp]` (descend there). Dispatches to `S::find_gt` on the
    /// node's live separator prefix (production's `S::find_gt(&L::data(&nd)[..n],
    /// word)`); mirrors `leaf_find_ge` with the strict boundary. Every separator
    /// left of `cp` is `<= word`, every one from `cp` on is `> word`, `cp <=
    /// count` (a valid child index, since kids.len() == count + 1).
    fn find_child(&self, node: &L::Node, word: L::Word) -> (cp: usize)
        requires
            L::node_wf(*node),
            !L::is_leaf_spec(*node),
            crate::bplus_tree::strictly_sorted(
                Seq::new(L::keys_view(*node).len(), |i: int| L::keys_view(*node)[i].as_nat())),
        ensures
            cp <= L::count_spec(*node),
            forall|j: int| 0 <= j < cp ==> (#[trigger] L::keys_view(*node)[j]).as_nat() <= word.as_nat(),
            forall|j: int| cp <= j < L::count_spec(*node) ==> word.as_nat() < (#[trigger] L::keys_view(*node)[j]).as_nat(),
    {
        let ghost ks = Seq::new(L::keys_view(*node).len(), |i: int| L::keys_view(*node)[i].as_nat());
        let keys = L::keys(node);
        proof {
            L::lemma_keys_view_len(*node);
            assert forall|i: int, j: int| 0 <= i <= j < keys@.len() implies
                (#[trigger] keys@[i].as_nat()) <= (#[trigger] keys@[j].as_nat()) by {
                if i < j { assert(ks[i] < ks[j]); }  // strictly_sorted
            }
            assert(crate::bplus_search::sorted_le(keys@));
        }
        let cp = S::find_gt(keys, word);
        proof {
            // Same transfer as leaf_find_ge's, at the `<=` / `<` boundary.
            assert forall|j: int| 0 <= j < cp implies
                (#[trigger] L::keys_view(*node)[j]).as_nat() <= word.as_nat() by {
                assert(keys@[j].as_nat() <= word.as_nat());
            }
            assert forall|j: int| cp <= j < L::count_spec(*node) implies
                word.as_nat() < (#[trigger] L::keys_view(*node)[j]).as_nat() by {
                assert(word.as_nat() < keys@[j].as_nat());
            }
        }
        cp
    }

    /// Descend root→leaf to the leaf that would hold `word`, returning
    /// `(leaf, pos, gm)`. Proven: the descent lands on chain leaf `gm` with `leaf
    /// == tree_leaf_ids[gm]`, `pos == leaf_find_ge` within it, and the GLOBAL
    /// position `chain_offset(gm) + pos == seek_target_idx(model, word)`. So a
    /// caller positioning at `(leaf, pos)` is at the first model key `>= word`
    /// (modulo `pos == |leaf|`, target past this leaf — handled by the caller via
    /// `link`). The descent maintains `acc == chain_offset(gm)` and `acc +
    /// seek_target_idx(tree_keys(cur)) == seek_target_idx(model)`; each step uses
    /// lemma_seek_idx_descent (model split) + lemma_chain_offset_child (acc law).
    pub(crate) fn seek_leaf(&self, word: L::Word) -> (res: (L::ArenaIdx, usize, Ghost<int>))
        requires self.wf(),
        ensures
            ({
                let lids = crate::bplus_tree::tree_leaf_ids(self.tree@);
                let gm = res.2@;
                &&& 0 <= gm < lids.len()
                &&& res.0.as_nat() == lids[gm]
                &&& res.1 <= leaf_word_keys::<L>(self.arena(), lids[gm]).len()
                &&& (chain_offset::<L>(self.arena(), lids, gm) + res.1)
                        == seek_target_idx(self.model(), word.as_nat())
            }),
    {
        let ghost lids = crate::bplus_tree::tree_leaf_ids(self.tree@);
        let mut idx = self.root;
        let ghost cur = self.tree@;
        let ghost gm: int = 0;
        let ghost acc: int = 0;
        let mut done = false;
        proof {
            L::lemma_arena_capacity();
            crate::bplus_tree::lemma_tree_wf_sorted(cur, crate::bplus_tree::tree_height(cur),
                L::leaf_cap_spec(), L::key_cap_spec(), true);
            crate::bplus_tree::lemma_tree_leaf_ids_nonempty(cur,
                crate::bplus_tree::tree_height(cur), L::leaf_cap_spec(), L::key_cap_spec(), true);
            // initial alignment: lids[0 + q] == tree_leaf_ids(cur)[q] (cur == tree@).
        }
        let ret_pos;
        while !done
            invariant
                self.wf(),
                lids == crate::bplus_tree::tree_leaf_ids(self.tree@),
                idx.as_nat() == crate::bplus_tree::tree_root_id(cur),
                binds::<L>(self.arena(), cur),
                crate::bplus_tree::tree_wf(cur, crate::bplus_tree::tree_height(cur),
                    L::leaf_cap_spec(), L::key_cap_spec(), true),
                0 <= gm,
                gm + crate::bplus_tree::tree_leaf_ids(cur).len() <= lids.len(),
                crate::bplus_tree::tree_leaf_ids(cur).len() >= 1,
                // alignment: cur's leaves are the chain sub-block at gm.
                forall|q: int| 0 <= q < crate::bplus_tree::tree_leaf_ids(cur).len()
                    ==> lids[gm + q] == #[trigger] crate::bplus_tree::tree_leaf_ids(cur)[q],
                acc == chain_offset::<L>(self.arena(), lids, gm),
                acc + seek_target_idx(crate::bplus_tree::tree_keys(cur), word.as_nat())
                    == seek_target_idx(self.model(), word.as_nat()),
                done ==> cur is Leaf,
            decreases crate::bplus_tree::tree_height(cur), (if done { 0int } else { 1int }),
        {
            let node = self.nodes.get_index(idx);
            proof { assert(self.arena()[idx.as_nat() as int] == node); }
            if L::is_leaf(&node) {
                proof {
                    match cur {
                        Tree::Leaf { .. } => {}
                        Tree::Inner { .. } => { assert(!L::is_leaf_spec(self.arena()[idx.as_nat() as int])); assert(false); }
                    }
                }
                done = true;
                continue;
            }
            // internal: pick descent child cp = find_gt(seps, word), then descend.
            let ghost h = crate::bplus_tree::tree_height(cur);
            let ghost kids = cur->Inner_kids;
            proof {
                assert(crate::bplus_tree::tree_root_id(cur) == idx.as_nat());  // loop inv
                assert(node == self.arena()[idx.as_nat() as int]);            // get ensures
                // cur is Inner (node not a leaf + binds); lemma_inner_facts gives
                // node_wf + !is_leaf(node) (find_child's requires), before the call.
                match cur {
                    Tree::Leaf { .. } => { assert(L::is_leaf_spec(node)); assert(false); }
                    Tree::Inner { .. } => {}
                }
                lemma_inner_facts::<L>(self.arena(), idx.as_nat(), cur->Inner_seps, kids, h);
                lemma_tree_wf_sorted_seps_view::<L>(self.arena(), cur, idx.as_nat(), node);
            }
            let cp = self.find_child(&node, word);
            proof {
                // find_child's separator characterization feeds the descent step.
                seek_descend_step::<K, L, S, TRACK>(self, cur, node, word, cp as int, gm, acc, Ghost(lids));
            }
            let ghost new_acc = acc + crate::bplus_tree::forest_keys(kids.subrange(0, cp as int)).len() as int;
            let ghost new_gm = gm + crate::bplus_tree::leaf_id_offset(kids, cp as int) as int;
            idx = L::child(&node, cp);
            proof {
                // child height is h-1 < h, so the descent decreases tree_height(cur).
                crate::bplus_tree::lemma_forest_wf_at(kids, (h - 1) as nat,
                    L::leaf_cap_spec(), L::key_cap_spec(), cp as int);
                crate::bplus_tree::lemma_tree_wf_relax_root(kids[cp as int], (h - 1) as nat,
                    L::leaf_cap_spec(), L::key_cap_spec());
                crate::bplus_tree::lemma_tree_wf_height(kids[cp as int], (h - 1) as nat,
                    L::leaf_cap_spec(), L::key_cap_spec(), true);
                cur = kids[cp as int];
                gm = new_gm;
                acc = new_acc;
            }
        }
        // at the leaf: leaf_find_ge gives pos == seek_target_idx(tree_keys(cur), word).
        let node = self.nodes.get_index(idx);
        proof {
            // cur is a Leaf (done invariant); its keys are sorted (tree_wf), and
            // keys_view(node) projects to them — leaf_find_ge's split == seek index.
            assert(crate::bplus_tree::tree_root_id(cur) == idx.as_nat());  // loop inv
            assert(node == self.arena()[idx.as_nat() as int]);            // get ensures
            // cur is Leaf (done inv) ⟹ node is a leaf + node_wf (binds leaf facts),
            // which leaf_find_ge requires.
            match cur {
                Tree::Leaf { id: lid, keys } => {
                    lemma_binds_leaf_facts::<L>(self.arena(), lid, keys,
                        crate::bplus_tree::tree_height(cur));
                }
                Tree::Inner { .. } => { assert(false); }
            }
            lemma_tree_wf_sorted_seps_view::<L>(self.arena(), cur, idx.as_nat(), node);
        }
        let p = self.leaf_find_ge(&node, word);
        ret_pos = p;
        proof {
            seek_leaf_finish::<K, L, S, TRACK>(self, cur, node, word, p, gm, acc, Ghost(lids));
        }
        (idx, ret_pos, Ghost(gm))
    }
}


impl<'a, K, L, S, const TRACK: bool> BPlusCursor<'a, K, L, S, TRACK>
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
{
    /// NIL leaf sentinel (`max_nat - 1` == `max_spec`), matching `new_leaf`'s
    /// terminator (`link == max_nat - 1`). `IndexLike::max()` is exactly that
    /// value (`lemma_max_as_nat`), so the sentinel's nat IS `nil_link`.
    fn nil() -> (r: L::ArenaIdx)
        ensures r.as_nat() == nil_link::<L>(),
    {
        proof { <L::ArenaIdx as IndexLike>::lemma_max_as_nat(); }
        <L::ArenaIdx as IndexLike>::max()
    }

    /// A fresh cursor over a `wf` tree, positioned at the EXHAUSTED end (`node ==
    /// NIL`, `idx == |model|`). `cursor_wf` holds immediately, so `seek` /
    /// `seek_first` can be called right away. (Production says "positioned
    /// nowhere"; modeling it as the well-formed exhausted state is what lets the
    /// fast path in `seek` trust `node != NIL` ⟹ positioned.)
    pub fn new(tree: &'a BPlusTreeSet<K, L, S, TRACK>) -> (c: Self)
        requires tree.wf(),
        ensures c.tree_ref() == tree, c.cursor_wf(), c.idx() == c.model().len(),
    {
        let nilv = Self::nil();   // nilv.as_nat() == nil_link
        let c = BPlusCursor {
            tree, node: nilv, pos: 0,
            gidx: Ghost(crate::bplus_tree::tree_keys(tree.tree@).len() as int),
            gleaf: Ghost(0),
            _k: core::marker::PhantomData,
        };
        proof {
            // exhausted arm of cursor_wf: node == nil_link, gidx == |model|.
            assert(c.node.as_nat() == nil_link::<L>());
            assert(c.gidx@ == c.model().len());
        }
        c
    }

    /// The cursor's model index (`gidx`), as a convenience for specs.
    pub open(crate) spec fn idx(self) -> int { self.gidx@ }

    /// The tree this cursor walks (spec twin; the field is `pub(crate)` —
    /// privacy closeout).
    pub open(crate) spec fn tree_ref(self) -> &'a BPlusTreeSet<K, L, S, TRACK> {
        self.tree
    }

    /// The tree's in-order model (the sorted set).
    pub open(crate) spec fn model(self) -> Seq<nat> { crate::bplus_tree::tree_keys(self.tree.tree@) }

    /// Cursor well-formedness: `(node, pos)` realizes model index `gidx`. Either
    /// EXHAUSTED — `gidx == |model|`, `node == NIL` — or POSITIONED on chain-leaf
    /// `gleaf`: that leaf id is `node`, `pos` indexes into it, and the flat model
    /// index is `chain_offset(gleaf) + pos == gidx`. Holds against a `wf` tree.
    pub open(crate) spec fn cursor_wf(self) -> bool {
        let lids = crate::bplus_tree::tree_leaf_ids(self.tree.tree@);
        let arena = self.tree.arena();
        &&& self.tree.wf()
        &&& 0 <= self.gidx@ <= self.model().len()
        &&& (self.node.as_nat() == nil_link::<L>() ==> self.gidx@ == self.model().len())
        &&& (self.node.as_nat() != nil_link::<L>() ==> {
                &&& 0 <= self.gleaf@ < lids.len()
                &&& self.node.as_nat() == lids[self.gleaf@]
                &&& self.pos < leaf_word_keys::<L>(arena, lids[self.gleaf@]).len()
                &&& self.gidx@ == chain_offset::<L>(arena, lids, self.gleaf@) + self.pos
            })
    }

    /// Position at the first model key `>= target` (leapfrog `seek`): establishes
    /// `cursor_wf` with `idx() == seek_target_idx(model, target)`. Verified via the
    /// root-descent `seek_leaf`, which returns the chain leaf `gm` and within-leaf
    /// position whose global index is `seek_target_idx`; if the position is past
    /// that leaf's keys (`pos == |leaf gm|`, target falls between leaves), advance
    /// over the end via `link` to leaf `gm+1` (or NIL), exactly as `step` does.
    ///
    /// (Production additionally has an O(1)-amortized fast path that checks the
    /// current / immediately-next leaf before descending; that is a performance
    /// optimization, omitted from the verified version, which always descends. The
    /// observable result is identical; the fast path is exercised by the property
    /// tests on the production-shaped exec.)
    pub fn seek(&mut self, target: K)
        requires old(self).cursor_wf(),
        ensures
            final(self).cursor_wf(),
            final(self).tree_ref() == old(self).tree_ref(),
            final(self).idx() == seek_target_idx(final(self).model(), target.id_nat()),
    {
        let word: L::Word = target.to_index();    // word.as_nat() == target.id_nat()
        let ghost lids = crate::bplus_tree::tree_leaf_ids(self.tree.tree@);
        let ghost ti = seek_target_idx(self.model(), target.id_nat());
        let (leaf, pos, gm) = self.tree.seek_leaf(word);
        // seek_leaf: leaf == lids[gm@], pos <= |leaf gm@|, chain_offset(gm@)+pos == ti.
        proof {
            // leaf == lids[gm@] is a real leaf id, so it is in arena range (for get).
            lemma_cursor_node_wf_at::<K, L, S, TRACK>(self.tree, gm@);
            assert(leaf.as_nat() == lids[gm@]);
            assert(leaf.as_nat() < self.tree.arena().len());
        }
        let node = self.tree.nodes.get_index(leaf);
        let cnt = L::count(&node);
        proof {
            assert(node == self.tree.arena()[leaf.as_nat() as int]);  // get ensures
            L::lemma_keys_view_len(node);
        }
        if pos < cnt {
            // target falls within leaf gm@ at pos: position there, idx == ti.
            self.node = leaf;
            self.pos = pos;
            proof {
                self.gleaf@ = gm@;
                self.gidx@ = ti;
                seek_finish_in_leaf::<K, L, S, TRACK>(self, old(self), gm@, pos, target.id_nat());
            }
        } else {
            // pos == |leaf gm@|: target is past leaf gm@'s keys. Advance over the
            // end via link to leaf gm@+1 (or NIL), at pos 0 — idx still ti.
            let link = L::link(&node);
            self.node = link;
            self.pos = 0;
            proof {
                self.gidx@ = ti;
                self.gleaf@ = gm@ + 1;   // the next chain leaf (ignored when exhausted)
                seek_finish_over_end::<K, L, S, TRACK>(self, old(self), node, gm@, target.id_nat());
            }
        }
    }

    /// Position at the smallest key in the set (model index 0), or exhausted if
    /// the set is empty. Descends child 0 from the root to the leftmost leaf
    /// (`tree_leaf_ids[0]`), then sits at position 0 — establishing `cursor_wf`
    /// with `gidx == 0` (or `gidx == |model| == 0` for the empty tree). The
    /// enumeration entry point: `seek_first` then `step`* reads the sorted set.
    pub fn seek_first(&mut self)
        requires old(self).tree_ref().wf(),
        ensures
            final(self).cursor_wf(),
            final(self).tree_ref() == old(self).tree_ref(),
            final(self).idx() == 0,
    {
        let mut idx = self.tree.root;
        let ghost cur = self.tree.tree@;
        let mut done = false;
        proof {
            // initial invariant from wf: root id, binds, tree_wf (root form), and
            // cur == tree@ so the leftmost-leaf equality is reflexive.
            L::lemma_arena_capacity();
            assert(idx.as_nat() == crate::bplus_tree::tree_root_id(cur));  // wf root-id
            crate::bplus_tree::lemma_tree_leaf_ids_nonempty(cur,
                crate::bplus_tree::tree_height(cur), L::leaf_cap_spec(), L::key_cap_spec(), true);
        }
        // Descent: walk child 0 to the leftmost leaf. The invariant carries that
        // `cur` is wf, binds at `idx`, its leftmost leaf is the whole tree's, and
        // (when `done`) `cur` is the Leaf we stopped at.
        while !done
            invariant
                self.tree.wf(),
                idx.as_nat() == crate::bplus_tree::tree_root_id(cur),
                binds::<L>(self.tree.arena(), cur),
                crate::bplus_tree::tree_wf(cur, crate::bplus_tree::tree_height(cur),
                    L::leaf_cap_spec(), L::key_cap_spec(), true),
                crate::bplus_tree::tree_leaf_ids(cur).len() >= 1,
                crate::bplus_tree::tree_leaf_ids(cur)[0]
                    == crate::bplus_tree::tree_leaf_ids(self.tree.tree@)[0],
                done ==> cur is Leaf,
            // lexicographic: descending a child cuts tree_height(cur); setting
            // `done` (without descending) cuts the second component to 0.
            decreases crate::bplus_tree::tree_height(cur), (if done { 0int } else { 1int }),
        {
            let node = self.tree.nodes.get_index(idx);
            proof { assert(self.tree.arena()[idx.as_nat() as int] == node); }
            if L::is_leaf(&node) {
                // is_leaf(arena[idx]) + binds(cur) at idx ⟹ cur is Leaf (the binds
                // Inner arm would force !is_leaf). Record it in the `done` invariant.
                proof {
                    match cur {
                        Tree::Leaf { .. } => {}
                        Tree::Inner { .. } => {
                            assert(!L::is_leaf_spec(self.tree.arena()[idx.as_nat() as int]));  // binds Inner arm
                            assert(false);
                        }
                    }
                }
                done = true;
                continue;
            }
            // internal: descend child 0. lemma_inner_first_leaf pins the leftmost
            // leaf to child 0's; lemma_inner_child_subtree_wf gives the child wf.
            let ghost h = crate::bplus_tree::tree_height(cur);
            proof {
                L::lemma_arena_capacity();
                // node is internal and binds cur ⟹ cur is Inner (binds Inner arm).
                assert(!L::is_leaf_spec(self.tree.arena()[idx.as_nat() as int]));
                match cur {
                    Tree::Leaf { .. } => { assert(false); }   // binds would force is_leaf
                    Tree::Inner { .. } => {}
                }
                assert(cur == (Tree::Inner { id: crate::bplus_tree::tree_root_id(cur),
                    seps: cur->Inner_seps, kids: cur->Inner_kids }));
                crate::bplus_tree::lemma_inner_first_leaf(cur, h, L::leaf_cap_spec(), L::key_cap_spec());
                lemma_inner_facts::<L>(self.tree.arena(),
                    crate::bplus_tree::tree_root_id(cur), cur->Inner_seps, cur->Inner_kids, h);
                // child 0 binds (forest binds projection) + is wf at h-1 (forest_wf
                // cons), relaxed to root form for the loop. Leftmost leaf carried by
                // lemma_inner_first_leaf. (No links/disjoint needed — seek_first
                // only reads binds + tree_wf + the leftmost-leaf id.)
                lemma_inner_binds_child::<L>(self.tree.arena(),
                    crate::bplus_tree::tree_root_id(cur), cur->Inner_seps, cur->Inner_kids, 0);
                crate::bplus_tree::lemma_forest_wf_cons(cur->Inner_kids, (h - 1) as nat,
                    L::leaf_cap_spec(), L::key_cap_spec());
                crate::bplus_tree::lemma_tree_wf_height(cur->Inner_kids[0], (h - 1) as nat,
                    L::leaf_cap_spec(), L::key_cap_spec(), false);
                crate::bplus_tree::lemma_tree_wf_relax_root(cur->Inner_kids[0], (h - 1) as nat,
                    L::leaf_cap_spec(), L::key_cap_spec());
            }
            let cp0: usize = 0;
            idx = L::child(&node, cp0);
            proof { cur = cur->Inner_kids[0]; }
        }
        // at the leftmost leaf `idx` (== tree_leaf_ids(tree@)[0]).
        let node = self.tree.nodes.get_index(idx);
        let cnt = L::count(&node);
        let ghost lids = crate::bplus_tree::tree_leaf_ids(self.tree.tree@);
        let nil = Self::nil();
        proof {
            // cur is the leaf; binds gives its arena node; leaf is tree_leaf_ids[0].
            match cur {
                Tree::Leaf { id, keys } => {
                    assert(idx.as_nat() == id);
                    assert(crate::bplus_tree::tree_leaf_ids(cur) =~= seq![id]);
                    assert(lids[0] == id);                          // loop inv: cur's leftmost == tree's
                    assert(node == self.tree.arena()[id as int]);   // get ensures + idx==id
                    lemma_binds_leaf_facts::<L>(self.tree.arena(), id, keys,
                        crate::bplus_tree::tree_height(cur));
                    L::lemma_keys_view_len(self.tree.arena()[id as int]);
                    // cnt == count(node) == count_spec(arena[id]) == |keys_view| ==
                    // |leaf_word_keys(arena, id)| == |leaf_word_keys(arena, lids[0])|.
                    assert(cnt as nat == L::count_spec(self.tree.arena()[id as int]));
                    assert(cnt == leaf_word_keys::<L>(self.tree.arena(), lids[0]).len());
                }
                Tree::Inner { .. } => { assert(false); }  // loop exits only at a leaf
            }
        }
        if cnt > 0 {
            // non-empty leftmost leaf: position (leaf, 0) at model index 0.
            self.node = idx;
            self.pos = 0;
            proof {
                self.gleaf@ = 0;
                self.gidx@ = 0;
                // node == lids[0]; pos 0 < cnt; chain_offset(0)+0 == 0; node != nil.
                assert(self.node.as_nat() == lids[0]);
                lemma_chain_leaf_binds::<L>(self.tree.arena(), self.tree.tree@,
                    crate::bplus_tree::tree_height(self.tree.tree@), true, 0);
                assert(self.node.as_nat() < self.tree.arena().len());
                assert(self.node.as_nat() != nil_link::<L>());  // wf arena bound
                assert(self.gidx@ == chain_offset::<L>(self.tree.arena(), lids, 0) + self.pos);
                // gidx 0 <= |model|; model nonempty since leaf 0 has a key.
                lemma_chain_keys_slice::<L>(self.tree.arena(), lids, 0);
                lemma_chain_keys_eq_model::<L>(self.tree.arena(), self.tree.tree@);
                assert(0 <= self.gidx@ < self.model().len());
            }
        } else {
            // empty leftmost leaf ⟹ empty model; exhausted. (If lids.len() >= 2 the
            // tree is Inner and EVERY leaf is non-root hence non-empty — so leaf 0
            // empty forces lids.len() == 1, i.e. a single root leaf, model empty.)
            self.node = nil;
            self.pos = 0;
            proof {
                self.gidx@ = 0;
                assert(cnt == leaf_word_keys::<L>(self.tree.arena(), lids[0]).len());  // == 0
                if lids.len() >= 2 {
                    lemma_cursor_next_leaf_nonempty::<K, L, S, TRACK>(self.tree, 0);  // leaf 0 >= 1: contra
                    assert(false);
                }
                assert(lids.len() == 1);
                // chain_offset(lids, 1) == chain_offset(lids,0) + |leaf 0| == 0 + cnt == 0
                // (offset def at m==1); and chain_offset(lids, len) == chain_keys.len.
                assert(chain_offset::<L>(self.tree.arena(), lids, 1)
                    == chain_offset::<L>(self.tree.arena(), lids, 0)
                        + leaf_word_keys::<L>(self.tree.arena(), lids[0]).len());
                lemma_chain_offset_full::<L>(self.tree.arena(), lids);  // chain_offset(1) == chain_keys.len
                lemma_chain_keys_eq_model::<L>(self.tree.arena(), self.tree.tree@);  // chain_keys == model
                assert(self.model().len() == 0);
                assert(self.node.as_nat() == nil_link::<L>());
            }
        }
    }

    /// The current key, or `None` if exhausted. Under `cursor_wf`, returns
    /// `Some(k)` with `k.id_nat() == model[idx]` when positioned (`idx < |model|`),
    /// and `None` exactly when exhausted (`idx == |model|`). This is the
    /// enumeration-read half of the leapfrog cursor's soundness.
    pub fn key(&self) -> (r: Option<K>)
        requires self.cursor_wf(),
        ensures
            self.idx() < self.model().len() ==> (match r {
                Some(k) => k.id_nat() == self.model()[self.idx()],
                None => false,
            }),
            self.idx() == self.model().len() ==> r is None,
    {
        let nil = Self::nil();
        if self.node.as_usize() == nil.as_usize() {
            // exhausted: as_usize equality ⟹ as_nat equality ⟹ node == nil_link,
            // and cursor_wf's NIL arm gives idx == |model|.
            proof { assert(self.node.as_nat() == nil_link::<L>()); }
            return None;
        }
        // positioned: read leaf `node`'s `pos`-th key and project to K.
        proof {
            assert(self.node.as_nat() != nil_link::<L>());
            lemma_cursor_node_wf::<K, L, S, TRACK>(self);  // node_wf(arena[node]), node in range
        }
        let node = self.tree.nodes.get_index(self.node);
        let ghost lids = crate::bplus_tree::tree_leaf_ids(self.tree.tree@);
        proof {
            // pos < count(node) == |leaf_word_keys(node)| (cursor_wf positioned arm).
            L::lemma_keys_view_len(node);
        }
        let w = L::key(&node, self.pos);
        let wu = w.as_usize();  // wu as nat == w.as_nat() (as_usize ensures)
        let r = K::from_usize(wu);
        proof {
            // positioned ⟹ gidx < |model|: gidx == chain_offset(gleaf) + pos, and
            // that flat index is a valid chain_keys index (slice bound) == |model|.
            let arena = self.tree.arena();
            let m = self.gleaf@;
            lemma_chain_keys_slice::<L>(arena, lids, m);   // offset + pos < chain_keys.len
            lemma_chain_keys_eq_model::<L>(arena, self.tree.tree@);  // chain_keys == model
            assert(self.gidx@ < self.model().len());
            // w.as_nat() == leaf_word_keys(node)[pos] == model[gidx] (slice + B2).
            lemma_cursor_key_at::<K, L, S, TRACK>(self);
            assert(w.as_nat() == self.model()[self.gidx@]);
            // model values are in id_bound, so from_usize round-trips.
            lemma_model_value_bounded::<K, L, S, TRACK>(self.tree, self.gidx@);
            assert((wu as nat) < K::id_bound());          // wu as nat == w.as_nat()
            assert(r.id_nat() == wu as nat);              // from_usize roundtrip
        }
        Some(r)
    }

    /// Advance to the next key in sorted order (following `link` at a leaf end).
    /// Preserves `cursor_wf` and advances the model index by one (or stays at the
    /// exhausted end). With `key()`, this enumerates the sorted set in order: the
    /// `step`-by-`step` walk from `seek_first` visits model[0], model[1], ... .
    pub fn step(&mut self)
        requires old(self).cursor_wf(),
        ensures
            final(self).cursor_wf(),
            final(self).tree_ref() == old(self).tree_ref(),
            // advance by one, clamped at the exhausted end (idx == |model|).
            final(self).idx() == if old(self).idx() < old(self).model().len() {
                old(self).idx() + 1
            } else {
                old(self).idx()
            },
    {
        let nil = Self::nil();
        let ghost lids = crate::bplus_tree::tree_leaf_ids(self.tree.tree@);
        let ghost arena = self.tree.arena();
        if self.node.as_usize() == nil.as_usize() {
            // exhausted: idx == |model| already (cursor_wf NIL arm); no-op.
            proof {
                assert(self.node.as_nat() == nil_link::<L>());
                assert(self.cursor_wf());  // unchanged from old(self)
            }
            return;
        }
        // positioned. Read the current leaf; advance within it, or follow `link`.
        proof { lemma_cursor_node_wf::<K, L, S, TRACK>(self); }
        let node = self.tree.nodes.get_index(self.node);
        let cnt = L::count(&node);
        let ghost m = self.gleaf@;
        proof {
            L::lemma_keys_view_len(node);
            // cnt == |leaf m| ; pos < cnt (cursor_wf positioned arm).
            assert(cnt == leaf_word_keys::<L>(arena, lids[m]).len());
            // idx < |model| on the positioned branch (slice bound + B2).
            lemma_chain_keys_slice::<L>(arena, lids, m);
            lemma_chain_keys_eq_model::<L>(arena, self.tree.tree@);
            assert(self.gidx@ < self.model().len());
        }
        self.pos = self.pos + 1;
        proof { self.gidx@ = self.gidx@ + 1; }
        if self.pos >= cnt {
            // ran off leaf m (pos was cnt-1, now == cnt): follow link to leaf m+1
            // (or NIL). `leaf_links_ok` (a wf clause) pins link(arena[lids[m]]) ==
            // (m+1 < len ? lids[m+1] : nil_link).
            let link = L::link(&node);
            self.node = link;
            self.pos = 0;
            proof {
                assert(self.pos == 0 && cnt >= 1);  // pos+1 >= cnt and pos was < cnt
                // gidx == chain_offset(m) + cnt == chain_offset(m+1)  (offset def).
                assert(self.gidx@ == chain_offset::<L>(arena, lids, m) + cnt);
                assert(chain_offset::<L>(arena, lids, m + 1)
                    == chain_offset::<L>(arena, lids, m) + leaf_word_keys::<L>(arena, lids[m]).len());
                assert(self.gidx@ == chain_offset::<L>(arena, lids, m + 1));
                // leaf_links_ok at p == m: link == lids[m+1] (or nil_link if last).
                assert(leaf_links_ok::<L>(arena, self.tree.tree@));
                assert(L::link_view(arena[lids[m] as int])
                    == (if m + 1 < lids.len() { lids[m + 1] } else { nil_link::<L>() }));
                assert(link.as_nat() == L::link_view(arena[lids[m] as int]));
                self.gleaf@ = m + 1;
                if m + 1 < lids.len() {
                    // positioned at leaf m+1, pos 0: node == lids[m+1], and leaf m+1
                    // is non-empty so pos 0 < |leaf m+1| (multi-leaf ⟹ Inner ⟹ every
                    // leaf non-root, hence >= 1 key).
                    assert(self.node.as_nat() == lids[m + 1]);
                    assert(lids.len() >= 2);  // m >= 0 and m+1 < len
                    lemma_cursor_next_leaf_nonempty::<K, L, S, TRACK>(self.tree, m + 1);
                    assert(self.node.as_nat() != nil_link::<L>());  // lids[m+1] real (wf arena bound)
                    assert(self.gleaf@ == m + 1);
                    assert(self.pos < leaf_word_keys::<L>(arena, lids[self.gleaf@]).len());
                    assert(self.gidx@ == chain_offset::<L>(arena, lids, self.gleaf@) + self.pos);
                    // upper bound: gidx == offset(m+1)+0 < |model| (slice at m+1 + B2).
                    lemma_chain_keys_slice::<L>(arena, lids, m + 1);
                    lemma_chain_keys_eq_model::<L>(arena, self.tree.tree@);
                    assert(0 <= self.gidx@ < self.model().len());
                    assert(self.cursor_wf());  // positioned at next leaf
                } else {
                    // exhausted: node == nil_link, gidx == chain_offset(len) == |model|.
                    assert(self.node.as_nat() == nil_link::<L>());
                    lemma_chain_offset_full::<L>(arena, lids);  // chain_offset(len) == |chain_keys|
                    lemma_chain_keys_eq_model::<L>(arena, self.tree.tree@);
                    assert(self.gidx@ == self.model().len());
                    assert(self.cursor_wf());  // exhausted
                }
            }
        } else {
            // stayed within leaf m: node/gleaf unchanged, pos < cnt == |leaf m|,
            // gidx == chain_offset(m) + pos. cursor_wf positioned arm holds.
            proof {
                assert(self.node.as_nat() != nil_link::<L>());        // node unchanged from positioned old
                assert(self.gleaf@ == m && 0 <= m < lids.len());
                assert(self.node.as_nat() == lids[m]);
                assert(self.pos < cnt);                                // loop guard else
                assert(cnt == leaf_word_keys::<L>(arena, lids[m]).len());
                assert(self.gidx@ == chain_offset::<L>(arena, lids, m) + self.pos);
                // upper bound gidx <= |model|: offset(m)+pos < offset(m)+cnt ==
                // offset(m+1) <= chain_keys.len == |model| (slice bound + B2).
                lemma_chain_keys_slice::<L>(arena, lids, m);
                lemma_chain_keys_eq_model::<L>(arena, self.tree.tree@);
                assert(0 <= self.gidx@ < self.model().len());
                // node != nil_link, so cursor_wf reduces to the positioned arm,
                // whose four conjuncts are all established above.
                assert(self.node.as_nat() != nil_link::<L>());
                assert(0 <= self.gleaf@ < lids.len());
                assert(self.node.as_nat() == lids[self.gleaf@]);
                assert(self.pos < leaf_word_keys::<L>(arena, lids[self.gleaf@]).len());
                assert(self.gidx@ == chain_offset::<L>(arena, lids, self.gleaf@) + self.pos);
                assert(self.cursor_wf());  // within-leaf branch
            }
        }
    }

    // =====================================================================
    // TOP-LEVEL SOUNDNESS THEOREMS for the seek/traversal cursor.
    //
    // These name the two end-to-end guarantees the whole B+tree exists to
    // provide, each a composition of the already-proven cursor contracts
    // (`seek_first`/`seek`/`step`/`key`) with the structural B-lemmas
    // (B1 sortedness, B2 chain==model, the `seek_target_idx` split). They add
    // no new axioms; they exist so the guarantee is stated once, explicitly,
    // rather than left implicit in the scattered `ensures`.
    // =====================================================================

    /// TRAVERSAL SOUNDNESS (in-order, no skips, no duplicates).
    ///
    /// For any `cursor_wf` cursor sitting at model index `n == idx()` with
    /// `n < |model|`, `key()` returns exactly `model[n]` and `step()` moves to
    /// `n + 1`. Chained from `seek_first` (which lands at `idx == 0`), this is
    /// the statement that the `key(); step()` loop enumerates
    /// `model[0], model[1], ...` — every key of the set, in strictly ascending
    /// order (the model is `strictly_sorted` by B1, so "ascending" also means
    /// "no duplicates"), terminating exactly when `idx == |model|`.
    ///
    /// This is a SPEC-level restatement: it asserts the relationship between
    /// `idx()`, `key()`'s result, and `model` that the exec `key`/`step`
    /// `ensures` already establish, plus the B1 fact that `model` is sorted, so
    /// successive reads strictly increase. No new proof obligation beyond
    /// pulling B1 into scope.
    pub(crate) proof fn theorem_traversal_in_order(self)
        requires self.cursor_wf(),
        ensures
            // the model the cursor enumerates is strictly sorted: ascending and
            // duplicate-free. (B1: `tree_wf ==> strictly_sorted(tree_keys)`.)
            crate::bplus_tree::strictly_sorted(self.model()),
            // the cursor index is always a valid position into the model or the
            // exhausted end — never out of range, so a traversal never skips off
            // the end or addresses a phantom key.
            0 <= self.idx() <= self.model().len(),
            // ASCENDING + NO SKIPS: every key the traversal reads at position i+1
            // is strictly greater than the one at i, and consecutive positions
            // differ by exactly one index — so `key(); step()` visits model[0],
            // model[1], ... with no gaps and no repeats. (Stated as the strict
            // monotonicity of the model under the +1 step, which IS what `step`'s
            // `idx == old.idx + 1` ensures composed with `key == model[idx]`.)
            forall|i: int, j: int|
                0 <= i < j < self.model().len() ==> #[trigger] self.model()[i] < #[trigger] self.model()[j],
    {
        // B1: the tree is wf (cursor_wf conjunct), so its key sequence is sorted.
        crate::bplus_tree::lemma_tree_wf_sorted(
            self.tree.tree@,
            crate::bplus_tree::tree_height(self.tree.tree@),
            L::leaf_cap_spec(),
            L::key_cap_spec(),
            true,
        );
        // strictly_sorted unfolds to exactly the ascending forall; 0 <= idx <=
        // |model| is a direct cursor_wf conjunct.
    }

    /// SEEK NEVER SKIPS A PRESENT KEY.
    ///
    /// The crux property: after `seek(target)`, if `target` is in the set the
    /// cursor lands EXACTLY on it (never steps past it). Formally, for a `wf`
    /// tree whose model contains `t == target.id_nat()`, the seek landing index
    /// `r == seek_target_idx(model, t)` satisfies `r < |model|` and
    /// `model[r] == t`. Combined with `seek`'s `ensures` (`idx() == r`) and
    /// `key`'s `ensures` (`idx() < |model| ==> key() == Some(model[idx])`), this
    /// gives: `target` present ==> after `seek(target)`, `key() == Some(target)`.
    ///
    /// For a target NOT in the set, `seek_target_idx` is still the first index
    /// with `model[r] >= t` (by `lemma_seek_target_idx_split`), i.e. seek stops
    /// on the least key `> target` (or exhausts) — it never overshoots a key it
    /// should have stopped before. So no present key is ever skipped.
    pub(crate) proof fn theorem_seek_never_skips(tree: &BPlusTreeSet<K, L, S, TRACK>, target: K)
        requires
            tree.wf(),
            tree.model().contains(target.id_nat()),
        ensures
            ({
                let r = seek_target_idx(tree.model(), target.id_nat());
                &&& 0 <= r < tree.model().len()
                &&& tree.model()[r] == target.id_nat()
            }),
    {
        let model = tree.model();
        let t = target.id_nat();
        // B1: model is strictly sorted, so seek_target_idx is the exact split.
        crate::bplus_tree::lemma_tree_wf_sorted(
            tree.tree@,
            crate::bplus_tree::tree_height(tree.tree@),
            L::leaf_cap_spec(),
            L::key_cap_spec(),
            true,
        );
        lemma_seek_target_idx_split(model, t);
        let r = seek_target_idx(model, t);
        // `t` is in the model: pick the witness position `w` with model[w] == t.
        let w = choose|w: int| 0 <= w < model.len() && model[w] == t;
        assert(model.contains(t));
        assert(0 <= w < model.len() && model[w] == t);
        // The split puts every i < r strictly below t and every i >= r at/above
        // t. The witness w has model[w] == t, so w cannot be < r (that side is
        // strictly < t). Hence r <= w < |model|, so r is a real index. And at r:
        // model[r] >= t (right side) while, were model[r] > t, strict sortedness
        // would force model[w] > t for the unique w too — but model[w] == t. So
        // r is itself a position holding t.
        assert(r <= w) by {
            if w < r {
                assert(model[w] < t);   // left side of the split
            }
        }
        assert(r < model.len());
        // model[r] >= t (right side). And model[r] <= t: r <= w and strict sort
        // gives model[r] <= model[w] == t (equal iff r == w).
        assert(t <= model[r]);          // split right side at r
        assert(model[r] <= t) by {
            if r < w { assert(model[r] < model[w]); }  // strictly_sorted
        }
    }
}

// ===== LAYER 4: mark / restore (semi-persistence) =====


/// The Phase 7 archive agreement for BPlusTreeSet, opaque (see the wf
/// comment): the header/tree archives are parallel to the arena snapshot
/// stack, each archived header round-trips through ArenaIdx, and each
/// archived (arena snapshot, header, tree) triple is `tree_state_wf`.
#[verifier::opaque]
pub open(crate) spec fn tree_archive_agrees<K, L, S, const TRACK: bool>(
    headers: Seq<(usize, usize, usize)>,
    trees: Seq<Tree>,
    arena_snaps: Seq<Seq<L::Node>>,
) -> bool
    where K: DenseId, L: NodeLayout<Word = K::Index>, S: SearchKind,
{
    &&& headers.len() == arena_snaps.len()
    &&& trees.len() == arena_snaps.len()
    &&& (forall|k: int| 0 <= k < headers.len()
            ==> (#[trigger] headers[k]).0 < <L::ArenaIdx as IndexLike>::max_nat())
    &&& (forall|k: int| 0 <= k < headers.len()
            ==> BPlusTreeSet::<K, L, S, TRACK>::tree_state_wf(
                    #[trigger] arena_snaps[k],
                    headers[k].0 as nat,
                    trees[k],
                    headers[k].1 as nat))
    // the archived `last_leaf` is the archived ghost tree's rightmost leaf, so
    // `restore` re-establishes `last_leaf_ok` from the archive alone. In range
    // for the same reason `root` is: it is a real arena slot of that snapshot.
    &&& (forall|k: int| 0 <= k < headers.len()
            ==> (#[trigger] headers[k]).2 < <L::ArenaIdx as IndexLike>::max_nat())
    &&& (forall|k: int| 0 <= k < headers.len()
            ==> (#[trigger] headers[k]).2 as nat == crate::bplus_tree::last_leaf_id(trees[k]))
}

/// Token for mark/restore. Delegates to the inner arena Vec's token, and
/// additionally snapshots the two exec header fields that live OUTSIDE the Vec
/// (`root`, `nkeys`) so `restore` can roll them back along with the arena.
#[derive(Copy, Clone)]
pub struct BPlusToken {
    pub(crate) nodes: VecToken,
    // Inert header copies (Phase 7: restore recovers the header from the
    // internal archive; these are never consulted — see `is_valid_token`).
    // Read only by spec code, which plain builds erase.
    #[allow(dead_code)]
    pub(crate) root: usize,
    #[allow(dead_code)]
    pub(crate) nkeys: usize,
}

impl BPlusToken {
    /// Reconstruction coordinate of the inner arena token (spec twin).
    pub open(crate) spec fn frame_idx_spec(self) -> nat {
        self.nodes.frame_idx as nat
    }

    /// The token's (inert) root header copy.
    pub open(crate) spec fn root_spec(self) -> nat {
        self.root as nat
    }

    /// The token's (inert) nkeys header copy.
    pub open(crate) spec fn nkeys_spec(self) -> nat {
        self.nkeys as nat
    }
}

impl<K, L, S, const TRACK: bool> BPlusTreeSet<K, L, S, TRACK>
    where
        K: DenseId,
        L: NodeLayout<Word = K::Index>,
        S: SearchKind,
{

    /// Semi-persistence: snapshot the whole tree (`mark`) so a later `restore`
    /// rolls it back. Delegates to the arena Vec's `mark`, plus records the two
    /// exec header fields (`root`, `nkeys`) that live outside the Vec. The view
    /// (`model`/`tree@`) is unchanged; the inner Vec pushes a frame capturing the
    /// current arena. Mirrors `SparseSet::mark`. Requires `TRACK` for the inner
    /// Vec to actually retain the snapshot.
    pub fn mark(&mut self, shrink: ShrinkPolicy) -> (token: BPlusToken)
        requires
            // `wf` already implies arena.len() < max_nat (its last clause), so no
            // separate capacity obligation: mark is total on any wf tree.
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).tree_spec() == old(self).tree_spec(),
            final(self).model() == old(self).model(),
            final(self).root_spec() == old(self).root_spec(),
            final(self).nkeys_spec() == old(self).nkeys_spec(),
            // the snapshot just pushed is the current arena; restore can return here.
            token.frame_idx_spec() == old(self).arena_depth_spec(),
            final(self).arena_snapshots_view()
                == old(self).arena_snapshots_view().push(old(self).arena()),
            token.root_spec() == final(self).root_spec().as_nat(),
            token.nkeys_spec() == final(self).nkeys_spec(),
        {
        // Total-with-documented-panic: the erased TRACK and depth requires
        // become explicit refuse branches; ensures bind returning paths only.
        if !TRACK {
            crate::guard::refuse("BPlusTreeSet::mark: tree is untracked");
        }
        if !(self.nodes.frames.len() < (u32::MAX as usize)) {
            crate::guard::refuse("BPlusTreeSet::mark: frame depth at u32 ceiling");
        }
            let nodes_token = self.nodes.mark(shrink);
            // Phase 7: archive the header + ghost tree alongside the arena
            // snapshot the inner mark just pushed.
            let root_usize = self.root.as_usize();
            let last_leaf_usize = self.last_leaf.as_usize();
            self.header_archive.push((root_usize, self.nkeys, last_leaf_usize));
            self.tree_snapshots = Ghost(self.tree_snapshots@.push(self.tree@));
            proof {
                reveal(tree_archive_agrees);
                assert(tree_archive_agrees::<K, L, S, TRACK>(
                    old(self).header_archive@, old(self).tree_snapshots@,
                    old(self).nodes.snapshots_view()));
                let k_new = self.header_archive@.len() - 1;
                assert(self.nodes.snapshots_view()[k_new] == old(self).arena());
                self.root.lemma_as_nat_bounded();
                assert(self.header_archive@[k_new].0 as nat == self.root.as_nat());
                assert forall|k: int| 0 <= k < self.header_archive@.len()
                    implies (#[trigger] self.header_archive@[k]).0
                        < <L::ArenaIdx as IndexLike>::max_nat()
                        && Self::tree_state_wf(
                            self.nodes.snapshots_view()[k],
                            self.header_archive@[k].0 as nat,
                            self.tree_snapshots@[k],
                            self.header_archive@[k].1 as nat) by {
                    if k < k_new {
                        assert(self.header_archive@[k] == old(self).header_archive@[k]);
                        assert(self.tree_snapshots@[k] == old(self).tree_snapshots@[k]);
                        assert(self.nodes.snapshots_view()[k]
                            == old(self).nodes.snapshots_view()[k]);
                    }
                }
                // the new `last_leaf` clauses: at k_new it is `self.last_leaf`,
                // which `wf`'s `last_leaf_ok` pins to the archived tree's rightmost
                // leaf (the tree just archived IS `self.tree@`); below k_new the
                // entries are the old archive's, which already agreed.
                self.last_leaf.lemma_as_nat_bounded();
                assert forall|k: int| 0 <= k < self.header_archive@.len()
                    implies (#[trigger] self.header_archive@[k]).2
                        < <L::ArenaIdx as IndexLike>::max_nat()
                        && self.header_archive@[k].2 as nat
                            == crate::bplus_tree::last_leaf_id(self.tree_snapshots@[k]) by {
                    if k < k_new {
                        assert(self.header_archive@[k] == old(self).header_archive@[k]);
                        assert(self.tree_snapshots@[k] == old(self).tree_snapshots@[k]);
                    } else {
                        assert(self.tree_snapshots@[k] == self.tree@);
                    }
                }
                assert(tree_archive_agrees::<K, L, S, TRACK>(
                    self.header_archive@, self.tree_snapshots@,
                    self.nodes.snapshots_view()));
            }
            BPlusToken {
                nodes: nodes_token,
                root: root_usize,
                nkeys: self.nkeys,
            }
        }

    /// Roll the whole tree back to the state captured by `token`. The arena Vec
    /// rolls back to its frame snapshot; `root`/`nkeys` come from the token; and
    /// the ghost model `tree@` is supplied as `snap_tree` (the ghost tree that was
    /// live at the mark — erased at runtime, like `ListArena::restore`'s
    /// `snap_model`). The caller proves `snap_tree` is a valid B+tree over the
    /// snapshot arena (`tree_state_wf`), exactly the structural half of `wf`; this
    /// method re-establishes the full `self.wf()`.
    /// "Restorable now" (plan 2.2): the Vec component is restorable AND every
    /// runtime-checkable header condition holds (the recorded root index
    /// round-trips through ArenaIdx). A token passing this check will not be
    /// rejected by any of `restore`'s runtime guards — one public validity
    /// meaning. (The proof-only `tree_state_wf` precondition is not runtime
    /// checkable; forged in-range-but-wrong headers are excluded by token
    /// opacity — fields go `pub(crate)` in the Phase 5 privacy closeout.)
    pub fn is_valid_token(&self, token: &BPlusToken) -> (b: bool)
        requires self.wf(),
        ensures b == self.is_restorable_spec(*token),
    {
        // The token's header copies (root/nkeys) are NOT consulted: restore
        // recovers the header from the internal archive (Phase 7), so forged
        // header fields are inert and validity is exactly the Vec component's
        // restorability.
        self.nodes.is_valid_token(&token.nodes)
    }

    pub fn restore(&mut self, token: BPlusToken)
        where L::Node: core::default::Default
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            // Restored to the state archived at that mark (Phase 7: header
            // and ghost tree recovered internally — the token's header copies
            // are NOT consulted; forged header fields are inert).
            final(self).tree_spec() == old(self).tree_snapshots_spec()[token.frame_idx_spec() as int],
            final(self).arena() == old(self).arena_snapshots_view()[token.frame_idx_spec() as int],
            final(self).model() == crate::bplus_tree::tree_keys(
                old(self).tree_snapshots_spec()[token.frame_idx_spec() as int]),
        {
        // Total-with-documented-panic: is_valid_token answers exactly "would
        // restore succeed now"; a stale/foreign token refuses here.
        if !self.is_valid_token(&token) {
            crate::guard::refuse("BPlusTreeSet::restore: token does not name a restorable frame");
        }
            // Runtime guards (plan 2.3), all BEFORE `self.nodes.restore`
            // mutates the arena, so a bad token cannot leave the tree
            // half-restored. The header comes from the internal archive (in
            // lockstep with the vec frames — wf agreement), so no token
            // header validation is needed: those fields are ignored.
            crate::guard::check_precondition(TRACK, "restore() called on untracked tree");
            crate::guard::check_precondition(
                self.is_valid_token(&token),
                "BPlusTreeSet::restore: invalid, foreign, stale, consumed, or abandoned token",
            );
            proof {
                reveal(tree_archive_agrees);
                // Archive lengths equal the snapshot stack (wf agreement); the
                // vec's own wf (wf_for_snap's parallel-stacks clause) gives
                // snapshots.len() == frames.len(), so frame_idx indexes the
                // archives.
            }
            let ghost snap_tree = self.tree_snapshots@[token.nodes.frame_idx_spec() as int];
            // Recover the archived header. frame_idx < frames.len() ==
            // header_archive.len() (agreement), so the indexing is in-bounds;
            // the guard above pins it for unverified callers too.
            crate::guard::check_precondition(
                token.nodes.frame_idx < self.header_archive.len(),
                "BPlusTreeSet::restore: token frame beyond header archive",
            );
            let (root_usize, saved_nkeys, saved_last_leaf) =
                self.header_archive[token.nodes.frame_idx];
            self.nodes.restore(token.nodes);
            // recover root from the archive (ArenaIdx from the stored usize;
            // in range by the archive agreement).
            let new_root = match <L::ArenaIdx as IndexLike>::try_from_usize(root_usize) {
                Some(r) => r,
                None => {
                    proof { assert(false); }
                    crate::guard::check_precondition(
                        false,
                        "BPlusTreeSet::restore: archived root index out of range",
                    );
                    return;
                }
            };
            self.root = new_root;
            self.nkeys = saved_nkeys;
            // recover `last_leaf` from the archive too (the agreement clause pins
            // it to the archived ghost tree's rightmost leaf, so `last_leaf_ok`
            // comes back with the rest of the header).
            let new_last_leaf = match <L::ArenaIdx as IndexLike>::try_from_usize(saved_last_leaf) {
                Some(r) => r,
                None => {
                    proof { assert(false); }
                    crate::guard::check_precondition(
                        false,
                        "BPlusTreeSet::restore: archived last_leaf index out of range",
                    );
                    return;
                }
            };
            self.last_leaf = new_last_leaf;
            self.tree = Ghost(snap_tree);
            // Truncate the archives in lockstep with the vec snapshot stack.
            self.header_archive.truncate(token.nodes.frame_idx);
            self.tree_snapshots =
                Ghost(self.tree_snapshots@.subrange(0, token.nodes.frame_idx_spec() as int));
            proof {
                reveal(tree_archive_agrees);
                let f = token.nodes.frame_idx_spec() as int;
                // nodes.restore put the arena at the snapshot; the archived
                // agreement at frame f is tree_state_wf over exactly that
                // snapshot + the archived header + tree.
                assert(self.arena()
                    == old(self).nodes.snapshots_view()[f]);
                assert(self.root.as_nat() == root_usize as nat);   // round-trip
                // Truncated archives agree with the truncated snapshot stack.
                assert(self.nodes.snapshots_view()
                    =~= old(self).nodes.snapshots_view().subrange(0, f));
                assert forall|k: int| 0 <= k < self.header_archive@.len()
                    implies (#[trigger] self.header_archive@[k]).0
                        < <L::ArenaIdx as IndexLike>::max_nat()
                        && Self::tree_state_wf(
                            self.nodes.snapshots_view()[k],
                            self.header_archive@[k].0 as nat,
                            self.tree_snapshots@[k],
                            self.header_archive@[k].1 as nat) by {
                    assert(self.header_archive@[k] == old(self).header_archive@[k]);
                    assert(self.tree_snapshots@[k] == old(self).tree_snapshots@[k]);
                    assert(self.nodes.snapshots_view()[k]
                        == old(self).nodes.snapshots_view()[k]);
                }
                assert(tree_archive_agrees::<K, L, S, TRACK>(
                    self.header_archive@, self.tree_snapshots@,
                    self.nodes.snapshots_view()));
            }
        }
}

} // verus!

// prod-parity: production exposed the whole B+tree surface under `bplus::`
// (`containers/src/lib.rs:39`) — including the search kinds (verus keeps them in
// `bplus_search`) and default-width layout aliases (`Layout64 = Layout64U32`,
// etc., `bplus.rs:328`). The B+tree is unwired in the consumer (descoped on
// measurement -- see `doc/migration/README.md`), but its benches (`egraph/benches/index_bench.rs`
// etc.) import these production names, so re-export/alias them here. Dropped at
// step 3 in favor of the width-suffixed names.
#[doc(hidden)]
pub use crate::bplus_layout::{
    Layout64U32, Layout128U32, Layout128U64, Layout256U32, Layout256U64, Layout512U64,
};
#[doc(hidden)]
pub use crate::bplus_search::{BinarySearch, Branchless};
// `SearchKind` / `NodeLayout` are already `use`d at the top of this module; the
// benches reach them via `bplus::` through those imports being in scope.
/// Production's default-width layout aliases (prod-parity).
#[doc(hidden)]
pub type Layout64 = Layout64U32;
#[doc(hidden)]
pub type Layout128 = Layout128U32;
#[doc(hidden)]
pub type Layout256 = Layout256U32;

// ---------------------------------------------------------------------------
// White-box oracle access (plain Rust, outside the verified surface). The
// runtime property tests (tests/bplus_proptest.rs) re-derive the structural
// invariants over the ARENA and walk the leaf-link chain; they need read-only
// access to the representation. Immutable borrows cannot violate any
// invariant, so this does not weaken the privacy closeout (no construction,
// no mutation).
// ---------------------------------------------------------------------------
impl<K, L, S, const TRACK: bool> BPlusTreeSet<K, L, S, TRACK>
where
    K: DenseId,
    L: NodeLayout<Word = K::Index>,
    S: SearchKind,
{
    /// Read-only arena access for white-box tests.
    #[doc(hidden)]
    pub fn white_box_nodes(
        &self,
    ) -> &crate::vec::Vec<
        L::Node,
        L::ArenaIdx,
        crate::inline_store::InlineStore<L::Node, L::ArenaIdx>,
        TRACK,
    > {
        &self.nodes
    }

    /// Read-only root arena index for white-box tests.
    #[doc(hidden)]
    pub fn white_box_root(&self) -> L::ArenaIdx {
        self.root
    }
}
