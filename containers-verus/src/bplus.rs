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
use crate::vec::{Vec as SpVec, VecToken};

verus! {

/// Token for mark/restore (delegates to the inner vector's token).
#[derive(Copy, Clone)]
pub struct BPlusToken {
    pub nodes: VecToken,
}

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
    /// structurally valid B+tree (`tree_wf` at its height, as root); and the
    /// cached `nkeys` equals the model length.
    ///
    /// (Disjointness of subtree id-sets — the dynamic-frames separation — is a
    /// conjunct added at M3 when multi-node trees first arise; vacuous here.)
    pub open spec fn wf(&self) -> bool {
        &&& self.nodes.wf()
        &&& crate::bplus_tree::tree_root_id(self.tree@) == self.root.as_nat()
        &&& binds::<L>(self.arena(), self.tree@)
        &&& crate::bplus_tree::tree_wf(
                self.tree@,
                crate::bplus_tree::tree_height(self.tree@),
                L::leaf_cap_spec(),
                L::key_cap_spec(),
                true,
            )
        &&& self.nkeys as nat == self.model().len()
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
}

} // verus!
