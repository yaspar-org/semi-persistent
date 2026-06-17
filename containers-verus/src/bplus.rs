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

    /// Membership. Decides `key ∈ model`.
    ///
    /// M2b restricts to the single-leaf tree (precondition: the root is a
    /// leaf), which is the only shape `new` produces and `insert`-no-split
    /// preserves; the search is a scan of the leaf's keys. When `insert` builds
    /// internal nodes (M4), this generalizes to a root-to-leaf descent driven by
    /// `S::find_gt` (the cross-node-ordering clause of `tree_wf` is what makes
    /// the descent land in the unique leaf that would hold `key`); the leaf
    /// membership step is `lemma_leaf_search_membership`. The `is_leaf` guard is
    /// the documented "restrict, later discharge" pattern.
    pub fn contains(&self, key: K) -> (b: bool)
        requires
            self.wf(),
            L::is_leaf_spec(self.arena()[self.root.as_nat() as int]),
        ensures
            b == self.model().contains(key.id_nat()),
    {
        let ghost root_id = self.root.as_nat() as int;
        let ghost gkeys = crate::bplus_tree::tree_keys(self.tree@);
        proof { lemma_leaf_facts::<K, L, S, TRACK>(self); }

        let root_node = self.nodes.get(self.root);
        let n = L::count(&root_node);
        let kw: L::Word = key.to_index();  // word with as_nat == key.id_nat()

        proof {
            assert(self.arena()[root_id] == root_node);
            // lemma_leaf_facts gives: node_wf(root_node), count == gkeys.len().
            assert(L::node_wf(root_node));
            assert(gkeys.len() == L::count_spec(root_node));
        }

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                root_id == self.root.as_nat() as int,
                n as nat == L::count_spec(root_node),
                root_node == self.arena()[root_id],
                L::node_wf(root_node),
                gkeys.len() == n as nat,
                kw.as_nat() == key.id_nat(),
                gkeys == crate::bplus_tree::tree_keys(self.tree@),
                self.wf(),
                L::is_leaf_spec(self.arena()[root_id]),
                // no key before i equals the target
                forall|j: int| 0 <= j < i ==> gkeys[j] != key.id_nat(),
            decreases n - i,
        {
            let ki: L::Word = L::key(&root_node, i);
            // equality on words via the IndexLike order (le both ways).
            let le1 = ki.le(kw);
            let le2 = kw.le(ki);
            proof {
                <L::Word as IndexLike>::lemma_order_is_as_nat(ki, kw);
                <L::Word as IndexLike>::lemma_order_is_as_nat(kw, ki);
                // root_node is the arena root node, so the lemma's count bound
                // (over arena[root]) matches the loop's `i < n`.
                assert(root_node == self.arena()[root_id]);
                assert(L::count_spec(self.arena()[root_id]) == n as nat);
                // binds(leaf): keys_view(arena[root])[i].as_nat() == gkeys[i]
                lemma_leaf_binds_key::<K, L, S, TRACK>(self, i as int);
                assert(ki == L::keys_view(root_node)[i as int]);  // L::key ensures
                assert(ki.as_nat() == gkeys[i as int]);
            }
            if le1 && le2 {
                proof {
                    // ki.as_nat() == kw.as_nat() == key.id_nat(), and
                    // ki.as_nat() == gkeys[i], so gkeys[i] == key.id_nat().
                    assert(gkeys[i as int] == key.id_nat());
                    assert(gkeys.contains(key.id_nat()));
                }
                return true;
            }
            proof {
                // ki.as_nat() != kw.as_nat() (not both <=), and ki.as_nat() ==
                // gkeys[i], so gkeys[i] != target — extends the invariant to i+1.
                assert(gkeys[i as int] != key.id_nat());
            }
            i = i + 1;
        }
        proof {
            // scanned every key, none equal the target.
            assert(forall|j: int| 0 <= j < gkeys.len() ==> gkeys[j] != key.id_nat());
            assert(!gkeys.contains(key.id_nat()));
        }
        false
    }
}

/// Leaf-root facts from `wf` + the leaf guard: the arena root node is
/// node-well-formed and its key count equals the ghost model length. Both
/// follow from `binds`'s leaf arm (count == keys.len()) and `tree_wf`'s leaf
/// arm (keys.len() <= leaf_cap ⟹ node_wf).
pub proof fn lemma_leaf_facts<K, L, S, const TRACK: bool>(t: &BPlusTreeSet<K, L, S, TRACK>)
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
pub proof fn lemma_leaf_binds_key<K, L, S, const TRACK: bool>(
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

} // verus!
