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

/// The NIL leaf-link sentinel (`max_nat - 1`), the `u32::MAX`/`usize::MAX` value
/// `new_leaf` writes. Terminates the leaf-link chain; provably distinct from
/// every real arena id because `Vec::push` keeps `len < max_nat - 1`.
pub open spec fn nil_link<L: NodeLayout>() -> nat {
    (<L::ArenaIdx as IndexLike>::max_nat() - 1) as nat
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
        &&& leaf_links_ok::<L>(self.arena(), self.tree@)
        &&& crate::bplus_tree::tree_disjoint(self.tree@)
        &&& self.nkeys as nat == self.model().len()
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

    /// Insert `key`. Returns whether the key was newly added (`!old contains`).
    ///
    /// M3 restricts to the no-split case on a leaf root: the root is a leaf with
    /// room (`count < leaf_cap`). Scans for the sorted position and presence; if
    /// already present, returns false with the model unchanged; otherwise
    /// shift-inserts via `L::leaf_insert_at`, writes the node back, bumps
    /// `nkeys`, and updates the ghost tree to the leaf with `key` inserted at
    /// its sorted position. `model'.to_set() == old model.to_set() ∪ {key}`.
    /// Leaf split + internal descent arrive at M4–M5; the `is_leaf` + room
    /// guards are the documented "restrict, later discharge" pattern.
    pub fn insert(&mut self, key: K) -> (added: bool)
        requires
            old(self).wf(),
            L::is_leaf_spec(old(self).arena()[old(self).root.as_nat() as int]),
            old(self).nkeys < usize::MAX,
            // room in the arena for the (at most two) nodes a split allocates.
            old(self).arena().len() + 2 < <L::ArenaIdx as IndexLike>::max_nat(),
        ensures
            self.wf(),
            added == !old(self).model().contains(key.id_nat()),
            self.model().to_set() == old(self).model().to_set().insert(key.id_nat()),
    {
        let ghost root_id = self.root.as_nat() as int;
        let ghost gkeys = crate::bplus_tree::tree_keys(self.tree@);
        proof { lemma_leaf_facts::<K, L, S, TRACK>(self); }

        let mut leaf = self.nodes.get(self.root);
        let n = L::count(&leaf);
        let kw: L::Word = key.to_index();

        // Scan for the sorted position: advance `pos` strictly past keys `<
        // target`, stopping when `pos == n` or `gkeys[pos] >= target`. The
        // invariant carries the boundary `forall j < pos. gkeys[j] < target`;
        // the exit condition (`pos == n || !(gkeys[pos] < target)`) then gives
        // the find-position characterization the sorted-insert lemma needs.
        let mut pos: usize = 0;
        proof { assert(L::node_wf(leaf)); assert(gkeys.len() == n as nat); }
        let mut stop = false;
        while !stop && pos < n
            invariant
                0 <= pos <= n,
                root_id == self.root.as_nat() as int,
                n as nat == L::count_spec(leaf),
                leaf == self.arena()[root_id],
                L::node_wf(leaf),
                gkeys.len() == n as nat,
                kw.as_nat() == key.id_nat(),
                gkeys == crate::bplus_tree::tree_keys(self.tree@),
                self.wf(),
                L::is_leaf_spec(self.arena()[root_id]),
                forall|j: int| 0 <= j < pos ==> gkeys[j] < key.id_nat(),
                // once stopped, pos is the boundary: gkeys[pos] >= target.
                stop ==> (pos < n && key.id_nat() <= gkeys[pos as int]),
            decreases (if stop { 0int } else { (n - pos) as int + 1 }),
        {
            let ki: L::Word = L::key(&leaf, pos);
            let lt = ki.lt(kw);
            proof {
                <L::Word as IndexLike>::lemma_order_is_as_nat(ki, kw);
                assert(L::count_spec(self.arena()[root_id]) == n as nat);
                lemma_leaf_binds_key::<K, L, S, TRACK>(self, pos as int);
                assert(ki == L::keys_view(leaf)[pos as int]);
                assert(ki.as_nat() == gkeys[pos as int]);
            }
            if lt {
                proof { assert(gkeys[pos as int] < key.id_nat()); }
                pos = pos + 1;
            } else {
                // gkeys[pos] >= target: stop here.
                stop = true;
            }
        }

        // Decide presence at the boundary, and establish the tail-ordering.
        let mut present = false;
        if stop {
            let ki: L::Word = L::key(&leaf, pos);
            let le = kw.le(ki);
            let ge = ki.le(kw);
            proof {
                <L::Word as IndexLike>::lemma_order_is_as_nat(kw, ki);
                <L::Word as IndexLike>::lemma_order_is_as_nat(ki, kw);
                assert(L::count_spec(self.arena()[root_id]) == n as nat);
                lemma_leaf_binds_key::<K, L, S, TRACK>(self, pos as int);
                assert(ki == L::keys_view(leaf)[pos as int]);
                assert(ki.as_nat() == gkeys[pos as int]);
            }
            if le && ge {
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
                if stop {
                    assert(key.id_nat() <= gkeys[pos as int]);   // boundary
                    assert(gkeys[pos as int] <= gkeys[j]);       // sorted, pos <= j
                    // absence ⟹ gkeys[pos] != k ⟹ k < gkeys[pos] <= gkeys[j]
                }
                // if !stop then pos == n, so the range is empty (vacuous).
            }
            assert(!gkeys.contains(key.id_nat()));
        }

        // Capture the OLD leaf's per-key binding (keys_view projects to gkeys)
        // before mutating — needed to rebuild binds for the new ghost leaf.
        let ghost old_kview = L::keys_view(leaf);
        proof {
            L::lemma_keys_view_len(leaf);  // old_kview.len() == count == n == gkeys.len()
            assert forall|j: int| 0 <= j < gkeys.len() implies old_kview[j].as_nat() == gkeys[j] by {
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
        self.nodes.set(self.root, leaf);
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
        }
        true
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
            old(self).nkeys < usize::MAX,
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
            self.wf(),
            added == !old(self).model().contains(key.id_nat()),
            self.model().to_set() == old(self).model().to_set().insert(key.id_nat()),
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
        self.nodes.set(self.root, left);

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
                combined[i].as_nat() == combined_nat[i] by {
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
        key: K,
        kw: L::Word,
        cur: Ghost<Tree>,
        h: Ghost<nat>,
        succ: Ghost<nat>,
    ) -> (res: (bool, Option<(L::Word, L::ArenaIdx)>, Ghost<Tree>, Ghost<Tree>))
        requires
            old(self).nodes.wf(),
            Self::subtree_wf(old(self).arena(), cur@, h@, succ@, false),
            idx.as_nat() == crate::bplus_tree::tree_root_id(cur@),
            L::is_leaf_spec(old(self).arena()[idx.as_nat() as int]),
            kw.as_nat() == key.id_nat(),
            old(self).arena().len() + 2 < <L::ArenaIdx as IndexLike>::max_nat(),
        ensures
            self.nodes.wf(),
            old(self).arena().len() <= self.arena().len(),
            ({
                let (added, split, nl, nr) = res;
                match split {
                    Option::None => {
                        &&& Self::subtree_wf(self.arena(), nl@, h@, succ@, false)
                        &&& crate::bplus_tree::tree_root_id(nl@) == idx.as_nat()
                        &&& crate::bplus_tree::tree_keys(nl@).to_set()
                                == crate::bplus_tree::tree_keys(cur@).to_set().insert(key.id_nat())
                        &&& added == !crate::bplus_tree::tree_keys(cur@).contains(key.id_nat())
                    }
                    Option::Some((sep, rid)) => {
                        &&& added
                        &&& Self::subtree_wf(self.arena(), nl@, h@,
                                crate::bplus_tree::tree_leaf_ids(nr@)[0], false)
                        &&& Self::subtree_wf(self.arena(), nr@, h@, succ@, false)
                        &&& crate::bplus_tree::tree_root_id(nl@) == idx.as_nat()
                        &&& crate::bplus_tree::tree_root_id(nr@) == rid.as_nat()
                        &&& crate::bplus_tree::tree_keys(nr@).len() >= 1
                        &&& sep.as_nat() == crate::bplus_tree::tree_keys(nr@)[0]
                        &&& (crate::bplus_tree::tree_keys(nl@) + crate::bplus_tree::tree_keys(nr@)).to_set()
                                == crate::bplus_tree::tree_keys(cur@).to_set().insert(key.id_nat())
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

        let leaf = self.nodes.get(idx);
        let n = L::count(&leaf);
        proof {
            assert(self.arena()[lid as int] == leaf);
            assert(gkeys.len() == n as nat);
            assert(L::node_wf(leaf));
        }

        // Scan for the sorted position + presence (the M3 condition-driven loop).
        let mut pos: usize = 0;
        let mut stop = false;
        while !stop && pos < n
            invariant
                0 <= pos <= n,
                n as nat == L::count_spec(leaf),
                leaf == self.arena()[lid as int],
                lid == idx.as_nat(),
                L::node_wf(leaf),
                L::is_leaf_spec(leaf),
                gkeys.len() == n as nat,
                kw.as_nat() == key.id_nat(),
                gkeys == crate::bplus_tree::tree_keys(cur@),
                cur@ == (Tree::Leaf { id: lid, keys: gkeys }),
                binds::<L>(self.arena(), cur@),
                forall|j: int| 0 <= j < pos ==> gkeys[j] < key.id_nat(),
                stop ==> (pos < n && key.id_nat() <= gkeys[pos as int]),
                forall|j: int| 0 <= j < gkeys.len() ==>
                    (#[trigger] L::keys_view(leaf)[j]).as_nat() == gkeys[j],
            decreases (if stop { 0int } else { (n - pos) as int + 1 }),
        {
            let ki: L::Word = L::key(&leaf, pos);
            let lt = ki.lt(kw);
            proof {
                <L::Word as IndexLike>::lemma_order_is_as_nat(ki, kw);
                lemma_leaf_binds_key_at::<K, L, S, TRACK>(self.arena(), cur@, lid, pos as int);
                assert(ki == L::keys_view(leaf)[pos as int]);
                assert(ki.as_nat() == gkeys[pos as int]);
            }
            if lt {
                proof { assert(gkeys[pos as int] < key.id_nat()); }
                pos = pos + 1;
            } else {
                stop = true;
            }
        }

        // presence at the boundary.
        let mut present = false;
        if stop {
            let ki: L::Word = L::key(&leaf, pos);
            let le = kw.le(ki);
            let ge = ki.le(kw);
            proof {
                <L::Word as IndexLike>::lemma_order_is_as_nat(kw, ki);
                <L::Word as IndexLike>::lemma_order_is_as_nat(ki, kw);
                lemma_leaf_binds_key_at::<K, L, S, TRACK>(self.arena(), cur@, lid, pos as int);
                assert(ki == L::keys_view(leaf)[pos as int]);
                assert(ki.as_nat() == gkeys[pos as int]);
            }
            if le && ge {
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
                if stop {
                    assert(key.id_nat() <= gkeys[pos as int]);
                    assert(gkeys[pos as int] <= gkeys[j]);
                }
            }
            assert(!gkeys.contains(key.id_nat()));
        }

        // capture old key view + the NIL/successor link before mutating.
        let ghost old_kview = L::keys_view(leaf);
        proof {
            L::lemma_keys_view_len(leaf);
            assert forall|j: int| 0 <= j < gkeys.len() implies old_kview[j].as_nat() == gkeys[j] by {
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
            let mut nleaf = leaf;
            L::leaf_insert_at(&mut nleaf, pos, kw);
            proof {
                assert(L::count_spec(nleaf) == n as nat + 1);
                assert(L::keys_view(nleaf) == old_kview.insert(pos as int, kw));
                assert(L::link_view(nleaf) == succ@);  // leaf_insert_at preserves link
            }
            self.nodes.set(idx, nleaf);
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
                // tree_wf(nl, h==0): sorted + count. lemma_sorted_insert.
                crate::bplus_tree::lemma_sorted_insert(gkeys, key.id_nat(), pos as int);
                assert(crate::bplus_tree::tree_wf(nl, h@, L::leaf_cap_spec(), L::key_cap_spec(), false));
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
        let (mut nleft, right) = L::leaf_split_at(&leaf, pos, kw);
        let ghost mid = L::split_mid_spec();
        proof {
            assert(combined == L::keys_view(leaf).insert(pos as int, kw));
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
        self.nodes.set(idx, nleft);

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
            assert forall|i: int| 0 <= i < combined.len() implies combined[i].as_nat() == combined_nat[i] by {
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
        }
        (true, Some((sep, right_idx)), Ghost(nl), Ghost(nr))
    }
}

/// Frame lemma for `binds` (the dynamic-frames separation). If two arenas agree
/// on every id in `tree_ids(t)` — `t`'s footprint — then `t` binds in one iff it
/// binds in the other. So a mutation confined to ids outside `tree_ids(t)`
/// preserves `binds(_, t)`. This is what lets a split touch one subtree's nodes
/// and frame out every disjoint subtree's binding for free.
pub proof fn lemma_binds_frame<L: NodeLayout>(a1: Seq<L::Node>, a2: Seq<L::Node>, t: Tree)
    requires
        binds::<L>(a1, t),
        a1.len() <= a2.len(),
        forall|id: nat| crate::bplus_tree::tree_ids(t).contains(id) ==> a1[id as int] == a2[id as int],
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
pub proof fn lemma_forest_binds_frame<L: NodeLayout>(
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
        forall|id: nat| crate::bplus_tree::tree_ids(parent).contains(id)
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
        assert forall|id: nat| crate::bplus_tree::tree_ids(kids[0]).contains(id)
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
        assert forall|id: nat| crate::bplus_tree::tree_ids(dparent).contains(id)
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
pub proof fn lemma_leaf_links_frame<L: NodeLayout>(
    a1: Seq<L::Node>,
    a2: Seq<L::Node>,
    t: Tree,
    succ: nat,
)
    requires
        leaf_links_to::<L>(a1, t, succ),
        forall|id: nat| crate::bplus_tree::tree_ids(t).contains(id) ==> a1[id as int] == a2[id as int],
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
pub proof fn lemma_subtree_wf_frame<K, L, S, const TRACK: bool>(
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
        forall|id: nat| crate::bplus_tree::tree_ids(t).contains(id) ==> a1[id as int] == a2[id as int],
    ensures
        BPlusTreeSet::<K, L, S, TRACK>::subtree_wf(a2, t, h, succ, is_root),
{
    lemma_binds_frame::<L>(a1, a2, t);
    lemma_leaf_links_frame::<L>(a1, a2, t, succ);
    // tree_wf and tree_disjoint are arena-independent, carried by the requires.
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

/// Per-key projection from `binds` at a leaf subtree, without needing `tree_wf`:
/// if `cur == Leaf{id, keys}` binds in `arena` and `0 <= i < keys.len()`, the
/// arena node's `i`-th word projects to `keys[i]`. The recursion's leaf scan
/// uses this (it has `subtree_wf`'s `binds`, not a root-form `tree_wf`).
pub proof fn lemma_leaf_binds_key_at<K, L, S, const TRACK: bool>(
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
pub proof fn lemma_leaf_sorted<K, L, S, const TRACK: bool>(t: &BPlusTreeSet<K, L, S, TRACK>)
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
