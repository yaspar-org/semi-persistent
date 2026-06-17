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
            L::count_spec(old(self).arena()[old(self).root.as_nat() as int])
                < L::leaf_cap_spec(),
            old(self).nkeys < usize::MAX,
        ensures
            self.wf(),
            L::is_leaf_spec(self.arena()[self.root.as_nat() as int]),
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
