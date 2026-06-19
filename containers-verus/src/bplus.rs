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

/// Every model value is a genuine `K`-image: `< K::id_bound()`. The refinement
/// the `K -> K::Index` storage coercion drops (the stored `Index` word type is
/// wider than the id's valid range), re-asserted at the model. Insert preserves
/// it for free — it only ever adds `key.id_nat()`, bounded by
/// `lemma_id_nat_bounded` — and it makes the cursor's `from_usize` read exact.
pub open spec fn model_bounded<K: DenseId>(model: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < model.len() ==> #[trigger] model[i] < K::id_bound()
}

/// `model_bounded` is preserved by inserting a bounded value at any position:
/// the insert-only model transition. `m.insert(pos, v)` stays bounded when `m`
/// is and `v < id_bound` (which `lemma_id_nat_bounded` gives for a real key).
pub proof fn lemma_model_bounded_insert<K: DenseId>(m: Seq<nat>, pos: int, v: nat)
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
pub proof fn lemma_model_bounded_set<K: DenseId>(m: Seq<nat>, old: Seq<nat>, v: nat)
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

/// `forest_links_to(kids)` composes to `leaf_links_to(Inner{.., kids})`: if every
/// child's chain threads to the next child's first leaf (and the last to `succ`),
/// the parent's whole-subtree chain holds. Each child must be non-empty
/// (`tree_leaf_ids(kids[i]).len() >= 1`), which `tree_wf` guarantees. Ported from
/// a standalone 7-lemma probe.
pub proof fn lemma_forest_links_compose<L: NodeLayout>(
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
        &&& model_bounded::<K>(self.model())
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
            // model_bounded: new_keys == gkeys.insert(pos, key.id_nat()); gkeys
            // (== old model) is bounded by old wf, key.id_nat() < id_bound.
            key.lemma_id_nat_bounded();
            assert(model_bounded::<K>(gkeys));  // old(self).wf() clause (gkeys == old model)
            lemma_model_bounded_insert::<K>(gkeys, pos as int, key.id_nat());
            assert(model_bounded::<K>(self.model()));
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
    pub fn insert_general(&mut self, key: K) -> (added: bool)
        requires
            old(self).wf(),
            old(self).nkeys < usize::MAX,
            // arena headroom for the whole descent path + the new root a root split
            // allocates (one node per level, plus the root). `tree_height + 3`.
            old(self).arena().len() + crate::bplus_tree::tree_height(old(self).tree@) + 3
                < <L::ArenaIdx as IndexLike>::max_nat(),
        ensures
            self.wf(),
            added == !old(self).model().contains(key.id_nat()),
            self.model().to_set() == old(self).model().to_set().insert(key.id_nat()),
    {
        let kw: L::Word = key.to_index();
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
        let (added, split, nl, nr) =
            self.insert_rec(root, key, kw, self.tree, Ghost(h), Ghost(nil_link::<L>()), Ghost(true));
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
                }
                added
            }
            Some((sep, rid)) => {
                // root split: build a new internal root over the two halves nl, nr.
                let new_root = L::new_internal2(sep, root, rid);
                let new_root_idx = self.nodes.len();
                let ghost arena_pre = self.arena();
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
                }
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
            // model_bounded: model == combined_nat == gkeys.insert(pos, key.id_nat());
            // gkeys (== old model) bounded by old wf, key.id_nat() < id_bound.
            key.lemma_id_nat_bounded();
            assert(model_bounded::<K>(gkeys));
            lemma_model_bounded_insert::<K>(gkeys, pos as int, key.id_nat());
            assert(self.model() == combined_nat);
            assert(model_bounded::<K>(self.model()));
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
            kw.as_nat() == key.id_nat(),
            h@ == 0,
            old(self).arena().len() + 2 < <L::ArenaIdx as IndexLike>::max_nat(),
        ensures
            self.nodes.wf(),
            // only the arena (self.nodes) is touched; the cached count, root index,
            // and ghost tree are unchanged (the caller frames its bookkeeping).
            self.nkeys == old(self).nkeys,
            self.root == old(self).root,
            self.tree@ == old(self).tree@,
            old(self).arena().len() <= self.arena().len(),
            // a leaf insert allocates at most one node (the split's right leaf).
            self.arena().len() <= old(self).arena().len() + h@ + 1,
            forall|i: int| 0 <= i < old(self).arena().len()
                && !crate::bplus_tree::tree_ids(cur@).contains(i as nat)
                ==> #[trigger] self.arena()[i] == old(self).arena()[i],
            ({
                let (added, split, nl, nr) = res;
                match split {
                    Option::None => {
                        &&& Self::subtree_wf(self.arena(), nl@, h@, succ@, is_root@)
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
                        &&& Self::subtree_wf(self.arena(), nl@, h@,
                                crate::bplus_tree::tree_leaf_ids(nr@)[0], false)
                        &&& Self::subtree_wf(self.arena(), nr@, h@, succ@, false)
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
            self.nodes.wf(),
            // only the arena (self.nodes) is touched; the cached count, root index,
            // and ghost tree are unchanged (the caller frames its bookkeeping).
            self.nkeys == old(self).nkeys,
            self.root == old(self).root,
            self.tree@ == old(self).tree@,
            // arena grows by at most h + 1 (one allocation per level + new root
            // is the caller's; here, at most one per level of this subtree).
            old(self).arena().len() <= self.arena().len(),
            self.arena().len() <= old(self).arena().len() + h@ + 1,
            // FRAME: every arena slot outside cur's footprint is unchanged. Lets
            // the caller (the level above) frame this subtree's siblings.
            forall|i: int| 0 <= i < old(self).arena().len()
                && !crate::bplus_tree::tree_ids(cur@).contains(i as nat)
                ==> #[trigger] self.arena()[i] == old(self).arena()[i],
            ({
                let (added, split, nl, nr) = res;
                match split {
                    Option::None => {
                        &&& Self::subtree_wf(self.arena(), nl@, h@, succ@, is_root@)
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
                        &&& Self::subtree_wf(self.arena(), nl@, h@,
                                crate::bplus_tree::tree_leaf_ids(nr@)[0], false)
                        &&& Self::subtree_wf(self.arena(), nr@, h@, succ@, false)
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
        let node = self.nodes.get(idx);
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
            return self.insert_rec_leaf(idx, key, kw, cur, h, succ, is_root);
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

        // find cp = find_gt(seps, key): scan past separators <= key.
        let mut cp: usize = 0;
        let mut stop = false;
        while !stop && cp < n
            invariant
                0 <= cp <= n,
                n as nat == gseps.len(),
                n as nat == L::count_spec(node),
                node == self.arena()[gid as int],
                idx.as_nat() == gid,
                L::node_wf(node),
                !L::is_leaf_spec(node),
                kw.as_nat() == key.id_nat(),
                forall|i: int| 0 <= i < gseps.len() ==>
                    (#[trigger] L::keys_view(node)[i]).as_nat() == gseps[i],
                forall|j: int| 0 <= j < cp ==> gseps[j] <= key.id_nat(),
                stop ==> (cp < n && key.id_nat() < gseps[cp as int]),
            decreases (if stop { 0int } else { (n - cp) as int + 1 }),
        {
            let ki: L::Word = L::key(&node, cp);
            let le = ki.le(kw);
            proof {
                <L::Word as IndexLike>::lemma_order_is_as_nat(ki, kw);
                assert(ki == L::keys_view(node)[cp as int]);
                assert(ki.as_nat() == gseps[cp as int]);
            }
            if le { proof { assert(gseps[cp as int] <= key.id_nat()); } cp = cp + 1; }
            else { proof { assert(key.id_nat() < gseps[cp as int]); } stop = true; }
        }
        // find_gt characterization: [0..cp) <= key, [cp..) > key.
        proof {
            assert(crate::bplus_tree::strictly_sorted(gseps));
            assert forall|i: int| cp <= i < gseps.len() implies key.id_nat() < gseps[i] by {
                if stop { if cp < i { assert(gseps[cp as int] < gseps[i]); } }
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
                    assert forall|id: nat| crate::bplus_tree::tree_ids(cur@).contains(id)
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
                        implies self.arena()[i] == arena1[i] by {
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
                }
                (added, None, Ghost(nt), cur)
            }
            Some((sep, rid)) => {
                // child cp split into (ncl@ at idx, ncr@ at rid), separated by
                // `sep`. Insert (sep, rid) into this parent at child-pos cp+1.
                let mut pnode = self.nodes.get(idx);
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
                    self.nodes.set(idx, pnode);
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
                    self.nodes.set(idx, pl);
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
                    }
                    (added, Some((promoted, new_int)), Ghost(lt), Ghost(rt))
                }
            }
        }
    }

    /// `find_ge` over a leaf node's keys: first index `i` with `keys[i] >= word`.
    #[verifier::external_body]
    fn leaf_find_ge(&self, node: &L::Node, word: L::Word) -> usize {
        let n = L::count(node);
        let mut lo: usize = 0;
        let mut hi: usize = n;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if L::key(node, mid).lt(word) { lo = mid + 1; } else { hi = mid; }
        }
        lo
    }

    /// Descend root→leaf to the leaf that would hold `word`, returning
    /// `(leaf_idx, find_ge_pos)`. The cursor's *fallback* positioning (used only
    /// when the fast path along the leaf-link chain misses). TEST-FIRST exec.
    #[verifier::external_body]
    pub fn seek_leaf(&self, word: L::Word) -> (L::ArenaIdx, usize) {
        let mut idx = self.root;
        loop {
            let node = self.nodes.get(idx);
            if L::is_leaf(&node) {
                return (idx, self.leaf_find_ge(&node, word));
            }
            let n = L::count(&node);
            let mut lo: usize = 0;
            let mut hi: usize = n;
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                if word.lt(L::key(&node, mid)) { hi = mid; } else { lo = mid + 1; }
            }
            idx = L::child(&node, lo);
        }
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
    pub tree: &'a BPlusTreeSet<K, L, S, TRACK>,
    /// Current leaf arena index, or NIL (`max_nat - 1`) when exhausted.
    pub node: L::ArenaIdx,
    /// Position within the current leaf.
    pub pos: usize,
    /// Ghost: the cursor's position in the IN-ORDER MODEL. `(node, pos)` is the
    /// executable realization of model index `gidx`; `gidx == model.len()` marks
    /// "exhausted" (`node == NIL`). The cursor's `wf` ties the two together, so
    /// `key()`/`step()` can be specified against the model rather than the arena.
    pub gidx: Ghost<int>,
    /// Ghost: which chain leaf `node` is — its position in `tree_leaf_ids`. Pins
    /// `node == tree_leaf_ids(tree@)[gleaf]` so we needn't `choose` it.
    pub gleaf: Ghost<int>,
    pub _k: core::marker::PhantomData<K>,
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

    /// A fresh cursor (positioned nowhere; call `seek` / `seek_first`).
    #[verifier::external_body]
    pub fn new(tree: &'a BPlusTreeSet<K, L, S, TRACK>) -> (c: Self)
        ensures c.tree == tree,
    {
        BPlusCursor {
            tree, node: Self::nil(), pos: 0,
            gidx: Ghost(0), gleaf: Ghost(0),
            _k: core::marker::PhantomData,
        }
    }

    /// The cursor's model index (`gidx`), as a convenience for specs.
    pub open spec fn idx(self) -> int { self.gidx@ }

    /// The tree's in-order model (the sorted set).
    pub open spec fn model(self) -> Seq<nat> { crate::bplus_tree::tree_keys(self.tree.tree@) }

    /// Cursor well-formedness: `(node, pos)` realizes model index `gidx`. Either
    /// EXHAUSTED — `gidx == |model|`, `node == NIL` — or POSITIONED on chain-leaf
    /// `gleaf`: that leaf id is `node`, `pos` indexes into it, and the flat model
    /// index is `chain_offset(gleaf) + pos == gidx`. Holds against a `wf` tree.
    pub open spec fn cursor_wf(self) -> bool {
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

    /// Position at the first key `>= target`. Production's fast path: if already
    /// positioned and `target` falls in the current leaf, just `find_ge` there;
    /// else try the next leaf via `link`; else fall back to a root descent.
    #[verifier::external_body]
    pub fn seek(&mut self, target: K) {
        let nil = Self::nil();
        let word: L::Word = target.to_index();

        if self.node.as_usize() != nil.as_usize() {
            let cur = self.tree.nodes.get(self.node);
            let n = L::count(&cur);
            if n > 0 {
                let last = L::key(&cur, n - 1);
                if word.le(last) {
                    // target is within the current leaf.
                    self.pos = self.tree.leaf_find_ge(&cur, word);
                    return;
                }
                let link = L::link(&cur);
                if link.as_usize() != nil.as_usize() {
                    let nxt = self.tree.nodes.get(link);
                    let nn = L::count(&nxt);
                    if nn > 0 && word.le(L::key(&nxt, nn - 1)) {
                        // target is in the immediately-next leaf (the fast path).
                        self.pos = self.tree.leaf_find_ge(&nxt, word);
                        self.node = link;
                        return;
                    }
                }
            }
        }

        // fallback: full root descent.
        let (leaf, pos) = self.tree.seek_leaf(word);
        let node = self.tree.nodes.get(leaf);
        if pos < L::count(&node) {
            self.node = leaf;
            self.pos = pos;
        } else {
            // ran off the end of this leaf — advance to the next via link.
            let link = L::link(&node);
            self.node = link; // link is the next leaf or NIL
            self.pos = 0;
        }
    }

    /// Position at the smallest key in the set.
    #[verifier::external_body]
    pub fn seek_first(&mut self) {
        self.seek(K::from_usize(0));
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
        let node = self.tree.nodes.get(self.node);
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
    #[verifier::external_body]
    pub fn step(&mut self) {
        let nil = Self::nil();
        if self.node.as_usize() == nil.as_usize() {
            return;
        }
        self.pos = self.pos + 1;
        let node = self.tree.nodes.get(self.node);
        if self.pos >= L::count(&node) {
            self.node = L::link(&node);
            self.pos = 0;
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
pub proof fn lemma_insert_new_root<K, L, S, const TRACK: bool>(
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
    assert forall|id: nat| crate::bplus_tree::tree_ids(nl@).contains(id) implies a1s[id as int] == a2s[id as int] by {
        assert(id < a1s.len());            // precondition
        assert(a2s[id as int] == a1s[id as int]);  // push leaves old slots unchanged
    }
    assert forall|id: nat| crate::bplus_tree::tree_ids(nr@).contains(id) implies a1s[id as int] == a2s[id as int] by {
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
pub proof fn lemma_tree_id_in_range<L: NodeLayout>(arena: Seq<L::Node>, t: Tree, id: nat)
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
pub proof fn lemma_child_ids_subset_tree<L: NodeLayout>(t: Tree, cp: int, id: nat)
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
pub proof fn reconstruct_absorb<K, L, S, const TRACK: bool>(
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
        (forall|id: nat| crate::bplus_tree::tree_ids(ncl@).contains(id)
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
pub proof fn reconstruct_split_frame<K, L, S, const TRACK: bool>(
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
pub proof fn lemma_forest_binds_subrange<L: NodeLayout>(a: Seq<L::Node>, kids: Seq<Tree>, lo: int, hi: int)
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
pub proof fn lemma_forest_ids_subrange_in<L: NodeLayout>(kids: Seq<Tree>, lo: int, hi: int, id: nat)
    requires 0 <= lo <= hi <= kids.len(),
        crate::bplus_tree::forest_ids(kids.subrange(lo, hi)).contains(id),
    ensures crate::bplus_tree::forest_ids(kids).contains(id),
{
    let sub = kids.subrange(lo, hi);
    crate::bplus_tree::lemma_forest_id_in_some_child(sub, id);
    let m = choose|m: int| 0 <= m < sub.len() && crate::bplus_tree::tree_ids(sub[m]).contains(id);
    assert(sub[m] == kids[lo + m]);
    crate::bplus_tree::lemma_forest_id_in_forest(kids, lo + m, id);
}

/// An id in `left`/`right` (the siblings of child cp) is disjoint from child cp's
/// footprint and is not `gid`. `is_left` selects `left = kids[0..cp]` vs `right =
/// kids[cp+1..]`. From `tree_disjoint(cur)` (pairwise children + gid ∉ children).
pub proof fn lemma_left_right_disjoint_cp<L: NodeLayout>(cur: Tree, cp: int, id: nat, is_left: bool)
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
    let m = choose|m: int| 0 <= m < sub.len() && crate::bplus_tree::tree_ids(sub[m]).contains(id);
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
pub proof fn lemma_splice_children_bind<K, L, S, const TRACK: bool>(
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
    assert forall|id: nat| crate::bplus_tree::forest_ids(left).contains(id)
        implies a1[id as int] == a2[id as int] by {
        lemma_forest_ids_subrange_in::<L>(kids, 0, cp, id);
        assert(crate::bplus_tree::tree_ids(cur).contains(id));
        lemma_tree_id_in_range::<L>(a1, cur, id);
        lemma_left_right_disjoint_cp::<L>(cur, cp, id, true);
        assert(!crate::bplus_tree::tree_ids(gkids[cp]).contains(id));
        assert(id != gid);
    }
    assert forall|id: nat| crate::bplus_tree::forest_ids(right).contains(id)
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
pub proof fn reconstruct_child_split_absorb<K, L, S, const TRACK: bool>(
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
        (forall|id: nat| crate::bplus_tree::tree_ids(ncl@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        (forall|id: nat| crate::bplus_tree::tree_ids(ncr@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        // old child's ids retained across the two halves (split distributes them).
        (forall|id: nat| crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
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
        (forall|j: int| 0 <= j <= cp@ ==> L::child_view(pnode@, j) == L::child_view(arena1@[gid@ as int], j)),
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
    assert forall|id: nat| crate::bplus_tree::forest_ids(gkids@).contains(id)
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
pub proof fn lemma_child_split_binds_node<K, L, S, const TRACK: bool>(
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
        (forall|j: int| 0 <= j <= cp ==> L::child_view(pnode, j) == L::child_view(a1[gid as int], j)),
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
pub proof fn lemma_isplit_cchild_is_ckid<K, L, S, const TRACK: bool>(
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
pub proof fn lemma_parent_split_half_binds<K, L, S, const TRACK: bool>(
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
pub open spec fn ncr_first<L: NodeLayout>(ncr: Tree) -> nat {
    crate::bplus_tree::tree_keys(ncr)[0]
}

/// `tree_disjoint(nt)` + footprint subset/freshness + first-leaf preservation for
/// the child-split splice: a thin arena-side wrapper that supplies the freshness
/// `bound = arena1.len()` (every old id is in range, every new id is a fresh tail
/// slot) to the pure-ghost `lemma_child_split_absorb_ids`.
pub proof fn reconstruct_child_split_disjoint<K, L, S, const TRACK: bool>(
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
        (forall|id: nat| crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
            ==> crate::bplus_tree::tree_ids(ncl@).contains(id) || crate::bplus_tree::tree_ids(ncr@).contains(id)),
        (forall|id: nat| crate::bplus_tree::tree_ids(ncl@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        (forall|id: nat| crate::bplus_tree::tree_ids(ncr@).contains(id)
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
pub proof fn reconstruct_child_split_links<K, L, S, const TRACK: bool>(
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
    assert forall|id: nat| crate::bplus_tree::forest_ids(kids).contains(id)
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
/// `rlimit(30)`: this composes eight building-block lemmas (tree_wf, two
/// half_binds, the link splice + half_links, two half_ids, footprint, disjoint)
/// in one body; the modest bump over the default covers the combined query.
#[verifier::rlimit(30)]
pub proof fn reconstruct_parent_split<K, L, S, const TRACK: bool>(
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
        (forall|id: nat| crate::bplus_tree::tree_ids(ncl@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        (forall|id: nat| crate::bplus_tree::tree_ids(ncr@).contains(id)
            ==> crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id) || id >= arena1@.len()),
        (forall|id: nat| crate::bplus_tree::tree_ids(gkids@[cp@]).contains(id)
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
    assert forall|id: nat| crate::bplus_tree::tree_ids(ncl@).contains(id)
        implies ar[id as int] == a2[id as int] by {
        lemma_tree_id_in_range::<L>(ar, ncl@, id);  // id < ar.len()
        assert(id != gid@);  // gid ∉ tree_ids(ncl)
    }
    lemma_binds_frame::<L>(ar, a2, ncl@);
    assert forall|id: nat| crate::bplus_tree::tree_ids(ncr@).contains(id)
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
    assert forall|id: nat| crate::bplus_tree::forest_ids(kids).contains(id)
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
        let m = choose|m: int| 0 <= m < ckids.len() && crate::bplus_tree::tree_ids(ckids[m]).contains(id);
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
pub proof fn reconstruct_absorb_links<K, L, S, const TRACK: bool>(
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
        (forall|id: nat| crate::bplus_tree::tree_ids(ncl@).contains(id)
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
    assert forall|id: nat| crate::bplus_tree::forest_ids(kids).contains(id)
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
pub proof fn lemma_forest_links_decompose<L: NodeLayout>(
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
pub proof fn lemma_links_drop_first<L: NodeLayout>(
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
pub proof fn lemma_build_forest_links<K, L, S, const TRACK: bool>(
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
pub proof fn lemma_forest_links_update<L: NodeLayout>(
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
        assert forall|id: nat| crate::bplus_tree::forest_ids(df).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
            // id in some df[m]==kids[m+1]; disjoint from kids[0]==kids[cp].
            crate::bplus_tree::lemma_forest_id_in_some_child(df, id);
            let m = choose|m: int| 0 <= m < df.len() && crate::bplus_tree::tree_ids(df[m]).contains(id);
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
        assert forall|id: nat| crate::bplus_tree::tree_ids(kids[0]).contains(id)
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
        assert forall|id: nat| crate::bplus_tree::forest_ids(df).contains(id)
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
pub proof fn lemma_forest_links_cons<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>, succ: nat)
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
pub proof fn lemma_forest_links_split_at<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>, succ: nat, m: int)
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
pub proof fn lemma_parent_split_half_links<L: NodeLayout>(
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
pub proof fn lemma_forest_links_splice<L: NodeLayout>(
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
        assert forall|id: nat| crate::bplus_tree::forest_ids(df).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
            crate::bplus_tree::lemma_forest_id_in_some_child(df, id);
            let m = choose|m: int| 0 <= m < df.len() && crate::bplus_tree::tree_ids(df[m]).contains(id);
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
        assert forall|id: nat| crate::bplus_tree::tree_ids(kids[0]).contains(id)
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
        assert forall|id: nat| crate::bplus_tree::forest_ids(df).contains(id)
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
pub proof fn lemma_forest_links_frame_ids<L: NodeLayout>(
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
        assert forall|id: nat| crate::bplus_tree::tree_ids(kids[0]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            crate::bplus_tree::lemma_child_ids_in_forest(kids, 0, id);
        }
        lemma_leaf_links_frame::<L>(a1, a2, kids[0], s0);
        assert forall|id: nat| crate::bplus_tree::forest_ids(df).contains(id)
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
pub proof fn reconstruct_absorb_model<K, L, S, const TRACK: bool>(
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
pub proof fn lemma_concat3_set(a: Seq<nat>, b: Seq<nat>, c: Seq<nat>)
    ensures (a + b + c).to_set() == a.to_set().union(b.to_set()).union(c.to_set()),
{
    assert((a + b + c).to_set() =~= a.to_set().union(b.to_set()).union(c.to_set())) by {
        assert forall|k: nat| (a + b + c).to_set().contains(k)
            <==> a.to_set().union(b.to_set()).union(c.to_set()).contains(k) by {
            crate::bplus_tree::lemma_concat_contains(a + b, c, k);
            crate::bplus_tree::lemma_concat_contains(a, b, k);
        }
    }
}

pub proof fn lemma_leaf_links_project<L: NodeLayout>(
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
pub proof fn lemma_inner_child_subtree_wf<K, L, S, const TRACK: bool>(
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

/// `subtree_wf` framed across a single-slot `update` whose slot is outside the
/// subtree's footprint: `subtree_wf(arena, t, …)` + `id_slot ∉ tree_ids(t)` ⟹
/// `subtree_wf(arena.update(id_slot, v), t, …)`. The agreement (slot `id_slot`
/// is the only change, and it's outside `t`) is discharged once here, so callers
/// don't fight the `id != id_slot` quantifier reasoning.
pub proof fn lemma_subtree_wf_frame_update<K, L, S, const TRACK: bool>(
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
    assert forall|id: nat| crate::bplus_tree::tree_ids(t).contains(id)
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

/// Rebuild `forest_binds_l` after replacing child `cp` by a new subtree `nc` in
/// the *new* arena `a2`: the absorb step's reconstruction. `a2` binds `nc` (the
/// recursive result) and agrees with the old arena `a1` on every *other* child's
/// footprint (the recursion grew the arena and touched only `nc`'s region; the
/// siblings' ids are disjoint from `nc`'s, by `tree_disjoint` on the parent).
pub proof fn lemma_forest_binds_update<L: NodeLayout>(
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
        implies !crate::bplus_tree::forest_ids(df).contains(id) by {
        if crate::bplus_tree::forest_ids(df).contains(id) {
            crate::bplus_tree::lemma_forest_id_in_some_child(df, id);
            let m = choose|m: int| 0 <= m < df.len() && crate::bplus_tree::tree_ids(df[m]).contains(id);
            assert(df[m] == kids[m + 1]);
            assert(crate::bplus_tree::tree_ids(kids[0]).disjoint(crate::bplus_tree::tree_ids(kids[m + 1])));
        }
    }
    if cp == 0 {
        assert(u[0] == nc);
        assert(u.drop_first() =~= df);
        assert forall|id: nat| crate::bplus_tree::forest_ids(df).contains(id)
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
        assert forall|id: nat| crate::bplus_tree::tree_ids(kids[0]).contains(id)
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
        assert forall|id: nat| crate::bplus_tree::forest_ids(df).contains(id)
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
pub proof fn lemma_forest_binds_frame_tail<L: NodeLayout>(
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
        assert forall|id: nat| crate::bplus_tree::tree_ids(kids[0]).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
        }
        lemma_binds_frame::<L>(a1, a2, kids[0]);
        assert forall|id: nat| crate::bplus_tree::forest_ids(df).contains(id)
            implies a1[id as int] == a2[id as int] by {
            assert(crate::bplus_tree::forest_ids(kids).contains(id));
        }
        lemma_forest_binds_frame_tail::<L>(a1, a2, df);
    }
}

/// `forest_binds_l(a, [x, y])` from `binds(a, x)` and `binds(a, y)` (the two-
/// element base case, with the recursive unfold made explicit for the SMT solver).
pub proof fn lemma_forest_binds_pair<L: NodeLayout>(a: Seq<L::Node>, x: Tree, y: Tree)
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
pub proof fn lemma_forest_binds_concat<L: NodeLayout>(a: Seq<L::Node>, x: Seq<Tree>, y: Seq<Tree>)
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

/// `chain_keys` distributes over `++` of leaf-id lists.
pub proof fn lemma_chain_keys_concat<L: NodeLayout>(arena: Seq<L::Node>, a: Seq<nat>, b: Seq<nat>)
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
pub proof fn lemma_chain_keys_eq_model<L: NodeLayout>(arena: Seq<L::Node>, t: Tree)
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
pub proof fn lemma_chain_keys_eq_model_forest<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>)
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
pub proof fn lemma_chain_yields_sorted_model<K, L, S, const TRACK: bool>(t: &BPlusTreeSet<K, L, S, TRACK>)
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

/// `chain_keys(lids)` at the slice for leaf `m` projects to that leaf's keys:
/// for `0 <= p < |leaf m|`, `chain_keys(lids)[chain_offset(m) + p] ==
/// leaf_word_keys(lids[m])[p]`, and the offset+len stays in range. The model
/// analogue of `lemma_forest_leaf_ids_slice`; induction on `m` peeling the head.
pub proof fn lemma_chain_keys_slice<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>, m: int)
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
pub proof fn lemma_chain_offset_cons<L: NodeLayout>(arena: Seq<L::Node>, lids: Seq<nat>, m: int)
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

/// The in-order leaf at chain position `m` binds as a `Leaf` node: for a
/// `binds`-ing tree, `arena[tree_leaf_ids(t)[m]]` is a well-formed leaf whose
/// key count is `leaf_word_keys(arena, that id).len()`. Structural induction
/// (the leaf-id list and the leaf nodes recurse together); the forest companion
/// peels children using `leaf_id_offset` to locate which child holds position m.
pub proof fn lemma_chain_leaf_binds<L: NodeLayout>(arena: Seq<L::Node>, t: Tree, h: nat, is_root: bool, m: int)
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
pub proof fn lemma_chain_leaf_binds_forest<L: NodeLayout>(arena: Seq<L::Node>, kids: Seq<Tree>, ch: nat, m: int)
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
pub proof fn lemma_cursor_node_wf<K, L, S, const TRACK: bool>(c: &BPlusCursor<K, L, S, TRACK>)
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

/// A positioned cursor reads the model: `keys_view(arena[node])[pos].as_nat() ==
/// model[gidx]`. Composes `lemma_chain_keys_slice` (chain reading at the leaf's
/// slice == that leaf's pos-th key) with B2 (`chain_keys == tree_keys == model`).
pub proof fn lemma_cursor_key_at<K, L, S, const TRACK: bool>(c: &BPlusCursor<K, L, S, TRACK>)
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
pub proof fn lemma_model_value_bounded<K, L, S, const TRACK: bool>(
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

} // verus!
