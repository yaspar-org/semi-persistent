// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Verified equivalence-class aggregate (stage 2 of `doc/future/egraph-wf.md`):
//! the e-graph's class layer with W1-W6 as its machine-checked `wf()`.
//!
//! Production's `EClasses` (`egraph/src/classes.rs`) composes five structures
//! and keeps their agreement by argument. This module composes the five
//! VERIFIED counterparts — `CircularList` ring, `SparseSet` repr set,
//! `UnionFind`, `ListArena` use-lists, `Vec` min-monomial pool — and states
//! the agreement as `eg_model_wf`, a predicate over the components'
//! specification views:
//!
//!   - W1 lives inside `UnionFind::wf` (the ghost root map and its measure);
//!   - W2: `x` is a union-find root iff ring cell `x` carries a present
//!     payload, and the live keys of the repr set are exactly the root
//!     payloads (stated as an iff, with injectivity across roots);
//!   - W3: two nodes share a ring iff they share a root — stated over model
//!     coordinates in both directions (same ring implies same root, same
//!     root implies same ring), which is what discharges `splice_absorb`'s
//!     distinct-rings precondition inside `merge`;
//!   - W4: live classes own pairwise-distinct, allocated use-lists;
//!   - W5: every use-list entry is an allocated node id (freshness across a
//!     merge is the dirty-set discipline, stage 3 — deliberately not claimed);
//!   - W6: the pool is whole rows of `min_width`, live row numbers are
//!     allocated and pairwise distinct.
//!
//! The key stored in a ring payload is `Opt<T>` — the repr-set id carried as
//! a node-typed dense id, whose packed word is the same one production's
//! `Opt<T::Index>` cell holds at a bit-stealing family. This kernel does not
//! replace production (`do not touch prod`); it is the verified twin the
//! consumer migrates to when its API is complete.

use vstd::prelude::*;

use crate::circular_list::CircularList;
use crate::index_like::IndexLike;
use crate::inline_store::InlineStore;
use crate::list::{ListArena, ListNode};
use crate::opt::{DenseId, Opt};
use crate::parallel_store::ParallelStore;
use crate::sparse_set::SparseSet;
use crate::tagged::Tagged;
use crate::union_find::UnionFind;
use crate::vec::Vec as SpVec;

verus! {

// ---------------------------------------------------------------------------
// ClassData — per-class payload in the repr sparse set
// ---------------------------------------------------------------------------

/// Per-class data: the class's use-list id, its optional min-monomial pool
/// row number, and the atomic flag (production's `ClassData`).
#[derive(Copy)]
pub struct ClassData<L: DenseId, T: DenseId> {
    pub use_list: L,
    pub min_row: Option<<T as DenseId>::Index>,
    pub atomic: bool,
}

impl<L: DenseId, T: DenseId> Clone for ClassData<L, T> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

impl<L: DenseId, T: DenseId> core::default::Default for ClassData<L, T> {
    fn default() -> (r: ClassData<L, T>)
    {
        ClassData { use_list: L::default(), min_row: None, atomic: false }
    }
}

/// Repr for `ClassData`: the use-list word carries the capture tag
/// (production's ordering); `min_row` is stored as `(row, present)` because
/// `T::Index` has no spare niche. A named struct because Verus's
/// trait-conflict checker rejects `Tagged` on tuples (the `ListNodeRepr`
/// limitation).
#[derive(Copy)]
pub struct ClassDataRepr<LR, I> {
    pub a: LR,
    pub row: I,
    pub present: bool,
    pub atomic: bool,
}

impl<LR: Copy, I: Copy> Clone for ClassDataRepr<LR, I> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// `Tagged` for `ClassData`, delegating the capture tag to the use-list
/// word. `repr_wf` pins the absent-row encoding to a canonical `(min, false)`
/// — without that, two reprs differing only in a hidden dead `row` word would
/// decode equal, violating the extensionality law.
impl<L: DenseId, T: DenseId> Tagged for ClassData<L, T> {
    type Repr = ClassDataRepr<<L as Tagged>::Repr, <T as DenseId>::Index>;

    open spec fn value_of(r: Self::Repr) -> Self {
        ClassData {
            use_list: L::value_of(r.a),
            min_row: if r.present { Some(r.row) } else { None },
            atomic: r.atomic,
        }
    }
    open spec fn tag_of(r: Self::Repr) -> bool {
        L::tag_of(r.a)
    }
    open spec fn repr_wf(r: Self::Repr) -> bool {
        &&& L::repr_wf(r.a)
        &&& (!r.present ==> r.row == <T::Index as IndexLike>::min_spec())
    }

    proof fn lemma_repr_extensional(r1: Self::Repr, r2: Self::Repr) {
        L::lemma_repr_extensional(r1.a, r2.a);
        // equal values pin `present` (Some vs None) and, when present, `row`;
        // when absent, repr_wf pins both rows to the canonical min.
        if r1.present {
            assert(Self::value_of(r1).min_row == Some(r1.row));
        }
    }

    fn into_repr(self) -> (r: Self::Repr) {
        let (row, present) = match self.min_row {
            Some(r) => (r, true),
            None => (<T::Index as IndexLike>::min(), false),
        };
        proof { <T::Index as IndexLike>::lemma_min_as_nat(); }
        ClassDataRepr { a: self.use_list.into_repr(), row, present, atomic: self.atomic }
    }
    fn from_repr(r: &Self::Repr) -> (v: Self) {
        ClassData {
            use_list: L::from_repr(&r.a),
            min_row: if r.present { Some(r.row) } else { None },
            atomic: r.atomic,
        }
    }
    fn tag(r: &Self::Repr) -> (b: bool) {
        L::tag(&r.a)
    }
    fn set_tag(r: &mut Self::Repr) {
        L::set_tag(&mut r.a);
    }
    fn clear_tag(r: &mut Self::Repr) {
        L::clear_tag(&mut r.a);
    }
}

// ---------------------------------------------------------------------------
// The joint model invariant (free function, archive-restateable)
// ---------------------------------------------------------------------------

/// Sparse-set liveness over bare column views (`SparseSet::contains_spec`
/// restated so the archive can apply it to snapshots).
pub open(crate) spec fn ss_contains<Idx: IndexLike>(
    sparse: Seq<Idx>, indices: Seq<Idx>, live: nat, id: nat,
) -> bool {
    &&& id < sparse.len()
    &&& sparse[id as int].as_nat() < live
    &&& indices[sparse[id as int].as_nat() as int].as_nat() == id
}

/// The value stored for live key `id` (dense slot through the indirection).
pub open(crate) spec fn ss_value<V, Idx: IndexLike>(
    dense: Seq<V>, sparse: Seq<Idx>, id: nat,
) -> V {
    dense[sparse[id as int].as_nat() as int]
}

/// W2-W6 over the components' views. `ring_model`/`payloads` are the
/// `CircularList`'s ghost rings and payload cells; `roots` is the
/// `UnionFind`'s ghost root map; the three `reprs_*` sequences are the
/// `SparseSet` columns (`live` its element count); `uses_model`/`uses_nodes`
/// are the `ListArena`'s ghost lists and node cells; `pool_len`/`min_width`
/// the pool geometry.
pub open(crate) spec fn eg_model_wf<T: DenseId, L: DenseId, N: DenseId + Tagged>(
    ring_model: Seq<Seq<usize>>,
    payloads: Seq<Opt<T>>,
    roots: Seq<usize>,
    reprs_dense: Seq<ClassData<L, T>>,
    reprs_sparse: Seq<<T as DenseId>::Index>,
    reprs_indices: Seq<<T as DenseId>::Index>,
    uses_model: Seq<Seq<usize>>,
    uses_nodes: Seq<ListNode<T, N>>,
    pool_len: nat,
    min_width: nat,
) -> bool {
    let n = payloads.len();
    let live = reprs_dense.len();
    &&& roots.len() == n
    // payload cells decode (Opt well-formedness)
    &&& (forall|x: int| 0 <= x < n ==> (#[trigger] payloads[x]).wf())
    // W2a: a root iff a present payload
    &&& (forall|x: int| 0 <= x < n
            ==> ((#[trigger] roots[x]) == x as usize <==> payloads[x].get_spec() is Some))
    // W2b (one direction of the key bijection): a root's key is live, and its
    // stored data names an allocated use-list
    &&& (forall|x: int| 0 <= x < n && (#[trigger] roots[x]) == x as usize
            ==> ss_contains(reprs_sparse, reprs_indices, live,
                    payloads[x].get_spec()->Some_0.id_nat()))
    // W2c: keys are injective across roots
    &&& (forall|x: int, y: int|
            0 <= x < n && 0 <= y < n && x != y
                && (#[trigger] roots[x]) == x as usize && (#[trigger] roots[y]) == y as usize
                ==> payloads[x].get_spec()->Some_0.id_nat()
                    != payloads[y].get_spec()->Some_0.id_nat())
    // W2d (the other direction): every live key is some root's key
    &&& (forall|id: nat| #[trigger] ss_contains(reprs_sparse, reprs_indices, live, id)
            ==> exists|x: int| 0 <= x < n && roots[x] == x as usize
                && (#[trigger] payloads[x]).get_spec()->Some_0.id_nat() == id)
    // W3a: same ring implies same root
    &&& (forall|c: int, p: int, q: int|
            0 <= c < ring_model.len() && 0 <= p < ring_model[c].len()
                && 0 <= q < ring_model[c].len()
                ==> roots[(#[trigger] ring_model[c][p]) as int]
                    == roots[(#[trigger] ring_model[c][q]) as int])
    // W3b: same root implies same ring
    &&& (forall|c1: int, p1: int, c2: int, p2: int|
            0 <= c1 < ring_model.len() && 0 <= p1 < ring_model[c1].len()
                && 0 <= c2 < ring_model.len() && 0 <= p2 < ring_model[c2].len()
                && roots[(#[trigger] ring_model[c1][p1]) as int]
                    == roots[(#[trigger] ring_model[c2][p2]) as int]
                ==> c1 == c2)
    // W4: live classes own pairwise-distinct, allocated use-lists
    &&& (forall|id: nat| #[trigger] ss_contains(reprs_sparse, reprs_indices, live, id)
            ==> ss_value(reprs_dense, reprs_sparse, id).use_list.id_nat()
                < uses_model.len())
    &&& (forall|id1: nat, id2: nat|
            ss_contains(reprs_sparse, reprs_indices, live, id1)
                && ss_contains(reprs_sparse, reprs_indices, live, id2) && id1 != id2
                ==> #[trigger] ss_value(reprs_dense, reprs_sparse, id1).use_list.id_nat()
                    != #[trigger] ss_value(reprs_dense, reprs_sparse, id2).use_list.id_nat())
    // W5: every use-list entry names an allocated node
    &&& (forall|l: int, p: int|
            0 <= l < uses_model.len() && 0 <= p < (#[trigger] uses_model[l]).len()
                ==> uses_nodes[#[trigger] uses_model[l][p] as int].payload.id_nat() < n)
    // W6: whole rows; live row numbers allocated and pairwise distinct
    &&& (min_width > 0 ==> pool_len % min_width == 0)
    &&& (forall|id: nat| #[trigger] ss_contains(reprs_sparse, reprs_indices, live, id)
            && ss_value(reprs_dense, reprs_sparse, id).min_row is Some
            ==> min_width > 0
                && (ss_value(reprs_dense, reprs_sparse, id).min_row->Some_0.as_nat() + 1)
                    * min_width <= pool_len)
    &&& (forall|id1: nat, id2: nat|
            ss_contains(reprs_sparse, reprs_indices, live, id1)
                && ss_contains(reprs_sparse, reprs_indices, live, id2) && id1 != id2
                && #[trigger] ss_value(reprs_dense, reprs_sparse, id1).min_row is Some
                && #[trigger] ss_value(reprs_dense, reprs_sparse, id2).min_row is Some
                ==> ss_value(reprs_dense, reprs_sparse, id1).min_row->Some_0.as_nat()
                    != ss_value(reprs_dense, reprs_sparse, id2).min_row->Some_0.as_nat())
}

// ---------------------------------------------------------------------------
// EClasses
// ---------------------------------------------------------------------------

/// Verified equivalence classes: ring + union-find + repr set + use-lists +
/// min-monomial pool, with the agreement clauses as `wf`.
pub struct EClasses<T, L, N, const TRACK: bool>
where
    T: DenseId,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
{
    /// The class ring; each cell carries the class's repr key (as a
    /// node-typed dense id) while the class is live, absent once absorbed.
    pub(crate) entries: CircularList<Opt<T>, T, TRACK>,
    /// Per-class data, keyed by repr id.
    pub(crate) reprs: SparseSet<ClassData<L, T>, <T as DenseId>::Index,
        InlineStore<ClassData<L, T>, <T as DenseId>::Index>, TRACK>,
    /// Canonical-representative lookup (verified stage 1).
    pub(crate) uf: UnionFind<T, TRACK>,
    /// Per-class parent lists.
    pub(crate) uses: ListArena<T, L, N, TRACK>,
    /// Min-monomial pool: flat rows of `min_width` columns. `ParallelStore`,
    /// as production's `VecP`: `Opt` owns its niche bit, so it cannot sit in
    /// a bit-stealing `InlineStore`.
    pub(crate) min_pool: SpVec<Opt<T>, usize, ParallelStore<Opt<T>, usize>, TRACK>,
    /// Fixed row width; 0 until `set_min_width`.
    pub(crate) min_width: usize,
}

impl<T, L, N, const TRACK: bool> EClasses<T, L, N, TRACK>
where
    T: DenseId,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
{
    /// Node count (spec).
    pub open(crate) spec fn n_spec(&self) -> nat {
        self.entries.n_spec()
    }

    /// Live class count (spec).
    pub open(crate) spec fn num_classes_spec(&self) -> nat {
        self.reprs.n_spec()
    }

    pub open(crate) spec fn roots_view(&self) -> Seq<usize> {
        self.uf.roots_view()
    }

    /// Two nodes are in the same class (spec).
    pub open(crate) spec fn same_class_spec(&self, a: int, b: int) -> bool {
        self.uf.same_set_spec(a, b)
    }

    /// The repr key stored in `x`'s ring cell (meaningful when `x` is a root).
    pub open(crate) spec fn key_of(&self, x: int) -> nat {
        self.entries.payload_seq()[x].get_spec()->Some_0.id_nat()
    }

    /// The class data of live key `id` (spec).
    pub open(crate) spec fn class_data_spec(&self, id: nat) -> ClassData<L, T> {
        ss_value(self.reprs.dense_view(), self.reprs.sparse_view(), id)
    }

    pub open(crate) spec fn min_width_spec(&self) -> nat {
        self.min_width as nat
    }

    pub open(crate) spec fn wf(&self) -> bool {
        &&& self.entries.wf()
        &&& self.reprs.wf()
        &&& self.uf.wf()
        &&& self.uses.wf()
        &&& self.min_pool.wf()
        &&& self.uf.n_spec() == self.n_spec()
        &&& self.reprs.cap_spec() <= self.n_spec()
        &&& eg_model_wf::<T, L, N>(
                self.entries.model_view(),
                self.entries.payload_seq(),
                self.uf.roots_view(),
                self.reprs.dense_view(),
                self.reprs.sparse_view(),
                self.reprs.indices_view(),
                self.uses.model_view(),
                self.uses.nodes_view(),
                self.min_pool.view().len(),
                self.min_width as nat)
    }

    pub fn new() -> (e: Self)
        ensures e.wf(), e.n_spec() == 0, e.num_classes_spec() == 0,
            e.min_width_spec() == 0,
    {
        EClasses {
            entries: CircularList::new(),
            reprs: SparseSet::new_inline(),
            uf: UnionFind::new(),
            uses: ListArena::new(),
            min_pool: SpVec::<Opt<T>, usize, ParallelStore<Opt<T>, usize>, TRACK>::new(),
            min_width: 0,
        }
    }

    /// Node count as the id family's index word.
    pub fn len(&self) -> (n: <T as DenseId>::Index)
        requires self.wf(),
        ensures n.as_nat() == self.n_spec(),
    {
        self.uf.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.n_spec() == 0),
    {
        self.uf.is_empty()
    }

    /// Live class count.
    pub fn num_classes(&self) -> (n: <T as DenseId>::Index)
        requires self.wf(),
        ensures n.as_nat() == self.num_classes_spec(),
    {
        self.reprs.len()
    }

    /// Canonical representative (compressing).
    pub fn find(&mut self, x: T) -> (r: T)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).roots_view() == old(self).roots_view(),
            x.id_nat() < old(self).n_spec() ==> {
                &&& r.id_nat() == old(self).roots_view()[x.id_nat() as int] as nat
                &&& r.id_nat() < old(self).n_spec()
            },
    {
        let r = self.uf.find(x);
        proof {
            // only uf.parent changed (compression); every eg_model_wf clause
            // reads roots, which find preserves.
            assert(self.entries == old(self).entries);
            assert(self.reprs == old(self).reprs);
            assert(self.uses == old(self).uses);
            assert(self.min_pool == old(self).min_pool);
        }
        r
    }

    /// Canonical representative (read-only).
    pub fn find_const(&self, x: T) -> (r: T)
        requires self.wf(),
        ensures
            x.id_nat() < self.n_spec() ==> {
                &&& r.id_nat() == self.roots_view()[x.id_nat() as int] as nat
                &&& r.id_nat() < self.n_spec()
            },
    {
        self.uf.find_const(x)
    }

    /// The repr key of node `idx`'s ring cell, `None` once its class was
    /// absorbed (production's `repr_id`). For a CANONICAL id (a root), `Some`
    /// is guaranteed by W2.
    pub fn repr_id(&self, idx: T) -> (r: Option<<T as DenseId>::Index>)
        requires self.wf(),
        ensures
            idx.id_nat() < self.n_spec() ==> {
                &&& (r is Some <==> self.roots_view()[idx.id_nat() as int] == idx.id_nat() as usize)
                &&& (r matches Some(k) ==> k.as_nat() == self.key_of(idx.id_nat() as int))
            },
    {
        if !(idx.to_usize() < self.entries.len().as_usize()) {
            crate::guard::refuse("EClasses::repr_id: node id out of range");
        }
        let p = self.entries.payload_of(idx);
        proof {
            crate::opt::lemma_id_nat_fits_usize(idx);
            assert(p == self.entries.payload_seq()[idx.id_nat() as int]);
            assert(p.wf());
        }
        match p.to_option() {
            Some(k) => {
                proof {
                    if idx.id_nat() < self.n_spec() {
                        k.lemma_as_nat_is_id_nat();
                    }
                }
                Some(k.to_index())
            }
            None => None,
        }
    }

    /// Allocate a fresh node as its own singleton class; returns the node id
    /// and its repr key. Total-with-documented-panic at the capacity
    /// ceilings (production allocates through `expect` at the same points).
    pub fn add_singleton(&mut self) -> (r: (T, <T as DenseId>::Index))
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec() + 1,
            final(self).num_classes_spec() == old(self).num_classes_spec() + 1,
            r.0.id_nat() == old(self).n_spec(),
            r.1.as_nat() == final(self).key_of(r.0.id_nat() as int),
            final(self).roots_view()
                == old(self).roots_view().push(old(self).n_spec() as usize),
            final(self).key_of(r.0.id_nat() as int) == r.1.as_nat(),
            final(self).min_width_spec() == old(self).min_width_spec(),
    {
        let ghost n0 = self.n_spec();
        // 1. union-find slot
        let id = match self.uf.try_make_set() {
            Ok(id) => id,
            Err(_) => crate::guard::refuse("EClasses::add_singleton: node-id range exhausted"),
        };
        // 2. use-list
        let list_id = match self.uses.try_new_list() {
            Ok(l) => l,
            Err(_) => crate::guard::refuse("EClasses::add_singleton: use-list id range exhausted"),
        };
        // 3. repr slot
        let key = match self.reprs.try_add(ClassData {
            use_list: list_id, min_row: None, atomic: false,
        }) {
            Ok(k) => k,
            Err(_) => crate::guard::refuse("EClasses::add_singleton: repr capacity exhausted"),
        };
        // the key is representable as a node-typed id: a fresh key is the old
        // capacity (<= old n < id_bound after make_set), a recycled key is
        // below it.
        proof {
            crate::opt::lemma_id_nat_fits_usize(id);
            id.lemma_id_nat_bounded();
            assert(key.as_nat() <= old(self).reprs.cap_spec());
            assert(old(self).reprs.cap_spec() <= n0);
            assert(n0 < T::id_bound());
        }
        let key_t = match T::try_new(key.as_usize()) {
            Some(k) => k,
            None => {
                proof { assert(false); }
                crate::guard::refuse("EClasses::add_singleton: unreachable key mint")
            }
        };
        // 4. ring cell
        let opt_key = Opt::some(key_t);
        let ring_id = match self.entries.try_add_singleton(opt_key) {
            Ok(rid) => rid,
            Err(_) => crate::guard::refuse("EClasses::add_singleton: ring capacity exhausted"),
        };
        proof {
            assert(ring_id.id_nat() == n0);
            assert(id.id_nat() == n0);
            T::lemma_id_injective(ring_id, id);

            let o = *old(self);
            let n1 = n0 + 1;
            let rm = self.entries.model_view();
            let pay = self.entries.payload_seq();
            let roots = self.uf.roots_view();
            let dense = self.reprs.dense_view();
            let sparse = self.reprs.sparse_view();
            let indices = self.reprs.indices_view();
            let um = self.uses.model_view();
            let un = self.uses.nodes_view();
            let orm = o.entries.model_view();
            let opay = o.entries.payload_seq();
            let oroots = o.uf.roots_view();
            let odense = o.reprs.dense_view();
            let osparse = o.reprs.sparse_view();
            let oindices = o.reprs.indices_view();
            let oum = o.uses.model_view();
            let olive = o.reprs.n_spec();
            let live = self.reprs.n_spec();
            let kn = key.as_nat();

            assert(pay == opay.push(opt_key));
            assert(opt_key.get_spec() == Some(key_t));
            assert(rm == orm.push(seq![n0 as usize]));
            assert(roots == oroots.push(n0 as usize));
            assert(um == oum.push(Seq::<usize>::empty()));
            assert(un == o.uses.nodes_view());
            assert(pay.len() == n1);
            assert(key_t.id_nat() == kn);
            crate::opt::lemma_id_nat_fits_usize(id);

            // the new key is live, with the fresh ClassData
            assert(self.reprs.contains_spec(key));
            assert(ss_contains(sparse, indices, live, kn));
            assert(ss_value(dense, sparse, kn)
                == ClassData::<L, T> { use_list: list_id, min_row: None, atomic: false });

            // survivors: old liveness and values carry over, id-for-nat
            assert forall|kk: nat| #[trigger] ss_contains(osparse, oindices, olive, kk)
                implies ss_contains(sparse, indices, live, kk)
                    && ss_value(dense, sparse, kk) == ss_value(odense, osparse, kk)
                    && kk != kn by {
                let kw = oindices[osparse[kk as int].as_nat() as int];
                assert(kw.as_nat() == kk);
                assert(o.reprs.contains_spec(kw));
                assert(self.reprs.contains_spec(kw));
                // the fresh key was not live before
                assert(!o.reprs.id_set().contains(kn));
                if kk == kn {
                    assert(o.reprs.id_set().contains(kk)) by {
                        assert(oindices[osparse[kk as int].as_nat() as int].as_nat() == kk);
                    }
                }
            }
            // dead keys stay dead (contrapositive of the id_set update)
            assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk) && kk != kn
                implies ss_contains(osparse, oindices, olive, kk) by {
                let kw = indices[sparse[kk as int].as_nat() as int];
                assert(kw.as_nat() == kk);
                assert(self.reprs.contains_spec(kw));
                assert(self.reprs.id_set().contains(kk)) by {
                    assert(indices[sparse[kk as int].as_nat() as int].as_nat() == kk);
                }
                assert(o.reprs.id_set().contains(kk));
                let p = choose|p: int| 0 <= p < olive
                    && (#[trigger] oindices[p]).as_nat() == kk;
                let ow = oindices[p];
                assert(o.reprs.contains_spec(ow));
            }

            // --- W2a
            assert forall|x: int| 0 <= x < n1 implies
                ((#[trigger] roots[x]) == x as usize <==> pay[x].get_spec() is Some) by {
                if x < n0 {
                    assert(roots[x] == oroots[x]);
                    assert(pay[x] == opay[x]);
                }
            }
            // --- W2b
            assert forall|x: int| 0 <= x < n1 && (#[trigger] roots[x]) == x as usize
                implies ss_contains(sparse, indices, live,
                    pay[x].get_spec()->Some_0.id_nat()) by {
                if x < n0 {
                    assert(ss_contains(osparse, oindices, olive,
                        opay[x].get_spec()->Some_0.id_nat()));
                    assert(pay[x] == opay[x]);
                }
            }
            // --- W2c
            assert forall|x: int, y: int|
                0 <= x < n1 && 0 <= y < n1 && x != y
                    && (#[trigger] roots[x]) == x as usize
                    && (#[trigger] roots[y]) == y as usize
                implies pay[x].get_spec()->Some_0.id_nat()
                    != pay[y].get_spec()->Some_0.id_nat() by {
                if x < n0 && y < n0 {
                    assert(pay[x] == opay[x] && pay[y] == opay[y]);
                } else if x == n0 as int && y < n0 {
                    // the fresh key differs from every old root's key, which
                    // is live in the OLD set.
                    assert(pay[y] == opay[y]);
                    assert(ss_contains(osparse, oindices, olive,
                        opay[y].get_spec()->Some_0.id_nat()));
                } else if y == n0 as int && x < n0 {
                    assert(pay[x] == opay[x]);
                    assert(ss_contains(osparse, oindices, olive,
                        opay[x].get_spec()->Some_0.id_nat()));
                }
            }
            // --- W2d
            assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
                implies exists|x: int| 0 <= x < n1 && roots[x] == x as usize
                    && (#[trigger] pay[x]).get_spec()->Some_0.id_nat() == kk by {
                if kk == kn {
                    assert(roots[n0 as int] == n0 as usize);
                    assert(pay[n0 as int].get_spec()->Some_0.id_nat() == kk);
                } else {
                    assert(ss_contains(osparse, oindices, olive, kk));
                    let x = choose|x: int| 0 <= x < n0 && oroots[x] == x as usize
                        && (#[trigger] opay[x]).get_spec()->Some_0.id_nat() == kk;
                    assert(roots[x] == x as usize);
                    assert(pay[x].get_spec()->Some_0.id_nat() == kk);
                }
            }
            // --- W3a / W3b (rings gained the singleton [n0])
            assert forall|c: int, p: int, q: int|
                0 <= c < rm.len() && 0 <= p < rm[c].len() && 0 <= q < rm[c].len()
                implies roots[(#[trigger] rm[c][p]) as int]
                    == roots[(#[trigger] rm[c][q]) as int] by {
                if c < orm.len() {
                    assert(rm[c] == orm[c]);
                    assert(orm[c][p] < n0 && orm[c][q] < n0);
                    assert(roots[orm[c][p] as int] == oroots[orm[c][p] as int]);
                    assert(roots[orm[c][q] as int] == oroots[orm[c][q] as int]);
                }
            }
            assert forall|c1: int, p1: int, c2: int, p2: int|
                0 <= c1 < rm.len() && 0 <= p1 < rm[c1].len()
                    && 0 <= c2 < rm.len() && 0 <= p2 < rm[c2].len()
                    && roots[(#[trigger] rm[c1][p1]) as int]
                        == roots[(#[trigger] rm[c2][p2]) as int]
                implies c1 == c2 by {
                if c1 < orm.len() && c2 < orm.len() {
                    assert(rm[c1] == orm[c1] && rm[c2] == orm[c2]);
                    assert(orm[c1][p1] < n0 && orm[c2][p2] < n0);
                } else if c1 < orm.len() && c2 == orm.len() as int {
                    // old member's root is an old id (< n0); the new ring's
                    // sole member has root n0.
                    assert(rm[c1][p1] < n0);
                    assert(roots[rm[c1][p1] as int] == oroots[rm[c1][p1] as int]);
                    assert(oroots[rm[c1][p1] as int] < n0 as usize);
                    assert(rm[c2][p2] == n0 as usize);
                    assert(roots[n0 as int] == n0 as usize);
                } else if c2 < orm.len() && c1 == orm.len() as int {
                    assert(rm[c2][p2] < n0);
                    assert(roots[rm[c2][p2] as int] == oroots[rm[c2][p2] as int]);
                    assert(oroots[rm[c2][p2] as int] < n0 as usize);
                    assert(rm[c1][p1] == n0 as usize);
                    assert(roots[n0 as int] == n0 as usize);
                }
            }
            // --- W4
            assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
                implies ss_value(dense, sparse, kk).use_list.id_nat() < um.len() by {
                if kk != kn {
                    assert(ss_contains(osparse, oindices, olive, kk));
                    assert(ss_value(dense, sparse, kk) == ss_value(odense, osparse, kk));
                }
            }
            assert forall|k1: nat, k2: nat|
                ss_contains(sparse, indices, live, k1)
                    && ss_contains(sparse, indices, live, k2) && k1 != k2
                implies #[trigger] ss_value(dense, sparse, k1).use_list.id_nat()
                    != #[trigger] ss_value(dense, sparse, k2).use_list.id_nat() by {
                if k1 != kn && k2 != kn {
                    assert(ss_contains(osparse, oindices, olive, k1));
                    assert(ss_contains(osparse, oindices, olive, k2));
                    assert(ss_value(dense, sparse, k1) == ss_value(odense, osparse, k1));
                    assert(ss_value(dense, sparse, k2) == ss_value(odense, osparse, k2));
                } else if k1 == kn {
                    assert(ss_contains(osparse, oindices, olive, k2));
                    assert(ss_value(dense, sparse, k2) == ss_value(odense, osparse, k2));
                    assert(ss_value(dense, sparse, k2).use_list.id_nat() < oum.len());
                    assert(ss_value(dense, sparse, k1).use_list.id_nat() == oum.len());
                } else {
                    assert(ss_contains(osparse, oindices, olive, k1));
                    assert(ss_value(dense, sparse, k1) == ss_value(odense, osparse, k1));
                    assert(ss_value(dense, sparse, k1).use_list.id_nat() < oum.len());
                    assert(ss_value(dense, sparse, k2).use_list.id_nat() == oum.len());
                }
            }
            // --- W5 (new list is empty; old lists and nodes untouched)
            assert forall|l: int, p: int|
                0 <= l < um.len() && 0 <= p < (#[trigger] um[l]).len()
                implies un[#[trigger] um[l][p] as int].payload.id_nat() < n1 by {
                assert(l < oum.len());
                assert(um[l] == oum[l]);
            }
            // --- W6 (pool untouched; new key has no row)
            assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
                && ss_value(dense, sparse, kk).min_row is Some
                implies self.min_width as nat > 0
                    && (ss_value(dense, sparse, kk).min_row->Some_0.as_nat() + 1)
                        * (self.min_width as nat) <= self.min_pool.view().len() by {
                assert(kk != kn);
                assert(ss_contains(osparse, oindices, olive, kk));
                assert(ss_value(dense, sparse, kk) == ss_value(odense, osparse, kk));
            }
            assert forall|k1: nat, k2: nat|
                ss_contains(sparse, indices, live, k1)
                    && ss_contains(sparse, indices, live, k2) && k1 != k2
                    && #[trigger] ss_value(dense, sparse, k1).min_row is Some
                    && #[trigger] ss_value(dense, sparse, k2).min_row is Some
                implies ss_value(dense, sparse, k1).min_row->Some_0.as_nat()
                    != ss_value(dense, sparse, k2).min_row->Some_0.as_nat() by {
                assert(k1 != kn && k2 != kn);
                assert(ss_contains(osparse, oindices, olive, k1));
                assert(ss_contains(osparse, oindices, olive, k2));
                assert(ss_value(dense, sparse, k1) == ss_value(odense, osparse, k1));
                assert(ss_value(dense, sparse, k2) == ss_value(odense, osparse, k2));
            }
            assert(eg_model_wf::<T, L, N>(rm, pay, roots, dense, sparse, indices,
                um, un, self.min_pool.view().len(), self.min_width as nat));
        }
        (id, key)
    }
}


/// W5 after a use-list splice, over bare views (extracted like
/// `lemma_splice_disjoint`: in the method body this quantifier e-matches
/// against both states' full wf).
pub(crate) proof fn lemma_splice_uses_w5<T: DenseId, N: DenseId + Tagged>(
    oum: Seq<Seq<usize>>, um: Seq<Seq<usize>>,
    oun: Seq<ListNode<T, N>>, un: Seq<ListNode<T, N>>,
    di: int, si: int, n: nat,
)
    requires
        0 <= di < oum.len(),
        0 <= si < oum.len(),
        di != si,
        um == oum.update(di, oum[di] + oum[si]).update(si, Seq::<usize>::empty()),
        un.len() == oun.len(),
        forall|k: int| 0 <= k < oun.len()
            ==> (#[trigger] un[k]).payload == oun[k].payload,
        forall|l: int, p: int|
            0 <= l < oum.len() && 0 <= p < oum[l].len()
                ==> (#[trigger] oum[l][p]) < oun.len(),
        forall|l: int, p: int|
            0 <= l < oum.len() && 0 <= p < oum[l].len()
                ==> oun[(#[trigger] oum[l][p]) as int].payload.id_nat() < n,
    ensures
        forall|l: int, p: int|
            0 <= l < um.len() && 0 <= p < (#[trigger] um[l]).len()
                ==> un[#[trigger] um[l][p] as int].payload.id_nat() < n,
{
    assert forall|l: int, p: int|
        0 <= l < um.len() && 0 <= p < (#[trigger] um[l]).len()
        implies un[#[trigger] um[l][p] as int].payload.id_nat() < n by {
        if l == di {
            if p < oum[di].len() {
                assert(um[l][p] == oum[di][p]);
            } else {
                assert(um[l][p] == oum[si][p - oum[di].len()]);
            }
        } else if l != si {
            assert(um[l] == oum[l]);
        }
        assert(um[l][p] < oun.len());
        assert(un[um[l][p] as int].payload == oun[um[l][p] as int].payload);
    }
}

// ---------------------------------------------------------------------------
// Merge
// ---------------------------------------------------------------------------

/// Returned by `merge`: the surviving and absorbed canonical ids plus the
/// absorbed class's data, which the rebuild loop consumes (production's
/// `MergeInfo`).
pub struct MergeInfo<T: DenseId, L: DenseId> {
    pub survivor: T,
    pub absorbed: T,
    pub absorbed_uses: L,
    pub absorbed_min_row: Option<<T as DenseId>::Index>,
    pub absorbed_atomic: bool,
}

impl<T, L, N, const TRACK: bool> EClasses<T, L, N, TRACK>
where
    T: DenseId,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
{

    /// Re-establishes `eg_model_wf` after a merge's three mutations (union,
    /// ring splice with payload clear, repr removal). Extracted for the same
    /// reason as `lemma_splice_disjoint` (list.rs): proved inline, the ring
    /// and root quantifiers e-match against both states' full `wf`.
    proof fn lemma_merge_wf(&self, o: Self, s: T, ab: T, key_ab: nat, ab_pay: Opt<T>,
        cs: int, ps: int, ca: int, pa: int)
        requires
            o.wf(),
            self.uf.wf(),
            self.entries.wf(),
            self.reprs.wf(),
            self.uses.wf(),
            self.min_pool.wf(),
            s.id_nat() < o.n_spec(),
            ab.id_nat() < o.n_spec(),
            s.id_nat() != ab.id_nat(),
            s.id_nat() <= usize::MAX as nat,
            ab.id_nat() <= usize::MAX as nat,
            o.roots_view()[s.id_nat() as int] == s.id_nat() as usize,
            o.roots_view()[ab.id_nat() as int] == ab.id_nat() as usize,
            key_ab == o.key_of(ab.id_nat() as int),
            ss_contains(o.reprs.sparse_view(), o.reprs.indices_view(),
                o.reprs.n_spec(), key_ab),
            0 <= cs < o.entries.model_view().len(),
            0 <= ps < o.entries.model_view()[cs].len(),
            o.entries.model_view()[cs][ps] == s.id_nat() as usize,
            0 <= ca < o.entries.model_view().len(),
            0 <= pa < o.entries.model_view()[ca].len(),
            o.entries.model_view()[ca][pa] == ab.id_nat() as usize,
            cs != ca,
            self.entries.model_view() == o.entries.model_view()
                .update(cs, crate::circular_list::rotate(o.entries.model_view()[cs], ps + 1)
                    + crate::circular_list::rotate(o.entries.model_view()[ca], pa + 1))
                .update(ca, Seq::<usize>::empty()),
            self.entries.payload_seq()
                == o.entries.payload_seq().update(ab.id_nat() as int, ab_pay),
            self.entries.n_spec() == o.n_spec(),
            ab_pay.wf(),
            ab_pay.get_spec() is None,
            self.uf.roots_view() == crate::union_find::merge_roots(
                o.roots_view(), s.id_nat(), ab.id_nat()),
            self.uf.n_spec() == o.n_spec(),
            self.reprs.n_spec() == o.reprs.n_spec() - 1,
            self.reprs.cap_spec() == o.reprs.cap_spec(),
            self.reprs.id_set() == o.reprs.id_set().remove(key_ab),
            forall|k: <T as DenseId>::Index| #[trigger] o.reprs.contains_spec(k)
                && k.as_nat() != key_ab
                ==> self.reprs.contains_spec(k)
                    && ss_value(self.reprs.dense_view(), self.reprs.sparse_view(),
                            k.as_nat())
                        == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(),
                            k.as_nat()),
            self.uses.model_view() == o.uses.model_view(),
            self.uses.nodes_view() == o.uses.nodes_view(),
            self.min_pool.view() == o.min_pool.view(),
            self.min_width == o.min_width,
        ensures
            eg_model_wf::<T, L, N>(
                self.entries.model_view(), self.entries.payload_seq(),
                self.uf.roots_view(), self.reprs.dense_view(),
                self.reprs.sparse_view(), self.reprs.indices_view(),
                self.uses.model_view(), self.uses.nodes_view(),
                self.min_pool.view().len(), self.min_width as nat),
            self.reprs.cap_spec() <= self.n_spec(),
    {
        let n = o.n_spec();
        let sn = s.id_nat();
        let abn = ab.id_nat();
        let su = sn as usize;
        let abu = abn as usize;
        let orm = o.entries.model_view();
        let opay = o.entries.payload_seq();
        let oroots = o.roots_view();
        let odense = o.reprs.dense_view();
        let osparse = o.reprs.sparse_view();
        let oindices = o.reprs.indices_view();
        let olive = o.reprs.n_spec();
        let rm = self.entries.model_view();
        let pay = self.entries.payload_seq();
        let roots = self.uf.roots_view();
        let dense = self.reprs.dense_view();
        let sparse = self.reprs.sparse_view();
        let indices = self.reprs.indices_view();
        let live = self.reprs.n_spec();
        let um = self.uses.model_view();
        let un = self.uses.nodes_view();
        let merged = crate::circular_list::rotate(orm[cs], ps + 1)
            + crate::circular_list::rotate(orm[ca], pa + 1);

        // casts between int positions and usize root values are faithful:
        // every id is below n <= id_bound <= usize::MAX + 1.
        T::lemma_id_bound_fits_usize();
        assert(n <= usize::MAX as nat + 1);

        crate::circular_list::lemma_rotate_props(orm[cs], ps + 1);
        crate::circular_list::lemma_rotate_props(orm[ca], pa + 1);

        // every merged-ring element is an element of one of the two old rings
        assert forall|q: int| 0 <= q < merged.len() implies
            exists|c0: int, j: int| (c0 == cs || c0 == ca)
                && 0 <= j < orm[c0].len() && orm[c0][j] == #[trigger] merged[q] by {
            let lcs = orm[cs].len() as int;
            if q < lcs {
                let j = if ps + 1 + q < lcs { ps + 1 + q } else { ps + 1 + q - lcs };
                assert(merged[q] == orm[cs][j]);
            } else {
                let q2 = q - lcs;
                let lca = orm[ca].len() as int;
                let j = if pa + 1 + q2 < lca { pa + 1 + q2 } else { pa + 1 + q2 - lca };
                assert(merged[q] == orm[ca][j]);
            }
        }
        // old roots of the two rings' members: cs members root to s, ca to ab
        assert forall|j: int| 0 <= j < orm[cs].len() implies
            oroots[(#[trigger] orm[cs][j]) as int] == su by {
            assert(oroots[orm[cs][j] as int] == oroots[orm[cs][ps] as int]);
        }
        assert forall|j: int| 0 <= j < orm[ca].len() implies
            oroots[(#[trigger] orm[ca][j]) as int] == abu by {
            assert(oroots[orm[ca][j] as int] == oroots[orm[ca][pa] as int]);
        }
        // a member of any OTHER ring roots to neither s nor ab
        assert forall|c: int, p: int|
            0 <= c < orm.len() && c != cs && c != ca && 0 <= p < orm[c].len()
            implies oroots[(#[trigger] orm[c][p]) as int] != su
                && oroots[orm[c][p] as int] != abu by {
            if oroots[orm[c][p] as int] == su {
                // same root as s -> same ring as s (old W3b) -> c == cs.
                assert(oroots[orm[cs][ps] as int] == su);
            }
            if oroots[orm[c][p] as int] == abu {
                assert(oroots[orm[ca][pa] as int] == abu);
            }
        }
        // the remap in one line: roots[x] = s if old ab, else old.
        assert forall|x: int| 0 <= x < n implies
            #[trigger] roots[x] == (if oroots[x] == abu { su } else { oroots[x] }) by {
            assert(roots[x] == crate::union_find::merge_roots(oroots, sn, abn)[x]);
        }

        // survivors + dead-stay-dead, in the nat form the clauses use
        assert forall|kk: nat| #[trigger] ss_contains(osparse, oindices, olive, kk)
            && kk != key_ab
            implies ss_contains(sparse, indices, live, kk)
                && ss_value(dense, sparse, kk) == ss_value(odense, osparse, kk) by {
            let kw = oindices[osparse[kk as int].as_nat() as int];
            assert(kw.as_nat() == kk);
            assert(o.reprs.contains_spec(kw));
            assert(self.reprs.contains_spec(kw));
        }
        assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
            implies ss_contains(osparse, oindices, olive, kk) && kk != key_ab by {
            let kw = indices[sparse[kk as int].as_nat() as int];
            assert(kw.as_nat() == kk);
            assert(self.reprs.contains_spec(kw));
            assert(self.reprs.id_set().contains(kk)) by {
                assert(indices[sparse[kk as int].as_nat() as int].as_nat() == kk);
            }
            assert(o.reprs.id_set().contains(kk) && kk != key_ab);
            let p = choose|p: int| 0 <= p < olive
                && (#[trigger] oindices[p]).as_nat() == kk;
            let ow = oindices[p];
            assert(o.reprs.contains_spec(ow));
        }

        // --- Opt wf on payload cells
        assert forall|x: int| 0 <= x < n implies (#[trigger] pay[x]).wf() by {
            if x != abn as int { assert(pay[x] == opay[x]); }
        }
        // --- W2a
        assert forall|x: int| 0 <= x < n implies
            ((#[trigger] roots[x]) == x as usize <==> pay[x].get_spec() is Some) by {
            if x == abn as int {
                assert(roots[x] == su);
                assert(pay[x] == ab_pay);
            } else {
                assert(pay[x] == opay[x]);
                if oroots[x] == abu {
                    // x was in ab's class but is not ab: not an old root
                    // (an old root satisfies oroots[x] == x, which with
                    // oroots[x] == ab forces x == ab), and its new root is
                    // s != x (x == s would make s's old root ab).
                    if oroots[x] == x as usize {
                        assert(x as usize == abu);
                        assert(x == abn as int);
                        assert(false);
                    }
                    assert(roots[x] == su);
                    if roots[x] == x as usize {
                        assert(x as usize == su);
                        assert(x == sn as int);
                        assert(oroots[sn as int] == su);
                        assert(false);
                    }
                } else {
                    assert(roots[x] == oroots[x]);
                }
            }
        }
        // --- W2b
        assert forall|x: int| 0 <= x < n && (#[trigger] roots[x]) == x as usize
            implies ss_contains(sparse, indices, live,
                pay[x].get_spec()->Some_0.id_nat()) by {
            assert(x != abn as int);
            assert(pay[x] == opay[x]);
            assert(oroots[x] == x as usize);
            assert(ss_contains(osparse, oindices, olive,
                opay[x].get_spec()->Some_0.id_nat()));
            // x's key is not ab's key: W2c injectivity in the old state.
            assert(opay[x].get_spec()->Some_0.id_nat() != key_ab);
        }
        // --- W2c
        assert forall|x: int, y: int|
            0 <= x < n && 0 <= y < n && x != y
                && (#[trigger] roots[x]) == x as usize
                && (#[trigger] roots[y]) == y as usize
            implies pay[x].get_spec()->Some_0.id_nat()
                != pay[y].get_spec()->Some_0.id_nat() by {
            assert(x != abn as int && y != abn as int);
            assert(pay[x] == opay[x] && pay[y] == opay[y]);
            assert(oroots[x] == x as usize && oroots[y] == y as usize);
        }
        // --- W2d
        assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
            implies exists|x: int| 0 <= x < n && roots[x] == x as usize
                && (#[trigger] pay[x]).get_spec()->Some_0.id_nat() == kk by {
            assert(ss_contains(osparse, oindices, olive, kk) && kk != key_ab);
            let x = choose|x: int| 0 <= x < n && oroots[x] == x as usize
                && (#[trigger] opay[x]).get_spec()->Some_0.id_nat() == kk;
            // x is an old root with key kk != key_ab, so x != ab, so x keeps
            // its payload; and x's class was not ab's (both were roots), so
            // its root stays x.
            assert(x != abn as int) by {
                if x == abn as int { assert(kk == key_ab); }
            }
            assert(oroots[x] != abu) by {
                if oroots[x] == abu {
                    assert(x as usize == abu);
                    assert(x == abn as int);
                    assert(false);
                }
            }
            assert(roots[x] == x as usize);
            assert(pay[x] == opay[x]);
        }
        // --- W3a
        assert forall|c: int, p: int, q: int|
            0 <= c < rm.len() && 0 <= p < rm[c].len() && 0 <= q < rm[c].len()
            implies roots[(#[trigger] rm[c][p]) as int]
                == roots[(#[trigger] rm[c][q]) as int] by {
            if c == cs {
                assert(rm[c] == merged);
                // both elements come from the two old rings; either way the
                // new root is s.
                let (c1, j1) = choose|c0: int, j: int| (c0 == cs || c0 == ca)
                    && 0 <= j < orm[c0].len() && orm[c0][j] == merged[p];
                let (c2, j2) = choose|c0: int, j: int| (c0 == cs || c0 == ca)
                    && 0 <= j < orm[c0].len() && orm[c0][j] == merged[q];
                assert(roots[merged[p] as int] == su);
                assert(roots[merged[q] as int] == su);
            } else if c == ca {
                assert(rm[c].len() == 0);
            } else {
                assert(rm[c] == orm[c]);
                assert(oroots[orm[c][p] as int] == oroots[orm[c][q] as int]);
                assert(oroots[orm[c][p] as int] != abu);
            }
        }
        // --- W3b
        assert forall|c1: int, p1: int, c2: int, p2: int|
            0 <= c1 < rm.len() && 0 <= p1 < rm[c1].len()
                && 0 <= c2 < rm.len() && 0 <= p2 < rm[c2].len()
                && roots[(#[trigger] rm[c1][p1]) as int]
                    == roots[(#[trigger] rm[c2][p2]) as int]
            implies c1 == c2 by {
            // roots of members: cs -> s; other rings -> their old root,
            // which is neither s nor ab.
            if c1 == cs && c2 != cs && c2 != ca {
                assert(roots[rm[c1][p1] as int] == su);
                assert(rm[c2] == orm[c2]);
                assert(oroots[orm[c2][p2] as int] != abu);
                assert(roots[rm[c2][p2] as int] == oroots[orm[c2][p2] as int]);
                assert(oroots[orm[c2][p2] as int] != su);
                assert(false);
            } else if c2 == cs && c1 != cs && c1 != ca {
                assert(roots[rm[c2][p2] as int] == su);
                assert(rm[c1] == orm[c1]);
                assert(oroots[orm[c1][p1] as int] != abu);
                assert(roots[rm[c1][p1] as int] == oroots[orm[c1][p1] as int]);
                assert(oroots[orm[c1][p1] as int] != su);
                assert(false);
            } else if c1 != cs && c1 != ca && c2 != cs && c2 != ca {
                assert(rm[c1] == orm[c1] && rm[c2] == orm[c2]);
                assert(oroots[orm[c1][p1] as int] != abu);
                assert(oroots[orm[c2][p2] as int] != abu);
                assert(roots[rm[c1][p1] as int] == oroots[orm[c1][p1] as int]);
                assert(roots[rm[c2][p2] as int] == oroots[orm[c2][p2] as int]);
            } else if c1 == ca {
                assert(rm[ca].len() == 0);
            } else if c2 == ca {
                assert(rm[ca].len() == 0);
            }
        }
        // --- W4
        assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
            implies ss_value(dense, sparse, kk).use_list.id_nat() < um.len() by {
            assert(ss_contains(osparse, oindices, olive, kk) && kk != key_ab);
            assert(ss_value(dense, sparse, kk) == ss_value(odense, osparse, kk));
        }
        assert forall|k1: nat, k2: nat|
            ss_contains(sparse, indices, live, k1)
                && ss_contains(sparse, indices, live, k2) && k1 != k2
            implies #[trigger] ss_value(dense, sparse, k1).use_list.id_nat()
                != #[trigger] ss_value(dense, sparse, k2).use_list.id_nat() by {
            assert(ss_contains(osparse, oindices, olive, k1) && k1 != key_ab);
            assert(ss_contains(osparse, oindices, olive, k2) && k2 != key_ab);
            assert(ss_value(dense, sparse, k1) == ss_value(odense, osparse, k1));
            assert(ss_value(dense, sparse, k2) == ss_value(odense, osparse, k2));
        }
        // --- W5 (uses untouched)
        assert forall|l: int, p: int|
            0 <= l < um.len() && 0 <= p < (#[trigger] um[l]).len()
            implies un[#[trigger] um[l][p] as int].payload.id_nat() < n by {
            assert(um[l] == o.uses.model_view()[l]);
        }
        // --- W6
        assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
            && ss_value(dense, sparse, kk).min_row is Some
            implies self.min_width as nat > 0
                && (ss_value(dense, sparse, kk).min_row->Some_0.as_nat() + 1)
                    * (self.min_width as nat) <= self.min_pool.view().len() by {
            assert(ss_contains(osparse, oindices, olive, kk) && kk != key_ab);
            assert(ss_value(dense, sparse, kk) == ss_value(odense, osparse, kk));
        }
        assert forall|k1: nat, k2: nat|
            ss_contains(sparse, indices, live, k1)
                && ss_contains(sparse, indices, live, k2) && k1 != k2
                && #[trigger] ss_value(dense, sparse, k1).min_row is Some
                && #[trigger] ss_value(dense, sparse, k2).min_row is Some
            implies ss_value(dense, sparse, k1).min_row->Some_0.as_nat()
                != ss_value(dense, sparse, k2).min_row->Some_0.as_nat() by {
            assert(ss_contains(osparse, oindices, olive, k1) && k1 != key_ab);
            assert(ss_contains(osparse, oindices, olive, k2) && k2 != key_ab);
            assert(ss_value(dense, sparse, k1) == ss_value(odense, osparse, k1));
            assert(ss_value(dense, sparse, k2) == ss_value(odense, osparse, k2));
        }
        assert(eg_model_wf::<T, L, N>(rm, pay, roots, dense, sparse, indices,
            um, un, self.min_pool.view().len(), self.min_width as nat));
    }

    /// Merge the classes of `a` and `b`: union-find link, ring splice with
    /// the absorbed payload cleared, repr removal. `None` iff already one
    /// class. The core of `merge` and `merge_directed`; the distinct-rings
    /// precondition of `splice_absorb` is DISCHARGED here from W2 + W3 —
    /// the machine-checked form of the argument that closes the
    /// WITNESS-PENDING allowlist entries for the aggregate's use.
    pub(crate) fn merge_with(&mut self, a: T, b: T, directed: bool, prefer_a: bool)
        -> (r: Option<MergeInfo<T, L>>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).min_width_spec() == old(self).min_width_spec(),
            a.id_nat() < old(self).n_spec() && b.id_nat() < old(self).n_spec() ==> {
                let ra = old(self).roots_view()[a.id_nat() as int] as nat;
                let rb = old(self).roots_view()[b.id_nat() as int] as nat;
                &&& (r is None <==> ra == rb)
                &&& (r is None ==> final(self).roots_view() == old(self).roots_view()
                        && final(self).num_classes_spec() == old(self).num_classes_spec())
                &&& (r matches Some(mi) ==> {
                        &&& ((mi.survivor.id_nat() == ra && mi.absorbed.id_nat() == rb)
                            || (mi.survivor.id_nat() == rb && mi.absorbed.id_nat() == ra))
                        &&& (directed ==> mi.survivor.id_nat()
                                == (if prefer_a { ra } else { rb }))
                        &&& ra != rb
                        &&& final(self).roots_view() == crate::union_find::merge_roots(
                                old(self).roots_view(), mi.survivor.id_nat(),
                                mi.absorbed.id_nat())
                        &&& final(self).num_classes_spec()
                            == old(self).num_classes_spec() - 1
                        &&& mi.absorbed_uses == old(self).class_data_spec(
                                old(self).key_of(mi.absorbed.id_nat() as int)).use_list
                        &&& mi.absorbed_min_row == old(self).class_data_spec(
                                old(self).key_of(mi.absorbed.id_nat() as int)).min_row
                        &&& mi.absorbed_atomic == old(self).class_data_spec(
                                old(self).key_of(mi.absorbed.id_nat() as int)).atomic
                    })
            },
    {
        if !(a.to_usize() < self.uf.len().as_usize()
            && b.to_usize() < self.uf.len().as_usize())
        {
            crate::guard::refuse("EClasses::merge: node id out of range");
        }
        let ghost o = *old(self);
        let ghost n = o.n_spec();
        let res = if directed {
            self.uf.union_directed(a, b, prefer_a)
        } else {
            self.uf.union(a, b)
        };
        let (s, ab) = match res {
            None => {
                return None;
            }
            Some(pair) => pair,
        };
        proof {
            crate::opt::lemma_id_nat_fits_usize(s);
            crate::opt::lemma_id_nat_fits_usize(ab);
            // s and ab are distinct old roots.
            assert(o.roots_view()[s.id_nat() as int] == s.id_nat() as usize);
            assert(o.roots_view()[ab.id_nat() as int] == ab.id_nat() as usize);
            assert(s.id_nat() != ab.id_nat());
        }
        // the absorbed root's payload is present (W2a) and names a live key
        // (W2b): production reads it with get_unchecked; here presence is a
        // theorem.
        let pay_ab = self.entries.payload_of(ab);
        proof {
            assert(self.entries == o.entries);
            assert(pay_ab == o.entries.payload_seq()[ab.id_nat() as int]);
            assert(pay_ab.wf());
            assert(pay_ab.get_spec() is Some);
        }
        let key_t = pay_ab.get();
        let key = key_t.to_index();
        proof {
            key_t.lemma_as_nat_is_id_nat();
            assert(key.as_nat() == o.key_of(ab.id_nat() as int));
            assert(ss_contains(o.reprs.sparse_view(), o.reprs.indices_view(),
                o.reprs.n_spec(), key.as_nat()));
            assert(self.reprs.contains_spec(key));
        }
        let data = self.reprs.get(key);
        proof {
            assert(data == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(),
                key.as_nat()));
        }
        // distinct rings, from W3a: were s and ab on one ring, they would
        // share a root, and they are distinct roots.
        let ghost cs = self.entries.locate(s.id_nat() as int).0;
        let ghost ps = self.entries.locate(s.id_nat() as int).1;
        let ghost ca = self.entries.locate(ab.id_nat() as int).0;
        let ghost pa = self.entries.locate(ab.id_nat() as int).1;
        proof {
            let orm = o.entries.model_view();
            assert(o.entries.in_some_ring(s.id_nat() as int));
            assert(o.entries.in_some_ring(ab.id_nat() as int));
            assert(0 <= cs < orm.len() && 0 <= ps < orm[cs].len()
                && orm[cs][ps] == s.id_nat() as usize);
            assert(0 <= ca < orm.len() && 0 <= pa < orm[ca].len()
                && orm[ca][pa] == ab.id_nat() as usize);
            if cs == ca {
                // same ring -> same root (W3a on the OLD state) -> s == ab.
                assert(o.roots_view()[orm[cs][ps] as int]
                    == o.roots_view()[orm[cs][pa] as int]);
                assert(false);
            }
        }
        let none_pay = Opt::<T>::none();
        self.entries.splice_absorb(s, ab, none_pay);
        self.reprs.remove(key);
        proof {
            // assemble the pointwise splice ensures into the update form.
            assert(self.entries.model_view() =~= o.entries.model_view()
                .update(cs, crate::circular_list::rotate(o.entries.model_view()[cs], ps + 1)
                    + crate::circular_list::rotate(o.entries.model_view()[ca], pa + 1))
                .update(ca, Seq::<usize>::empty()));
            assert(self.reprs.id_set() =~= o.reprs.id_set().remove(key.as_nat()));
            self.lemma_merge_wf(o, s, ab, key.as_nat(), none_pay, cs, ps, ca, pa);
        }
        Some(MergeInfo {
            survivor: s,
            absorbed: ab,
            absorbed_uses: data.use_list,
            absorbed_min_row: data.min_row,
            absorbed_atomic: data.atomic,
        })
    }


    /// Record that `parent_node` uses class `child_key` as a child, marking
    /// the class atomic (production's `add_use`). Refuses a dead key, an
    /// out-of-range parent id, or node exhaustion.
    pub fn add_use(&mut self, child_key: <T as DenseId>::Index, parent_node: T)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).roots_view() == old(self).roots_view(),
            final(self).num_classes_spec() == old(self).num_classes_spec(),
    {
        if !(parent_node.to_usize() < self.uf.len().as_usize()) {
            crate::guard::refuse("EClasses::add_use: parent node id out of range");
        }
        if !self.reprs.contains(child_key) {
            crate::guard::refuse("EClasses::add_use: class key is not live");
        }
        let ghost o = *old(self);
        let mut data = self.reprs.get(child_key);
        proof {
            crate::opt::lemma_id_nat_fits_usize(parent_node);
            assert(data == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(),
                child_key.as_nat()));
            assert(ss_contains(o.reprs.sparse_view(), o.reprs.indices_view(),
                o.reprs.n_spec(), child_key.as_nat()));
            // W4a: the class's list handle is allocated.
            assert(data.use_list.id_nat() < o.uses.model_view().len());
        }
        match self.uses.try_append(data.use_list, parent_node) {
            Ok(()) => (),
            Err(_) => crate::guard::refuse("EClasses::add_use: use-list node range exhausted"),
        }
        let ghost mid_um = self.uses.model_view();
        let ghost mid_un = self.uses.nodes_view();
        if !data.atomic {
            data.atomic = true;
            self.reprs.set(child_key, data);
        }
        proof {
            let n = o.n_spec();
            let li = data.use_list.id_nat() as int;
            let um = self.uses.model_view();
            let un = self.uses.nodes_view();
            let oum = o.uses.model_view();
            let oun = o.uses.nodes_view();
            let dense = self.reprs.dense_view();
            let sparse = self.reprs.sparse_view();
            let indices = self.reprs.indices_view();
            let live = self.reprs.n_spec();
            let odense = o.reprs.dense_view();
            let osparse = o.reprs.sparse_view();
            let oindices = o.reprs.indices_view();

            // reprs: at most one value changed, and only its atomic flag.
            assert(sparse == osparse && indices == oindices && live == o.reprs.n_spec());
            assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
                implies ss_contains(osparse, oindices, o.reprs.n_spec(), kk)
                    && ss_value(dense, sparse, kk).use_list
                        == ss_value(odense, osparse, kk).use_list
                    && ss_value(dense, sparse, kk).min_row
                        == ss_value(odense, osparse, kk).min_row by {
                if kk != child_key.as_nat() {
                    // positions are injective on the live region, so a
                    // different live key reads a different dense slot.
                    assert(osparse[kk as int].as_nat() != osparse[child_key.as_nat() as int].as_nat()) by {
                        if osparse[kk as int].as_nat() == osparse[child_key.as_nat() as int].as_nat() {
                            assert(oindices[osparse[kk as int].as_nat() as int].as_nat() == kk);
                        }
                    }
                }
            }
            assert forall|kk: nat| #[trigger] ss_contains(osparse, oindices, o.reprs.n_spec(), kk)
                implies ss_contains(sparse, indices, live, kk) by {}

            // uses: list li gained one entry naming parent_node; others same.
            o.uses.lemma_nodes_len_fits();
            <N as DenseId>::Index::lemma_max_nat_fits_usize();
            assert(oun.len() <= usize::MAX as nat);
            assert(um == oum.update(li, oum[li].push(oun.len() as usize)));
            assert(un.len() == oun.len() + 1);
            assert(un[oun.len() as int].payload == parent_node);

            assert forall|l: int, p: int|
                0 <= l < um.len() && 0 <= p < (#[trigger] um[l]).len()
                implies un[#[trigger] um[l][p] as int].payload.id_nat() < n by {
                if l == li && p == um[l].len() - 1 {
                    assert(um[l][p] == oun.len() as usize);
                } else {
                    assert(um[l][p] == oum[l][p]);
                    assert(oum[l][p] < oun.len());
                    assert(un[um[l][p] as int].payload == oun[oum[l][p] as int].payload);
                }
            }
            assert(eg_model_wf::<T, L, N>(
                self.entries.model_view(), self.entries.payload_seq(),
                self.uf.roots_view(), dense, sparse, indices, um, un,
                self.min_pool.view().len(), self.min_width as nat));
        }
    }

    /// Splice the absorbed class's use-list onto the survivor's after a
    /// merge (production's `splice_uses`; the rebuild loop iterates the
    /// absorbed list first). Refuses equal handles at runtime inside the
    /// arena; W4 ownership is untouched because list ids do not move.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(120)]
    pub fn splice_uses(&mut self, survivor_list: L, absorbed_list: L)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).roots_view() == old(self).roots_view(),
            final(self).num_classes_spec() == old(self).num_classes_spec(),
    {
        let ghost o = *old(self);
        self.uses.splice(survivor_list, absorbed_list);
        proof {
            let n = o.n_spec();
            let um = self.uses.model_view();
            let un = self.uses.nodes_view();
            let oum = o.uses.model_view();
            let oun = o.uses.nodes_view();
            o.uses.lemma_nodes_len_fits();
            <N as DenseId>::Index::lemma_max_nat_fits_usize();
            if survivor_list.id_nat() < oum.len() && absorbed_list.id_nat() < oum.len()
                && survivor_list.id_nat() != absorbed_list.id_nat()
            {
                let di = survivor_list.id_nat() as int;
                let si = absorbed_list.id_nat() as int;
                assert(um == oum.update(di, oum[di] + oum[si]).update(si, Seq::<usize>::empty()));
                lemma_splice_uses_w5::<T, N>(oum, um, oun, un, di, si, n);
                assert(eg_model_wf::<T, L, N>(
                    self.entries.model_view(), self.entries.payload_seq(),
                    self.uf.roots_view(), self.reprs.dense_view(),
                    self.reprs.sparse_view(), self.reprs.indices_view(),
                    um, un, self.min_pool.view().len(), self.min_width as nat));
            } else {
                // the arena refused (equal or out-of-range handles diverge
                // before mutation) or the ensures' conditional guards fired;
                // in every returning case the views are unchanged.
                assert(um == oum && un == oun);
                assert(eg_model_wf::<T, L, N>(
                    self.entries.model_view(), self.entries.payload_seq(),
                    self.uf.roots_view(), self.reprs.dense_view(),
                    self.reprs.sparse_view(), self.reprs.indices_view(),
                    um, un, self.min_pool.view().len(), self.min_width as nat));
            }
        }
    }

    /// Union-by-rank merge (production's `merge`, minus the proof-forest
    /// justification, which is postponed with the verified union-find's).
    pub fn merge(&mut self, a: T, b: T) -> (r: Option<MergeInfo<T, L>>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).min_width_spec() == old(self).min_width_spec(),
            a.id_nat() < old(self).n_spec() && b.id_nat() < old(self).n_spec() ==> {
                let ra = old(self).roots_view()[a.id_nat() as int] as nat;
                let rb = old(self).roots_view()[b.id_nat() as int] as nat;
                &&& (r is None <==> ra == rb)
                &&& (r is None ==> final(self).roots_view() == old(self).roots_view())
                &&& (r matches Some(mi) ==> {
                        &&& ((mi.survivor.id_nat() == ra && mi.absorbed.id_nat() == rb)
                            || (mi.survivor.id_nat() == rb && mi.absorbed.id_nat() == ra))
                        &&& ra != rb
                        &&& final(self).roots_view() == crate::union_find::merge_roots(
                                old(self).roots_view(), mi.survivor.id_nat(),
                                mi.absorbed.id_nat())
                        &&& final(self).num_classes_spec()
                            == old(self).num_classes_spec() - 1
                    })
            },
    {
        self.merge_with(a, b, false, false)
    }

    /// Directed merge: the survivor is `a`'s class when `prefer_a`
    /// (production's `merge_directed` policy hook; the parent-count policy
    /// computes the flag from use-list lengths).
    pub fn merge_directed(&mut self, a: T, b: T, prefer_a: bool)
        -> (r: Option<MergeInfo<T, L>>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            a.id_nat() < old(self).n_spec() && b.id_nat() < old(self).n_spec() ==> {
                let ra = old(self).roots_view()[a.id_nat() as int] as nat;
                let rb = old(self).roots_view()[b.id_nat() as int] as nat;
                &&& (r is None <==> ra == rb)
                &&& (r matches Some(mi) ==> {
                        &&& mi.survivor.id_nat() == (if prefer_a { ra } else { rb })
                        &&& mi.absorbed.id_nat() == (if prefer_a { rb } else { ra })
                        &&& final(self).roots_view() == crate::union_find::merge_roots(
                                old(self).roots_view(), mi.survivor.id_nat(),
                                mi.absorbed.id_nat())
                    })
            },
    {
        self.merge_with(a, b, true, prefer_a)
    }
}

} // verus!
