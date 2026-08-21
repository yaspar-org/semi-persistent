// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Verified equivalence-class aggregate: the e-graph's class layer with
//! W1-W7 as its machine-checked `wf()`.
//!
//! The module composes five verified structures: `CircularList` ring,
//! `SparseSet` class-key set, `UnionFind`, `ListArena` use-lists, `Vec`
//! min-monomial pool. Their agreement is `eg_model_wf`, a predicate over the
//! components' specification views. This table is the authoritative
//! W-invariant numbering; every other document cites it.
//!
//!   - W1: the union-find's ghost root map and its measure (inside
//!     `UnionFind::wf`);
//!   - W2: `x` is a union-find root iff ring cell `x` carries a present
//!     payload, and the live class keys are exactly the root payloads
//!     (stated as an iff, with injectivity across roots);
//!   - W3: two nodes share a ring iff they share a root, stated over model
//!     coordinates in both directions (same ring implies same root, same
//!     root implies same ring), which is what discharges `splice_absorb`'s
//!     distinct-rings precondition inside `merge`;
//!   - W4: live classes own pairwise-distinct, allocated use-lists;
//!   - W5: every use-list entry is an allocated node id (freshness across a
//!     merge is the consumer's dirty-set discipline, deliberately not
//!     claimed here);
//!   - W6: the pool is whole rows of `min_width`, live row numbers are
//!     allocated and pairwise distinct;
//!   - W7: the size stored in a class payload equals its ring's length,
//!     stated at the ring member that is the class's root. The archive
//!     invariant (`eg_archive_agrees`) asserts `eg_model_wf` per frame, so
//!     W7 holds in every archived mark and `restore` preserves it.
//!
//! Terminology: a "class key" is the `SparseSet` id a root's ring payload
//! carries; "live" is the key's state while its class exists. The prose
//! word "frame" and the API word "snapshot" (`*_snapshots_view`) name the
//! same thing: one archived mark level. The key stored in a ring payload is
//! `Opt<T::Index>`, an index-typed cell, 12 bytes at a bit-stealing family;
//! the 16-byte class payload (`ClassData`) is pinned by the consumer's
//! compile-time asserts. This kernel is the production e-graph class layer:
//! `egraph::EClasses` and `egraph::UnionFind` are type aliases of it.

use vstd::prelude::*;

use crate::circular_list::{CircularList, CircularListNode, CircularListToken};
use crate::index_like::IndexLike;
use crate::inline_store::InlineStore;
use crate::list::{ListArena, ListArenaToken, ListNode};
use crate::opt::{DenseId, Opt};
use crate::parallel_store::ParallelStore;
use crate::sparse_set::{SparseSet, SparseSetToken};
use crate::tagged::Tagged;
use crate::union_find::{UnionFind, UnionFindToken};
use crate::vec::{ShrinkPolicy, Vec as SpVec, VecToken};

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
    /// Member-node count of the class, in the node-id family's index type so
    /// the width follows the configuration (the `min_row` pattern). Set to 1
    /// at `add_singleton`, folded survivor += absorbed at `merge_with`,
    /// carried unchanged by every other payload write. Feeds the
    /// `--union-by size`/`sum` survivor policy.
    pub size: <T as DenseId>::Index,
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
        ClassData {
            use_list: L::default(),
            min_row: None,
            atomic: false,
            size: <T::Index as IndexLike>::min(),
        }
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
    pub size: I,
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
            size: r.size,
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
        ClassDataRepr {
            a: self.use_list.into_repr(),
            row,
            present,
            atomic: self.atomic,
            size: self.size,
        }
    }
    fn from_repr(r: &Self::Repr) -> (v: Self) {
        ClassData {
            use_list: L::from_repr(&r.a),
            min_row: if r.present { Some(r.row) } else { None },
            atomic: r.atomic,
            size: r.size,
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

/// The value stored for the live class key `id` (dense slot through the indirection).
pub open(crate) spec fn ss_value<V, Idx: IndexLike>(
    dense: Seq<V>, sparse: Seq<Idx>, id: nat,
) -> V {
    dense[sparse[id as int].as_nat() as int]
}

/// W2-W7 over the components' views (the module header holds the invariant
/// table). `ring_model`/`payloads` are the
/// `CircularList`'s ghost rings and payload cells; `roots` is the
/// `UnionFind`'s ghost root map; the three `reprs_*` sequences are the
/// `SparseSet` columns (`live` its element count); `uses_model`/`uses_nodes`
/// are the `ListArena`'s ghost lists and node cells; `pool_len`/`min_width`
/// the pool geometry.
pub open(crate) spec fn eg_model_wf<T: DenseId, L: DenseId, N: DenseId + Tagged>(
    ring_model: Seq<Seq<usize>>,
    payloads: Seq<Opt<<T as DenseId>::Index>>,
    roots: Seq<usize>,
    reprs_dense: Seq<ClassData<L, T>>,
    reprs_sparse: Seq<<T as DenseId>::Index>,
    reprs_indices: Seq<<T as DenseId>::Index>,
    uses_model: Seq<Seq<usize>>,
    uses_nodes: Seq<ListNode<T, N>>,
    pool: Seq<Opt<T>>,
    min_width: nat,
) -> bool {
    let n = payloads.len();
    let live = reprs_dense.len();
    let pool_len = pool.len();
    &&& roots.len() == n
    // the repr capacity never outgrows the node count (one live class key per
    // root, keys minted at most one per node)
    &&& reprs_sparse.len() <= n
    // payload cells decode (Opt well-formedness)
    &&& (forall|x: int| 0 <= x < n ==> (#[trigger] payloads[x]).wf())
    // W2a: a root iff a present payload
    &&& (forall|x: int| 0 <= x < n
            ==> ((#[trigger] roots[x]) == x as usize <==> payloads[x].get_spec() is Some))
    // W2b (one direction of the key bijection): a root's key is live, and its
    // stored data names an allocated use-list
    &&& (forall|x: int| 0 <= x < n && (#[trigger] roots[x]) == x as usize
            ==> ss_contains(reprs_sparse, reprs_indices, live,
                    payloads[x].get_spec()->Some_0.as_nat()))
    // W2c: keys are injective across roots
    &&& (forall|x: int, y: int|
            0 <= x < n && 0 <= y < n && x != y
                && (#[trigger] roots[x]) == x as usize && (#[trigger] roots[y]) == y as usize
                ==> payloads[x].get_spec()->Some_0.as_nat()
                    != payloads[y].get_spec()->Some_0.as_nat())
    // W2d (the other direction): every live class key is some root's key
    &&& (forall|id: nat| #[trigger] ss_contains(reprs_sparse, reprs_indices, live, id)
            ==> exists|x: int| 0 <= x < n && roots[x] == x as usize
                && (#[trigger] payloads[x]).get_spec()->Some_0.as_nat() == id)
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
    // W7: the stored class size is the ring length. Stated at the ring member
    // that is the class's root (every class's root node sits on its own ring),
    // whose payload carries the live class key; the key's ClassData.size counts
    // exactly the ring's members. This is what makes `class_size` a verified
    // O(1) read of the member count (the `--union-by size` policy input).
    &&& (forall|c: int, p: int|
            0 <= c < ring_model.len() && 0 <= p < ring_model[c].len()
                && roots[(#[trigger] ring_model[c][p]) as int] == ring_model[c][p]
                ==> ss_value(reprs_dense, reprs_sparse,
                        payloads[ring_model[c][p] as int].get_spec()->Some_0.as_nat())
                    .size.as_nat() == ring_model[c].len())
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
    // pool cells decode (Opt well-formedness; the cells are data, W6 is
    // geometry, but a read must round-trip)
    &&& (forall|i: int| 0 <= i < pool.len() ==> (#[trigger] pool[i]).wf())
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


/// The payload column of a ring snapshot.
pub open(crate) spec fn ring_payloads<T: DenseId>(
    cells: Seq<CircularListNode<Opt<<T as DenseId>::Index>, T>>,
) -> Seq<Opt<<T as DenseId>::Index>> {
    Seq::new(cells.len(), |i: int| cells[i].payload)
}

/// The aggregate archive: each frame's component snapshots jointly
/// satisfy the invariant, the stacks move in lockstep, the archived pool
/// lengths are monotone (the pool only grows between marks), and each
/// archived repr triple is a valid sparse-set state. This lets the aggregate's
/// restore discharge `SparseSet::restore`'s snapshot-wf precondition from its
/// own `wf`.
/// Opaque for the standard reason; only mark/restore (and `set_min_width`,
/// which re-checks W6 vacuity over empty archived pools) reveal it.
#[verifier::opaque]
pub open(crate) spec fn eg_archive_agrees<T: DenseId, L: DenseId, N: DenseId + Tagged>(
    ring_models: Seq<Seq<Seq<usize>>>,
    ring_cells: Seq<Seq<CircularListNode<Opt<<T as DenseId>::Index>, T>>>,
    roots_arch: Seq<Seq<usize>>,
    dense_snaps: Seq<Seq<ClassData<L, T>>>,
    sparse_snaps: Seq<Seq<<T as DenseId>::Index>>,
    indices_snaps: Seq<Seq<<T as DenseId>::Index>>,
    uses_models: Seq<Seq<Seq<usize>>>,
    uses_nodes_snaps: Seq<Seq<ListNode<T, N>>>,
    pool_snaps: Seq<Seq<Opt<T>>>,
    min_width: nat,
) -> bool {
    let f = ring_models.len();
    &&& ring_cells.len() == f
    &&& roots_arch.len() == f
    &&& dense_snaps.len() == f
    &&& sparse_snaps.len() == f
    &&& indices_snaps.len() == f
    &&& uses_models.len() == f
    &&& uses_nodes_snaps.len() == f
    &&& pool_snaps.len() == f
    &&& (forall|k: int| 0 <= k < f ==> eg_model_wf::<T, L, N>(
            ring_models[k], ring_payloads(#[trigger] ring_cells[k]), roots_arch[k],
            dense_snaps[k], sparse_snaps[k], indices_snaps[k],
            uses_models[k], uses_nodes_snaps[k], pool_snaps[k], min_width))
    &&& (forall|k: int| 0 <= k < f ==> crate::sparse_set::sparse_set_snap_wf(
            #[trigger] dense_snaps[k], sparse_snaps[k], indices_snaps[k]))
    &&& (forall|k1: int, k2: int| 0 <= k1 <= k2 < f
            ==> (#[trigger] pool_snaps[k1]).len() <= (#[trigger] pool_snaps[k2]).len())
}

// ---------------------------------------------------------------------------
// EClasses
// ---------------------------------------------------------------------------

/// Verified equivalence classes: ring + union-find + repr set + use-lists +
/// min-monomial pool, with the agreement clauses as `wf`.
pub struct EClasses<T, L, N, J, const TRACK: bool, const PROOFS: bool>
where
    T: DenseId,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
    J: Tagged + Copy + core::default::Default,
{
    /// The class ring; each cell carries the class's key (as a
    /// node-typed dense id) while the class is live, absent once absorbed.
    pub(crate) entries: CircularList<Opt<<T as DenseId>::Index>, T, TRACK>,
    /// Per-class data, keyed by repr id.
    pub(crate) reprs: SparseSet<ClassData<L, T>, <T as DenseId>::Index,
        InlineStore<ClassData<L, T>, <T as DenseId>::Index>, TRACK>,
    /// Verified canonical-representative lookup.
    pub(crate) uf: UnionFind<T, J, TRACK, PROOFS>,
    /// Per-class parent lists.
    pub(crate) uses: ListArena<T, L, N, TRACK>,
    /// Min-monomial pool: flat rows of `min_width` columns. `ParallelStore`,
    /// as production's `VecP`: `Opt` owns its niche bit, so it cannot sit in
    /// a bit-stealing `InlineStore`.
    pub(crate) min_pool: SpVec<Opt<T>, usize, ParallelStore<Opt<T>, usize>, TRACK>,
    /// Fixed row width; 0 until `set_min_width`.
    pub(crate) min_width: usize,
}

impl<T, L, N, J, const TRACK: bool, const PROOFS: bool> EClasses<T, L, N, J, TRACK, PROOFS>
where
    T: DenseId,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
    J: Tagged + Copy + core::default::Default,
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

    /// The class key stored in `x`'s ring cell (meaningful when `x` is a root).
    pub open(crate) spec fn key_of(&self, x: int) -> nat {
        self.entries.payload_seq()[x].get_spec()->Some_0.as_nat()
    }

    /// The class data of live class key `id` (spec).
    pub open(crate) spec fn class_data_spec(&self, id: nat) -> ClassData<L, T> {
        ss_value(self.reprs.dense_view(), self.reprs.sparse_view(), id)
    }

    /// Key liveness (spec counterpart of the repr set's membership).
    pub open(crate) spec fn contains_key_spec(&self, key: <T as DenseId>::Index) -> bool {
        self.reprs.contains_spec(key)
    }

    /// The ring component (spec ref, for iterator ensures).
    pub open(crate) spec fn entries_ref(&self)
        -> &CircularList<Opt<<T as DenseId>::Index>, T, TRACK> {
        &self.entries
    }

    /// The use-list arena (spec ref, for iterator ensures).
    pub open(crate) spec fn uses_ref(&self) -> &ListArena<T, L, N, TRACK> {
        &self.uses
    }

    /// The class-ring walk of `start` (spec counterpart of `iter_class`'s output).
    pub open(crate) spec fn class_seq(&self, start: int) -> Seq<usize> {
        self.entries.class_seq(start)
    }

    /// The archived root maps, one per mark (spec).
    pub open(crate) spec fn roots_archive_view(&self) -> Seq<Seq<usize>> {
        self.uf.roots_snapshots_view()
    }

    /// Mark depth (spec): the number of live frames.
    pub open(crate) spec fn depth_spec(&self) -> nat {
        self.min_pool.snapshots_view().len()
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
        &&& eg_model_wf::<T, L, N>(
                self.entries.model_view(),
                self.entries.payload_seq(),
                self.uf.roots_view(),
                self.reprs.dense_view(),
                self.reprs.sparse_view(),
                self.reprs.indices_view(),
                self.uses.model_view(),
                self.uses.nodes_view(),
                self.min_pool.view(),
                self.min_width as nat)
        // Joint archive over the component snapshot stacks.
        &&& eg_archive_agrees::<T, L, N>(
                self.entries.model_snapshots_view(),
                self.entries.entries_snapshots_view(),
                self.uf.roots_snapshots_view(),
                self.reprs.dense_snapshots_view(),
                self.reprs.sparse_snapshots_view(),
                self.reprs.indices_snapshots_view(),
                self.uses.model_snapshots_view(),
                self.uses.nodes_snapshots_view(),
                self.min_pool.snapshots_view(),
                self.min_width as nat)
        // archived pool lengths never exceed the live pool (outside the
        // opaque predicate: the live length changes on row allocation, and
        // an opaque argument change would not transfer by congruence).
        &&& (forall|k: int| 0 <= k < self.min_pool.snapshots_view().len()
                ==> (#[trigger] self.min_pool.snapshots_view()[k]).len()
                    <= self.min_pool.view().len())
    }

    pub fn new() -> (e: Self)
        ensures e.wf(), e.n_spec() == 0, e.num_classes_spec() == 0,
            e.min_width_spec() == 0,
    {
        let e = EClasses {
            entries: CircularList::new(),
            reprs: SparseSet::new_inline(),
            uf: UnionFind::new(),
            uses: ListArena::new(),
            min_pool: SpVec::<Opt<T>, usize, ParallelStore<Opt<T>, usize>, TRACK>::new(),
            min_width: 0,
        };
        proof { reveal(eg_archive_agrees); }
        e
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

    /// The class key of node `idx`'s ring cell, `None` once its class was
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
        p.to_option()
    }

    /// Allocate `id` as its own singleton class, returning its class key
    /// (production's surface: the caller supplies the next dense id; the
    /// sequential contract refuses with production's message, which
    /// historically came from `UnionFind::make_set`).
    pub fn add_singleton(&mut self, id: T) -> (key: <T as DenseId>::Index)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            id.id_nat() == old(self).n_spec() ==> {
                &&& final(self).n_spec() == old(self).n_spec() + 1
                &&& final(self).num_classes_spec() == old(self).num_classes_spec() + 1
                &&& final(self).roots_view()
                    == old(self).roots_view().push(old(self).n_spec() as usize)
                &&& final(self).key_of(id.id_nat() as int) == key.as_nat()
            },
    {
        if !(id.to_usize() == self.uf.len().as_usize()) {
            crate::guard::refuse("UnionFind::make_set: id must be sequential");
        }
        let (minted, key) = self.try_add_singleton();
        proof {
            if id.id_nat() == old(self).n_spec() {
                T::lemma_id_injective(minted, id);
            }
        }
        key
    }

    /// Allocate the NEXT fresh node as its own singleton class; returns the
    /// minted node id and its class key. Total-with-documented-panic at the
    /// capacity ceilings (production allocates through `expect` at the same
    /// points).
    pub fn try_add_singleton(&mut self) -> (r: (T, <T as DenseId>::Index))
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
        let one = match <T::Index as IndexLike>::try_from_usize(1) {
            Some(o) => o,
            None => crate::guard::refuse("EClasses::add_singleton: index width below 1"),
        };
        let key = match self.reprs.try_add(ClassData {
            use_list: list_id, min_row: None, atomic: false, size: one,
        }) {
            Ok(k) => k,
            Err(_) => crate::guard::refuse("EClasses::add_singleton: repr capacity exhausted"),
        };
        proof {
            crate::opt::lemma_id_nat_fits_usize(id);
            id.lemma_id_nat_bounded();
            assert(key.as_nat() <= old(self).reprs.cap_spec());
            assert(old(self).reprs.cap_spec() <= n0);
        }
        // 4. ring cell: the key word is the payload, as production stores it.
        let opt_key = Opt::some(key);
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
            assert(opt_key.get_spec() == Some(key));
            assert(rm == orm.push(seq![n0 as usize]));
            assert(roots == oroots.push(n0 as usize));
            assert(um == oum.push(Seq::<usize>::empty()));
            assert(un == o.uses.nodes_view());
            assert(pay.len() == n1);
            crate::opt::lemma_id_nat_fits_usize(id);

            // the new key is live, with the fresh ClassData
            assert(self.reprs.contains_spec(key));
            assert(ss_contains(sparse, indices, live, kn));
            assert(ss_value(dense, sparse, kn)
                == ClassData::<L, T> { use_list: list_id, min_row: None, atomic: false, size: one });

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
                    pay[x].get_spec()->Some_0.as_nat()) by {
                if x < n0 {
                    assert(ss_contains(osparse, oindices, olive,
                        opay[x].get_spec()->Some_0.as_nat()));
                    assert(pay[x] == opay[x]);
                }
            }
            // --- W2c
            assert forall|x: int, y: int|
                0 <= x < n1 && 0 <= y < n1 && x != y
                    && (#[trigger] roots[x]) == x as usize
                    && (#[trigger] roots[y]) == y as usize
                implies pay[x].get_spec()->Some_0.as_nat()
                    != pay[y].get_spec()->Some_0.as_nat() by {
                if x < n0 && y < n0 {
                    assert(pay[x] == opay[x] && pay[y] == opay[y]);
                } else if x == n0 as int && y < n0 {
                    // the fresh key differs from every old root's key, which
                    // is live in the OLD set.
                    assert(pay[y] == opay[y]);
                    assert(ss_contains(osparse, oindices, olive,
                        opay[y].get_spec()->Some_0.as_nat()));
                } else if y == n0 as int && x < n0 {
                    assert(pay[x] == opay[x]);
                    assert(ss_contains(osparse, oindices, olive,
                        opay[x].get_spec()->Some_0.as_nat()));
                }
            }
            // --- W2d
            assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
                implies exists|x: int| 0 <= x < n1 && roots[x] == x as usize
                    && (#[trigger] pay[x]).get_spec()->Some_0.as_nat() == kk by {
                if kk == kn {
                    assert(roots[n0 as int] == n0 as usize);
                    assert(pay[n0 as int].get_spec()->Some_0.as_nat() == kk);
                } else {
                    assert(ss_contains(osparse, oindices, olive, kk));
                    let x = choose|x: int| 0 <= x < n0 && oroots[x] == x as usize
                        && (#[trigger] opay[x]).get_spec()->Some_0.as_nat() == kk;
                    assert(roots[x] == x as usize);
                    assert(pay[x].get_spec()->Some_0.as_nat() == kk);
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
                um, un, self.min_pool.view(), self.min_width as nat));
            // the archive transfers by congruence: every snapshot stack is
            // framed by the component contracts.
            assert(eg_archive_agrees::<T, L, N>(
                self.entries.model_snapshots_view(),
                self.entries.entries_snapshots_view(),
                self.uf.roots_snapshots_view(),
                self.reprs.dense_snapshots_view(),
                self.reprs.sparse_snapshots_view(),
                self.reprs.indices_snapshots_view(),
                self.uses.model_snapshots_view(),
                self.uses.nodes_snapshots_view(),
                self.min_pool.snapshots_view(),
                self.min_width as nat))
            by {
                assert(self.entries.model_snapshots_view()
                    == o.entries.model_snapshots_view());
                assert(self.entries.entries_snapshots_view()
                    == o.entries.entries_snapshots_view());
                assert(self.uf.roots_snapshots_view() == o.uf.roots_snapshots_view());
                assert(self.reprs.dense_snapshots_view()
                    == o.reprs.dense_snapshots_view());
                assert(self.reprs.sparse_snapshots_view()
                    == o.reprs.sparse_snapshots_view());
                assert(self.reprs.indices_snapshots_view()
                    == o.reprs.indices_snapshots_view());
                assert(self.uses.model_snapshots_view()
                    == o.uses.model_snapshots_view());
                assert(self.uses.nodes_snapshots_view()
                    == o.uses.nodes_snapshots_view());
                assert(self.min_pool.snapshots_view() == o.min_pool.snapshots_view());
            }
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

impl<T, L, N, J, const TRACK: bool, const PROOFS: bool> EClasses<T, L, N, J, TRACK, PROOFS>
where
    T: DenseId,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
    J: Tagged + Copy + core::default::Default,
{

    /// Re-establishes `eg_model_wf` after a merge's three mutations (union,
    /// ring splice with payload clear, repr removal). Extracted for the same
    /// reason as `lemma_splice_disjoint` (list.rs): proved inline, the ring
    /// and root quantifiers e-match against both states' full `wf`.
    proof fn lemma_merge_wf(&self, o: Self, s: T, ab: T, key_ab: nat, skey: nat,
        ab_pay: Opt<<T as DenseId>::Index>, cs: int, ps: int, ca: int, pa: int)
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
            skey == o.key_of(s.id_nat() as int),
            ss_contains(o.reprs.sparse_view(), o.reprs.indices_view(),
                o.reprs.n_spec(), skey),
            skey != key_ab,
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
                && k.as_nat() != key_ab && k.as_nat() != skey
                ==> self.reprs.contains_spec(k)
                    && ss_value(self.reprs.dense_view(), self.reprs.sparse_view(),
                            k.as_nat())
                        == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(),
                            k.as_nat()),
            // the survivor's key stays live with only its size folded:
            // new size = old survivor size + absorbed size.
            forall|k: <T as DenseId>::Index| #[trigger] o.reprs.contains_spec(k)
                && k.as_nat() == skey
                ==> self.reprs.contains_spec(k),
            ss_value(self.reprs.dense_view(), self.reprs.sparse_view(), skey).use_list
                == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(), skey).use_list,
            ss_value(self.reprs.dense_view(), self.reprs.sparse_view(), skey).min_row
                == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(), skey).min_row,
            ss_value(self.reprs.dense_view(), self.reprs.sparse_view(), skey).atomic
                == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(), skey).atomic,
            ss_value(self.reprs.dense_view(), self.reprs.sparse_view(), skey)
                .size.as_nat()
                == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(), skey)
                    .size.as_nat()
                    + ss_value(o.reprs.dense_view(), o.reprs.sparse_view(), key_ab)
                        .size.as_nat(),
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
                self.min_pool.view(), self.min_width as nat),
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
                && 0 <= j < orm[c0].len()
                && (#[trigger] orm[c0][j]) == #[trigger] merged[q] by {
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

        // survivors + dead-stay-dead, in the nat form the clauses use: values
        // carry field-for-field, fully except the survivor key's folded size.
        assert forall|kk: nat| #[trigger] ss_contains(osparse, oindices, olive, kk)
            && kk != key_ab
            implies ss_contains(sparse, indices, live, kk)
                && ss_value(dense, sparse, kk).use_list
                    == ss_value(odense, osparse, kk).use_list
                && ss_value(dense, sparse, kk).min_row
                    == ss_value(odense, osparse, kk).min_row
                && (kk != skey ==> ss_value(dense, sparse, kk)
                    == ss_value(odense, osparse, kk)) by {
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
                pay[x].get_spec()->Some_0.as_nat()) by {
            assert(x != abn as int);
            assert(pay[x] == opay[x]);
            assert(oroots[x] == x as usize);
            assert(ss_contains(osparse, oindices, olive,
                opay[x].get_spec()->Some_0.as_nat()));
            // x's key is not ab's key: W2c injectivity in the old state.
            assert(opay[x].get_spec()->Some_0.as_nat() != key_ab);
        }
        // --- W2c
        assert forall|x: int, y: int|
            0 <= x < n && 0 <= y < n && x != y
                && (#[trigger] roots[x]) == x as usize
                && (#[trigger] roots[y]) == y as usize
            implies pay[x].get_spec()->Some_0.as_nat()
                != pay[y].get_spec()->Some_0.as_nat() by {
            assert(x != abn as int && y != abn as int);
            assert(pay[x] == opay[x] && pay[y] == opay[y]);
            assert(oroots[x] == x as usize && oroots[y] == y as usize);
        }
        // --- W2d
        assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
            implies exists|x: int| 0 <= x < n && roots[x] == x as usize
                && (#[trigger] pay[x]).get_spec()->Some_0.as_nat() == kk by {
            assert(ss_contains(osparse, oindices, olive, kk) && kk != key_ab);
            let x = choose|x: int| 0 <= x < n && oroots[x] == x as usize
                && (#[trigger] opay[x]).get_spec()->Some_0.as_nat() == kk;
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
                    && 0 <= j < orm[c0].len() && (#[trigger] orm[c0][j]) == merged[p];
                let (c2, j2) = choose|c0: int, j: int| (c0 == cs || c0 == ca)
                    && 0 <= j < orm[c0].len() && (#[trigger] orm[c0][j]) == merged[q];
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
            assert(ss_value(dense, sparse, kk).use_list
                == ss_value(odense, osparse, kk).use_list);
        }
        assert forall|k1: nat, k2: nat|
            ss_contains(sparse, indices, live, k1)
                && ss_contains(sparse, indices, live, k2) && k1 != k2
            implies #[trigger] ss_value(dense, sparse, k1).use_list.id_nat()
                != #[trigger] ss_value(dense, sparse, k2).use_list.id_nat() by {
            assert(ss_contains(osparse, oindices, olive, k1) && k1 != key_ab);
            assert(ss_contains(osparse, oindices, olive, k2) && k2 != key_ab);
            assert(ss_value(dense, sparse, k1).use_list
                == ss_value(odense, osparse, k1).use_list);
            assert(ss_value(dense, sparse, k2).use_list
                == ss_value(odense, osparse, k2).use_list);
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
            assert(ss_value(dense, sparse, kk).min_row
                == ss_value(odense, osparse, kk).min_row);
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
            assert(ss_value(dense, sparse, k1).min_row
                == ss_value(odense, osparse, k1).min_row);
            assert(ss_value(dense, sparse, k2).min_row
                == ss_value(odense, osparse, k2).min_row);
        }
        // --- W7: the stored class size is the ring length.
        // s sits on the merged ring: rotate(orm[cs], ps+1)[lcs-1] == orm[cs][ps].
        let lcs = orm[cs].len() as int;
        assert(merged[lcs - 1] == orm[cs][ps]);
        assert forall|c: int, p: int|
            0 <= c < rm.len() && 0 <= p < rm[c].len()
                && roots[(#[trigger] rm[c][p]) as int] == rm[c][p]
            implies ss_value(dense, sparse,
                    pay[rm[c][p] as int].get_spec()->Some_0.as_nat())
                .size.as_nat() == rm[c].len() by {
            let m = rm[c][p];
            if c == ca {
                assert(rm[ca].len() == 0);
            } else if c == cs {
                // every merged member roots to s, so the root member IS s.
                assert(roots[m as int] == su);
                assert(m == su);
                assert(pay[m as int] == opay[m as int]);
                assert(pay[m as int].get_spec()->Some_0.as_nat() == skey);
                // o's W7 at the two old rings gives the two old sizes.
                assert(oroots[orm[cs][ps] as int] == orm[cs][ps]);
                assert(ss_value(odense, osparse, skey).size.as_nat()
                    == orm[cs].len());
                assert(oroots[orm[ca][pa] as int] == orm[ca][pa]);
                assert(ss_value(odense, osparse, key_ab).size.as_nat()
                    == orm[ca].len());
                assert(merged.len() == orm[cs].len() + orm[ca].len());
                assert(ss_value(dense, sparse, skey).size.as_nat()
                    == orm[cs].len() + orm[ca].len());
            } else {
                assert(rm[c] == orm[c]);
                // the root member kept its old root (it is neither s's nor
                // ab's class member: those all live on cs/ca in o).
                assert(oroots[m as int] != abu && oroots[m as int] != su);
                assert(roots[m as int] == oroots[m as int]);
                assert(oroots[m as int] == m);
                assert(m != abu && m != su);
                assert(pay[m as int] == opay[m as int]);
                let kk = opay[m as int].get_spec()->Some_0.as_nat();
                assert(ss_contains(osparse, oindices, olive, kk));
                assert(ss_value(odense, osparse, kk).size.as_nat() == orm[c].len());
                // kk is neither the absorbed key nor the survivor key (W2c on
                // o: distinct roots carry distinct keys).
                assert(kk != key_ab);
                assert(kk != skey);
                assert(ss_value(dense, sparse, kk) == ss_value(odense, osparse, kk));
            }
        }
        assert(eg_model_wf::<T, L, N>(rm, pay, roots, dense, sparse, indices,
            um, un, self.min_pool.view(), self.min_width as nat));
    }

    /// Merge the classes of `a` and `b`: union-find link, ring splice with
    /// the absorbed payload cleared, repr removal. `None` iff already one
    /// class. The core of `merge` and `merge_directed`; the distinct-rings
    /// precondition of `splice_absorb` is discharged here from W2 + W3.
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
            self.uf.union_directed_core(a, b, prefer_a)
        } else {
            self.uf.union_core(a, b)
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
        // the absorbed root's payload is present (W2a) and names a live class key
        // (W2b): production reads it with get_unchecked; here presence is a
        // theorem.
        let pay_ab = self.entries.payload_of(ab);
        proof {
            assert(self.entries == o.entries);
            assert(pay_ab == o.entries.payload_seq()[ab.id_nat() as int]);
            assert(pay_ab.wf());
            assert(pay_ab.get_spec() is Some);
        }
        let key = pay_ab.get();
        proof {
            assert(key.as_nat() == o.key_of(ab.id_nat() as int));
            assert(ss_contains(o.reprs.sparse_view(), o.reprs.indices_view(),
                o.reprs.n_spec(), key.as_nat()));
            assert(self.reprs.contains_spec(key));
        }
        let data = self.reprs.get_live(key);
        proof {
            assert(data == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(),
                key.as_nat()));
        }
        // Survivor size fold, BEFORE the splice so the wf lemma sees the final
        // payload: survivor.size += absorbed.size, tied to the merged ring
        // length by W7. The survivor root's payload is present (W2a) and
        // names a live class key (W2b), the same theorem as for `ab` above.
        let pay_s = self.entries.payload_of(s);
        proof {
            assert(pay_s == o.entries.payload_seq()[s.id_nat() as int]);
            assert(pay_s.wf());
            assert(pay_s.get_spec() is Some);
        }
        let skey = pay_s.get();
        proof {
            assert(skey.as_nat() == o.key_of(s.id_nat() as int));
            assert(ss_contains(o.reprs.sparse_view(), o.reprs.indices_view(),
                o.reprs.n_spec(), skey.as_nat()));
            assert(self.reprs.contains_spec(skey));
            // distinct roots carry distinct keys (W2c).
            assert(skey.as_nat() != key.as_nat());
        }
        let mut sdata = self.reprs.get_live(skey);
        proof {
            assert(sdata == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(),
                skey.as_nat()));
        }
        sdata.size = match crate::index_like::checked_add(sdata.size, data.size) {
            Some(v) => v,
            None => crate::guard::refuse(
                "EClasses::merge: class size overflows the index width"),
        };
        self.reprs.set_live(skey, sdata);
        let ghost m1 = *self;
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
        let none_pay = Opt::<<T as DenseId>::Index>::none();
        self.entries.splice_absorb(s, ab, none_pay);
        self.reprs.remove(key);
        proof {
            // assemble the pointwise splice ensures into the update form.
            assert(self.entries.model_view() =~= o.entries.model_view()
                .update(cs, crate::circular_list::rotate(o.entries.model_view()[cs], ps + 1)
                    + crate::circular_list::rotate(o.entries.model_view()[ca], pa + 1))
                .update(ca, Seq::<usize>::empty()));
            assert(self.reprs.id_set() =~= o.reprs.id_set().remove(key.as_nat()));
            // set_live changed only skey's dense slot: distinct live class keys sit
            // at distinct dense positions, so every other survivor's value is
            // o's, and skey's is `sdata` (o's value with the size folded).
            assert forall|k: <T as DenseId>::Index| #[trigger] o.reprs.contains_spec(k)
                && k.as_nat() != key.as_nat() && k.as_nat() != skey.as_nat()
                implies self.reprs.contains_spec(k)
                    && ss_value(self.reprs.dense_view(), self.reprs.sparse_view(),
                            k.as_nat())
                        == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(),
                            k.as_nat()) by {
                assert(m1.reprs.contains_spec(k));
                assert(o.reprs.sparse_view()[k.as_nat() as int].as_nat()
                    != o.reprs.sparse_view()[skey.as_nat() as int].as_nat()) by {
                    if o.reprs.sparse_view()[k.as_nat() as int].as_nat()
                        == o.reprs.sparse_view()[skey.as_nat() as int].as_nat() {
                        assert(o.reprs.indices_view()[o.reprs.sparse_view()
                            [k.as_nat() as int].as_nat() as int].as_nat() == k.as_nat());
                    }
                }
                assert(ss_value(m1.reprs.dense_view(), m1.reprs.sparse_view(),
                        k.as_nat())
                    == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(),
                        k.as_nat()));
            }
            assert(m1.reprs.contains_spec(skey));
            assert(ss_contains(m1.reprs.sparse_view(), m1.reprs.indices_view(),
                m1.reprs.n_spec(), skey.as_nat()));
            assert(ss_value(m1.reprs.dense_view(), m1.reprs.sparse_view(),
                skey.as_nat()) == sdata);
            assert(self.reprs.contains_spec(skey));
            assert(ss_value(self.reprs.dense_view(), self.reprs.sparse_view(),
                skey.as_nat()) == sdata);
            self.lemma_merge_wf(o, s, ab, key.as_nat(), skey.as_nat(),
                none_pay, cs, ps, ca, pa);
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
    ///
    /// Prepends. W5 constrains the use-list's contents, not its order, and no
    /// consumer reads the order: the rebuild sweep recanonizes each parent
    /// independently, and critical-pair partner discovery sorts and dedups what
    /// it collects. Prepending touches one memory location (the list head)
    /// where appending touches two (the head and the old tail node).
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
        let mut data = self.reprs.get_live(child_key);
        proof {
            crate::opt::lemma_id_nat_fits_usize(parent_node);
            assert(data == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(),
                child_key.as_nat()));
            assert(ss_contains(o.reprs.sparse_view(), o.reprs.indices_view(),
                o.reprs.n_spec(), child_key.as_nat()));
            // W4a: the class's list handle is allocated.
            assert(data.use_list.id_nat() < o.uses.model_view().len());
        }
        match self.uses.try_prepend(data.use_list, parent_node) {
            Ok(()) => (),
            Err(_) => crate::guard::refuse("EClasses::add_use: use-list node range exhausted"),
        }
        let ghost mid_um = self.uses.model_view();
        let ghost mid_un = self.uses.nodes_view();
        if !data.atomic {
            data.atomic = true;
            self.reprs.set_live(child_key, data);
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
                    // different live class key reads a different dense slot.
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
            assert(um == oum.update(li, seq![oun.len() as usize] + oum[li]));
            assert(un.len() == oun.len() + 1);
            assert(un[oun.len() as int].payload == parent_node);

            assert forall|l: int, p: int|
                0 <= l < um.len() && 0 <= p < (#[trigger] um[l]).len()
                implies un[#[trigger] um[l][p] as int].payload.id_nat() < n by {
                if l == li && p == 0 {
                    // the fresh node, at the front: it names `parent_node`,
                    // whose id the entry guard bounded by `n`.
                    assert(um[l][p] == oun.len() as usize);
                } else if l == li {
                    // an old entry of this list, shifted one right by the prepend.
                    assert(um[l][p] == oum[l][p - 1]);
                    assert(oum[l][p - 1] < oun.len());
                    assert(un[um[l][p] as int].payload == oun[oum[l][p - 1] as int].payload);
                } else {
                    assert(um[l][p] == oum[l][p]);
                    assert(oum[l][p] < oun.len());
                    assert(un[um[l][p] as int].payload == oun[oum[l][p] as int].payload);
                }
            }
            assert(eg_model_wf::<T, L, N>(
                self.entries.model_view(), self.entries.payload_seq(),
                self.uf.roots_view(), dense, sparse, indices, um, un,
                self.min_pool.view(), self.min_width as nat));
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
                    um, un, self.min_pool.view(), self.min_width as nat));
            } else {
                // the arena refused (equal or out-of-range handles diverge
                // before mutation) or the ensures' conditional guards fired;
                // in every returning case the views are unchanged.
                assert(um == oum && un == oun);
                assert(eg_model_wf::<T, L, N>(
                    self.entries.model_view(), self.entries.payload_seq(),
                    self.uf.roots_view(), self.reprs.dense_view(),
                    self.reprs.sparse_view(), self.reprs.indices_view(),
                    um, un, self.min_pool.view(), self.min_width as nat));
            }
        }
    }


    /// Set the min-monomial pool row width (production's `set_min_width`):
    /// once rows exist the width is frozen, and a change request refuses.
    pub fn set_min_width(&mut self, width: usize)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).roots_view() == old(self).roots_view(),
            final(self).min_width_spec() == width as nat,
    {
        if self.min_width == width {
            return;
        }
        if !(self.min_pool.len() == 0) {
            crate::guard::refuse("EClasses::set_min_width: width is fixed once rows exist");
        }
        let ghost o = *old(self);
        self.min_width = width;
        proof {
            // the pool is empty, so the geometry clause is 0 % w == 0 and no
            // live class can hold a row number (its allocation bound would
            // read (r+1)*w <= 0).
            let dense = self.reprs.dense_view();
            let sparse = self.reprs.sparse_view();
            let indices = self.reprs.indices_view();
            let live = self.reprs.n_spec();
            assert(self.min_pool.view().len() == 0);
            assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
                && ss_value(dense, sparse, kk).min_row is Some
                implies (width as nat) > 0
                    && (ss_value(dense, sparse, kk).min_row->Some_0.as_nat() + 1)
                        * (width as nat) <= self.min_pool.view().len() by {
                // refuted: under the OLD width the same clause bounded the
                // row by the pool length, which is 0.
                assert((ss_value(dense, sparse, kk).min_row->Some_0.as_nat() + 1)
                    * (o.min_width as nat) <= 0);
                assert(false) by (nonlinear_arith)
                    requires (ss_value(dense, sparse, kk).min_row->Some_0.as_nat() + 1)
                        * (o.min_width as nat) <= 0,
                        o.min_width as nat > 0;
            }
            assert((self.min_pool.view().len() as nat) % (width as nat) == 0
                || width == 0) by {
                if width > 0 {
                    assert((0 as nat) % (width as nat) == 0);
                }
            }
            assert(eg_model_wf::<T, L, N>(
                self.entries.model_view(), self.entries.payload_seq(),
                self.uf.roots_view(), dense, sparse, indices,
                self.uses.model_view(), self.uses.nodes_view(),
                self.min_pool.view(), width as nat));
            // the archive under the NEW width: the live pool is empty and
            // archived pool lengths are bounded by it, so every archived
            // frame's pool is empty, W6 is vacuous at any width, and no
            // other clause reads the width.
            reveal(eg_archive_agrees);
            assert(eg_archive_agrees::<T, L, N>(
                o.entries.model_snapshots_view(),
                o.entries.entries_snapshots_view(),
                o.uf.roots_snapshots_view(),
                o.reprs.dense_snapshots_view(),
                o.reprs.sparse_snapshots_view(),
                o.reprs.indices_snapshots_view(),
                o.uses.model_snapshots_view(),
                o.uses.nodes_snapshots_view(),
                o.min_pool.snapshots_view(),
                o.min_width as nat));
            assert forall|k: int| 0 <= k < self.entries.model_snapshots_view().len()
                implies eg_model_wf::<T, L, N>(
                    #[trigger] self.entries.model_snapshots_view()[k],
                    ring_payloads(self.entries.entries_snapshots_view()[k]),
                    self.uf.roots_snapshots_view()[k],
                    self.reprs.dense_snapshots_view()[k],
                    self.reprs.sparse_snapshots_view()[k],
                    self.reprs.indices_snapshots_view()[k],
                    self.uses.model_snapshots_view()[k],
                    self.uses.nodes_snapshots_view()[k],
                    self.min_pool.snapshots_view()[k],
                    width as nat) by {
                let pool_k = self.min_pool.snapshots_view()[k];
                assert(pool_k.len() <= self.min_pool.view().len());
                assert(pool_k.len() == 0);
                let sp_k = self.reprs.sparse_snapshots_view()[k];
                let ix_k = self.reprs.indices_snapshots_view()[k];
                let de_k = self.reprs.dense_snapshots_view()[k];
                // old-width frame invariant
                assert(eg_model_wf::<T, L, N>(
                    self.entries.model_snapshots_view()[k],
                    ring_payloads(self.entries.entries_snapshots_view()[k]),
                    self.uf.roots_snapshots_view()[k],
                    de_k, sp_k, ix_k,
                    self.uses.model_snapshots_view()[k],
                    self.uses.nodes_snapshots_view()[k],
                    pool_k, o.min_width as nat));
                // no archived live class key can hold a row: the old-width W6
                // bound reads (r+1)*old_w <= 0 with old_w > 0, or forces
                // old_w > 0 when a row exists.
                assert forall|id: nat| #[trigger] ss_contains(sp_k, ix_k, de_k.len(), id)
                    && ss_value(de_k, sp_k, id).min_row is Some
                    implies false by {
                    let r0 = ss_value(de_k, sp_k, id).min_row->Some_0.as_nat();
                    assert((o.min_width as nat) > 0
                        && (r0 + 1) * (o.min_width as nat) <= pool_k.len());
                    assert((r0 + 1) * (o.min_width as nat) > 0) by (nonlinear_arith)
                        requires (o.min_width as nat) > 0;
                }
                if width > 0 {
                    assert((pool_k.len() as nat) % (width as nat) == 0);
                }
            }
            assert(eg_archive_agrees::<T, L, N>(
                self.entries.model_snapshots_view(),
                self.entries.entries_snapshots_view(),
                self.uf.roots_snapshots_view(),
                self.reprs.dense_snapshots_view(),
                self.reprs.sparse_snapshots_view(),
                self.reprs.indices_snapshots_view(),
                self.uses.model_snapshots_view(),
                self.uses.nodes_snapshots_view(),
                self.min_pool.snapshots_view(),
                width as nat));
        }
    }

    pub fn min_width(&self) -> (w: usize)
        requires self.wf(),
        ensures w as nat == self.min_width_spec(),
    {
        self.min_width
    }

    /// Read class `key`'s min-monomial for completion column `col`
    /// (`None` when the class has no row or the cell is empty). Refuses a
    /// dead key or an out-of-range column.
    pub fn min_monomial(&self, key: <T as DenseId>::Index, col: usize) -> (r: Option<T>)
        requires self.wf(),
    {
        if !(col < self.min_width) {
            crate::guard::refuse("EClasses::min_monomial: completion column out of range");
        }
        if !self.reprs.contains(key) {
            crate::guard::refuse("EClasses::min_monomial: class key is not live");
        }
        let data = self.reprs.get_live(key);
        match data.min_row {
            None => None,
            Some(row) => {
                proof {
                    // W6: the row is allocated, so base + col is in the pool.
                    assert(ss_contains(self.reprs.sparse_view(), self.reprs.indices_view(),
                        self.reprs.n_spec(), key.as_nat()));
                    assert((row.as_nat() + 1) * (self.min_width as nat)
                        <= self.min_pool.view().len());
                    assert(row.as_nat() * (self.min_width as nat) + (self.min_width as nat)
                        == (row.as_nat() + 1) * (self.min_width as nat)) by (nonlinear_arith);
                    <T::Index as IndexLike>::lemma_max_nat_fits_usize();
                }
                let base = row.as_usize() * self.min_width;
                let cell = self.min_pool.get_index(base + col);
                proof {
                    assert(cell == self.min_pool.view()[(base + col) as int]);
                    assert(cell.wf());
                }
                cell.to_option()
            }
        }
    }

    /// Write class `key`'s min-monomial for column `col`, allocating the
    /// class's pool row on first use (production's `ensure_min_row` +
    /// `set_min_monomial`). Refuses a dead key, an out-of-range column, a
    /// zero width, or pool exhaustion.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(120)]
    pub fn set_min_monomial(&mut self, key: <T as DenseId>::Index, col: usize, node: T)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).roots_view() == old(self).roots_view(),
            final(self).num_classes_spec() == old(self).num_classes_spec(),
            final(self).min_width_spec() == old(self).min_width_spec(),
    {
        if !(self.min_width > 0 && col < self.min_width) {
            crate::guard::refuse("EClasses::set_min_monomial: completion column out of range");
        }
        if !self.reprs.contains(key) {
            crate::guard::refuse("EClasses::set_min_monomial: class key is not live");
        }
        let ghost o = *old(self);
        let ghost w = o.min_width as nat;
        let mut data = self.reprs.get_live(key);
        proof {
            assert(ss_contains(o.reprs.sparse_view(), o.reprs.indices_view(),
                o.reprs.n_spec(), key.as_nat()));
            assert(data == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(),
                key.as_nat()));
        }
        let row = match data.min_row {
            Some(row) => {
                proof {
                    // W6 in the old state bounds the existing row; the pool
                    // is untouched on this arm.
                    assert((row.as_nat() + 1) * w <= self.min_pool.view().len());
                    assert(forall|i: int| 0 <= i < self.min_pool.view().len()
                        ==> (#[trigger] self.min_pool.view()[i]).wf());
                }
                row
            }
            None => {
                // allocate a fresh all-empty row at the pool's end.
                let len0 = self.min_pool.len();
                proof {
                    assert(len0 as nat % w == 0);
                    assert(len0 as nat == self.min_pool.view().len());
                }
                let row_num = len0 / self.min_width;
                proof {
                    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                        len0 as int, o.min_width as int);
                    assert(len0 as int == (o.min_width as int) * (row_num as int));
                }
                let row = match <T::Index as IndexLike>::try_from_usize(row_num) {
                    Some(r) => r,
                    None => crate::guard::refuse(
                        "EClasses::set_min_monomial: row number exceeds the id index range"),
                };
                let mut i: usize = 0;
                while i < self.min_width
                    invariant
                        o.wf(),
                        self.min_width == o.min_width,
                        self.min_width > 0,
                        i <= self.min_width,
                        self.entries == o.entries,
                        self.reprs == o.reprs,
                        self.uf == o.uf,
                        self.uses == o.uses,
                        self.min_pool.wf(),
                        self.min_pool.view().len() == o.min_pool.view().len() + i as nat,
                        self.min_pool.snapshots_view() == o.min_pool.snapshots_view(),
                        forall|j: int| 0 <= j < self.min_pool.view().len()
                            ==> (#[trigger] self.min_pool.view()[j]).wf(),
                    decreases self.min_width - i,
                {
                    match self.min_pool.try_push(Opt::none()) {
                        Ok(()) => (),
                        Err(_) => crate::guard::refuse(
                            "EClasses::set_min_monomial: min-monomial pool exhausted"),
                    }
                    i = i + 1;
                }
                data.min_row = Some(row);
                self.reprs.set_live(key, data);
                proof {
                    let len1 = self.min_pool.view().len();
                    let dense = self.reprs.dense_view();
                    let sparse = self.reprs.sparse_view();
                    let indices = self.reprs.indices_view();
                    let live = self.reprs.n_spec();
                    let odense = o.reprs.dense_view();
                    let osparse = o.reprs.sparse_view();
                    let oindices = o.reprs.indices_view();
                    assert(len1 == o.min_pool.view().len() + w);
                    assert(row.as_nat() == row_num as nat);
                    // the new row is exactly the grown tail.
                    assert((row.as_nat() + 1) * w == len1) by (nonlinear_arith)
                        requires
                            o.min_pool.view().len() as int
                                == (w as int) * (row.as_nat() as int),
                            len1 == o.min_pool.view().len() + w;
                    // geometry: len1 == w * (row + 1), a whole number of rows.
                    assert(len1 as int == (w as int) * ((row.as_nat() + 1) as int))
                        by (nonlinear_arith)
                        requires
                            o.min_pool.view().len() as int
                                == (w as int) * (row.as_nat() as int),
                            len1 == o.min_pool.view().len() + w;
                    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
                        (row.as_nat() + 1) as int, w as int);
                    assert(len1 % w == 0);
                    // reprs: only key's value changed, and only its min_row.
                    assert(sparse == osparse && indices == oindices
                        && live == o.reprs.n_spec());
                    assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
                        && kk != key.as_nat()
                        implies ss_value(dense, sparse, kk)
                            == ss_value(odense, osparse, kk) by {
                        assert(osparse[kk as int].as_nat()
                            != osparse[key.as_nat() as int].as_nat()) by {
                            if osparse[kk as int].as_nat()
                                == osparse[key.as_nat() as int].as_nat() {
                                assert(oindices[osparse[kk as int].as_nat() as int]
                                    .as_nat() == kk);
                            }
                        }
                    }
                    // every OLD row is strictly below the new one.
                    assert forall|kk: nat| #[trigger] ss_contains(osparse, oindices,
                            o.reprs.n_spec(), kk)
                        && ss_value(odense, osparse, kk).min_row is Some
                        implies ss_value(odense, osparse, kk).min_row->Some_0.as_nat()
                            < row.as_nat() by {
                        let r0 = ss_value(odense, osparse, kk).min_row->Some_0.as_nat();
                        assert((r0 + 1) * w <= o.min_pool.view().len());
                        assert(r0 < row.as_nat()) by (nonlinear_arith)
                            requires
                                (r0 + 1) * w <= o.min_pool.view().len(),
                                o.min_pool.view().len() as int
                                    == (w as int) * (row.as_nat() as int),
                                w > 0;
                    }
                    assert(forall|i: int| 0 <= i < self.min_pool.view().len()
                        ==> (#[trigger] self.min_pool.view()[i]).wf());
                }
                row
            }
        };
        let ghost mid = *self;
        proof {
            // both arms deliver: the class's row is allocated in the current
            // pool, and eg_model_wf holds for the mid state.
            assert((row.as_nat() + 1) * w <= self.min_pool.view().len());
            assert(row.as_nat() * w + w == (row.as_nat() + 1) * w) by (nonlinear_arith);
            <T::Index as IndexLike>::lemma_max_nat_fits_usize();
            self.lemma_mid_pool_wf(o, key, row);
        }
        let base = row.as_usize() * self.min_width;
        let cell = Opt::some(node);
        self.min_pool.set_index(base + col, cell);
        proof {
            assert(self.min_pool.view().len() == mid.min_pool.view().len());
            assert(eg_model_wf::<T, L, N>(
                self.entries.model_view(), self.entries.payload_seq(),
                self.uf.roots_view(), self.reprs.dense_view(),
                self.reprs.sparse_view(), self.reprs.indices_view(),
                self.uses.model_view(), self.uses.nodes_view(),
                self.min_pool.view(), self.min_width as nat));
            // the pool only grew, so the archived-length bound carries.
            assert(self.min_pool.snapshots_view() == o.min_pool.snapshots_view());
            assert(o.min_pool.view().len() <= self.min_pool.view().len());
            assert forall|k: int| 0 <= k < self.min_pool.snapshots_view().len()
                implies (#[trigger] self.min_pool.snapshots_view()[k]).len()
                    <= self.min_pool.view().len() by {
                assert(self.min_pool.snapshots_view()[k].len()
                    <= o.min_pool.view().len());
            }
        }
    }

    /// The mid-state invariant of `set_min_monomial`, per arm: with the row
    /// already allocated (either from the old state or freshly grown), the
    /// full joint invariant holds. Extracted so the two arms discharge one
    /// obligation each instead of the final assert re-deriving both.
    proof fn lemma_mid_pool_wf(&self, o: Self, key: <T as DenseId>::Index,
        row: <T as DenseId>::Index)
        requires
            o.wf(),
            self.entries == o.entries,
            self.uf == o.uf,
            self.uses == o.uses,
            self.min_width == o.min_width,
            (o.min_width as nat) > 0,
            self.reprs.wf(),
            self.min_pool.wf(),
            self.reprs.n_spec() == o.reprs.n_spec(),
            self.reprs.cap_spec() == o.reprs.cap_spec(),
            self.reprs.sparse_view() == o.reprs.sparse_view(),
            self.reprs.indices_view() == o.reprs.indices_view(),
            ss_contains(o.reprs.sparse_view(), o.reprs.indices_view(),
                o.reprs.n_spec(), key.as_nat()),
            // the only possible dense change is key's min_row becoming
            // Some(row); everything else of the value survives.
            ss_value(self.reprs.dense_view(), self.reprs.sparse_view(), key.as_nat())
                .use_list
                == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(), key.as_nat())
                    .use_list,
            ss_value(self.reprs.dense_view(), self.reprs.sparse_view(), key.as_nat())
                .size
                == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(), key.as_nat())
                    .size,
            ss_value(self.reprs.dense_view(), self.reprs.sparse_view(), key.as_nat())
                .min_row is Some,
            ss_value(self.reprs.dense_view(), self.reprs.sparse_view(), key.as_nat())
                .min_row->Some_0 == row,
            forall|kk: nat| #[trigger] ss_contains(o.reprs.sparse_view(),
                    o.reprs.indices_view(), o.reprs.n_spec(), kk)
                && kk != key.as_nat()
                ==> ss_value(self.reprs.dense_view(), self.reprs.sparse_view(), kk)
                    == ss_value(o.reprs.dense_view(), o.reprs.sparse_view(), kk),
            (row.as_nat() + 1) * (o.min_width as nat) <= self.min_pool.view().len(),
            self.min_pool.view().len() % (o.min_width as nat) == 0,
            forall|i: int| 0 <= i < self.min_pool.view().len()
                ==> (#[trigger] self.min_pool.view()[i]).wf(),
            // strict dominance: every other live row is below `row` OR the
            // pool did not grow and rows are the old ones (covered by the
            // dominance hypothesis at the call sites).
            forall|kk: nat| #[trigger] ss_contains(o.reprs.sparse_view(),
                    o.reprs.indices_view(), o.reprs.n_spec(), kk)
                && kk != key.as_nat()
                && ss_value(o.reprs.dense_view(), o.reprs.sparse_view(), kk)
                    .min_row is Some
                ==> ss_value(o.reprs.dense_view(), o.reprs.sparse_view(), kk)
                        .min_row->Some_0.as_nat() != row.as_nat()
                    && (ss_value(o.reprs.dense_view(), o.reprs.sparse_view(), kk)
                        .min_row->Some_0.as_nat() + 1) * (o.min_width as nat)
                        <= self.min_pool.view().len(),
        ensures
            eg_model_wf::<T, L, N>(
                self.entries.model_view(), self.entries.payload_seq(),
                self.uf.roots_view(), self.reprs.dense_view(),
                self.reprs.sparse_view(), self.reprs.indices_view(),
                self.uses.model_view(), self.uses.nodes_view(),
                self.min_pool.view(), self.min_width as nat),
    {
        let dense = self.reprs.dense_view();
        let sparse = self.reprs.sparse_view();
        let indices = self.reprs.indices_view();
        let live = self.reprs.n_spec();
        let odense = o.reprs.dense_view();
        let osparse = o.reprs.sparse_view();
        let oindices = o.reprs.indices_view();
        // W2b-d and W4 quantify over values whose use_list/liveness are
        // untouched; W6 is the hypothesis set.
        assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
            implies ss_value(dense, sparse, kk).use_list
                    == ss_value(odense, osparse, kk).use_list
                && ss_value(dense, sparse, kk).size
                    == ss_value(odense, osparse, kk).size by {
            if kk != key.as_nat() {
                assert(ss_value(dense, sparse, kk) == ss_value(odense, osparse, kk));
            }
        }
        assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
            && kk != key.as_nat()
            implies ss_value(dense, sparse, kk) == ss_value(odense, osparse, kk) by {}
        assert(eg_model_wf::<T, L, N>(
            self.entries.model_view(), self.entries.payload_seq(),
            self.uf.roots_view(), dense, sparse, indices,
            self.uses.model_view(), self.uses.nodes_view(),
            self.min_pool.view(), self.min_width as nat));
    }

    /// Whether class `key` is atomic (referenced as a child). Refuses a
    /// dead key.
    pub fn atomic(&self, key: <T as DenseId>::Index) -> (b: bool)
        requires self.wf(),
    {
        if !self.reprs.contains(key) {
            crate::guard::refuse("EClasses::atomic: class key is not live");
        }
        self.reprs.get_live(key).atomic
    }

    /// The use-list id of class `key`. Refuses a dead key.
    pub fn use_list_id(&self, key: <T as DenseId>::Index) -> (l: L)
        requires self.wf(),
        ensures self.contains_key_spec(key)
            ==> l == self.class_data_spec(key.as_nat()).use_list,
    {
        if !self.reprs.contains(key) {
            crate::guard::refuse("EClasses::use_list_id: class key is not live");
        }
        self.reprs.get_live(key).use_list
    }


    /// Mark class `key` atomic (production's `set_atomic`; `EGraph` calls it
    /// when a class gains a non-completion node). Refuses a dead key.
    pub fn set_atomic(&mut self, key: <T as DenseId>::Index)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).roots_view() == old(self).roots_view(),
            final(self).num_classes_spec() == old(self).num_classes_spec(),
    {
        if !self.reprs.contains(key) {
            crate::guard::refuse("EClasses::set_atomic: class key is not live");
        }
        let ghost o = *old(self);
        let mut data = self.reprs.get_live(key);
        if data.atomic {
            return;
        }
        data.atomic = true;
        self.reprs.set_live(key, data);
        proof {
            let dense = self.reprs.dense_view();
            let sparse = self.reprs.sparse_view();
            let indices = self.reprs.indices_view();
            let live = self.reprs.n_spec();
            let odense = o.reprs.dense_view();
            let osparse = o.reprs.sparse_view();
            let oindices = o.reprs.indices_view();
            assert(sparse == osparse && indices == oindices && live == o.reprs.n_spec());
            assert forall|kk: nat| #[trigger] ss_contains(sparse, indices, live, kk)
                implies ss_value(dense, sparse, kk).use_list
                        == ss_value(odense, osparse, kk).use_list
                    && ss_value(dense, sparse, kk).min_row
                        == ss_value(odense, osparse, kk).min_row by {
                if kk != key.as_nat() {
                    assert(osparse[kk as int].as_nat()
                        != osparse[key.as_nat() as int].as_nat()) by {
                        if osparse[kk as int].as_nat()
                            == osparse[key.as_nat() as int].as_nat() {
                            assert(oindices[osparse[kk as int].as_nat() as int]
                                .as_nat() == kk);
                        }
                    }
                    assert(ss_value(dense, sparse, kk) == ss_value(odense, osparse, kk));
                }
            }
            assert(eg_model_wf::<T, L, N>(
                self.entries.model_view(), self.entries.payload_seq(),
                self.uf.roots_view(), dense, sparse, indices,
                self.uses.model_view(), self.uses.nodes_view(),
                self.min_pool.view(), self.min_width as nat));
        }
    }

    /// Iterate `start`'s class ring (the verified `RingIter`: exactly the
    /// ring's nodes, each once, in successor order).
    pub fn iter_class(&self, start: T)
        -> (it: crate::circular_list::RingIter<'_, Opt<<T as DenseId>::Index>, T, TRACK>)
        requires self.wf(),
        ensures start.id_nat() < self.n_spec() ==> ({
            &&& it.list_ref() == self.entries_ref()
            &&& it.start_spec() == start.id_nat()
            &&& it.pos_spec() == 0
            &&& !it.done_spec()
            &&& it.cursor_ok()
            &&& it.walk_seq() == self.class_seq(start.id_nat() as int)
        }),
    {
        self.entries.iter_class(start)
    }

    /// Iterate class `key`'s use-list (the verified `ListIter`). Refuses a
    /// dead key.
    pub fn iter_uses(&self, key: <T as DenseId>::Index)
        -> (it: crate::list::ListIter<'_, T, L, N, TRACK>)
        requires self.wf(),
        ensures self.contains_key_spec(key) ==> ({
            &&& it.arena_ref() == self.uses_ref()
            &&& it.list_spec() == self.class_data_spec(key.as_nat()).use_list.id_nat()
            &&& it.pos_spec() == 0
            &&& it.cursor_ok()
        }),
    {
        if !self.reprs.contains(key) {
            crate::guard::refuse("EClasses::iter_uses: class key is not live");
        }
        let l = self.reprs.get_live(key).use_list;
        proof {
            assert(ss_contains(self.reprs.sparse_view(), self.reprs.indices_view(),
                self.reprs.n_spec(), key.as_nat()));
            assert(l.id_nat() < self.uses.model_view().len());
        }
        self.uses.iter(l)
    }


    /// O(1) length of class `key`'s use-list, widened to `usize` at the
    /// boundary (production's `use_list_len`). Refuses a dead key.
    pub fn use_list_len(&self, key: <T as DenseId>::Index) -> (n: usize)
        requires self.wf(),
    {
        if !self.reprs.contains(key) {
            crate::guard::refuse("EClasses::use_list_len: class key is not live");
        }
        let l = self.reprs.get_live(key).use_list;
        proof {
            assert(ss_contains(self.reprs.sparse_view(), self.reprs.indices_view(),
                self.reprs.n_spec(), key.as_nat()));
            assert(l.id_nat() < self.uses.model_view().len());
        }
        self.uses.len(l).as_usize()
    }

    /// O(1) member-node count of class `key`, widened to `usize` at the
    /// boundary like `use_list_len` (the stored counter is `T::Index`-wide,
    /// so the width follows the configuration). Refuses a dead key. Feeds the
    /// `--union-by size`/`sum` survivor policy.
    pub fn class_size(&self, key: <T as DenseId>::Index) -> (n: usize)
        requires self.wf(),
    {
        if !self.reprs.contains(key) {
            crate::guard::refuse("EClasses::class_size: class key is not live");
        }
        self.reprs.get_live(key).size.as_usize()
    }

    /// Read completion column `col` of a pool row number carried in
    /// `MergeInfo` (production's `min_monomial_at_row`): `None` when the row
    /// is absent or the cell is empty. Refuses an out-of-range column or an
    /// unallocated row number.
    pub fn min_monomial_at_row(&self, row: Option<<T as DenseId>::Index>, col: usize)
        -> (r: Option<T>)
        requires self.wf(),
    {
        if !(col < self.min_width) {
            crate::guard::refuse("EClasses::min_monomial_at_row: completion column out of range");
        }
        let row = match row {
            None => {
                return None;
            }
            Some(row) => row,
        };
        proof { <T::Index as IndexLike>::lemma_max_nat_fits_usize(); }
        let base = match crate::index_like::checked_mul(row.as_usize(), self.min_width) {
            Some(b) => b,
            None => crate::guard::refuse(
                "EClasses::min_monomial_at_row: row offset overflows"),
        };
        let len = self.min_pool.len();
        if !(base < len && col < len - base) {
            crate::guard::refuse("EClasses::min_monomial_at_row: row is not allocated");
        }
        let cell = self.min_pool.get_index(base + col);
        proof {
            assert(cell == self.min_pool.view()[(base + col) as int]);
            assert(cell.wf());
        }
        cell.to_option()
    }

    /// Direct read access to the use-list arena (production's `uses`; the
    /// rebuild loop iterates an absorbed list by id).
    pub fn uses(&self) -> (a: &ListArena<T, L, N, TRACK>)
        requires self.wf(),
        ensures a == self.uses_ref(), a.wf(),
    {
        &self.uses
    }

    /// Union-by-rank merge. Only available when `PROOFS = false`
    /// (production's contract, with its message); `merge_justified` is the
    /// proofs form.
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
        if PROOFS {
            crate::guard::refuse(
                "union() called on a PROOFS=true UnionFind; use union_justified() instead");
        }
        self.merge_with(a, b, false, false)
    }

    /// Whether `find(a)`'s class has at least as many parents as `find(b)`'s
    /// (production's survivor policy for directed merges).
    fn prefer_a_by_uses(&self, a: T, b: T) -> (r: bool)
        requires self.wf(),
    {
        if !(a.to_usize() < self.uf.len().as_usize()
            && b.to_usize() < self.uf.len().as_usize())
        {
            crate::guard::refuse("EClasses::merge_directed: node id out of range");
        }
        let ra = self.uf.find_const(a);
        let rb = self.uf.find_const(b);
        let la = match self.repr_id(ra) {
            Some(k) => self.use_list_len(k),
            None => 0,
        };
        let lb = match self.repr_id(rb) {
            Some(k) => self.use_list_len(k),
            None => 0,
        };
        la >= lb
    }

    /// Like [`Self::merge`], but keeps the larger-use-list class as
    /// survivor (production's two-argument `merge_directed`). Only
    /// available when `PROOFS = false`.
    pub fn merge_directed(&mut self, a: T, b: T) -> (r: Option<MergeInfo<T, L>>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            a.id_nat() < old(self).n_spec() && b.id_nat() < old(self).n_spec() ==> {
                let ra = old(self).roots_view()[a.id_nat() as int] as nat;
                let rb = old(self).roots_view()[b.id_nat() as int] as nat;
                &&& (r is None <==> ra == rb)
                &&& (r matches Some(mi) ==> {
                        &&& ((mi.survivor.id_nat() == ra && mi.absorbed.id_nat() == rb)
                            || (mi.survivor.id_nat() == rb && mi.absorbed.id_nat() == ra))
                        &&& final(self).roots_view() == crate::union_find::merge_roots(
                                old(self).roots_view(), mi.survivor.id_nat(),
                                mi.absorbed.id_nat())
                    })
            },
    {
        if PROOFS {
            crate::guard::refuse(
                "union_directed() called on a PROOFS=true UnionFind; use union_justified_directed()");
        }
        let prefer_a = self.prefer_a_by_uses(a, b);
        self.merge_with(a, b, true, prefer_a)
    }

    /// The directed core with an explicit survivor flag (`merge_with`'s
    /// public face for callers that computed their own policy; the
    /// conformance differential uses it).
    pub fn merge_directed_with(&mut self, a: T, b: T, prefer_a: bool)
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

// ---------------------------------------------------------------------------
// Semi-persistence: compose from the five components
// ---------------------------------------------------------------------------

/// Token bundling the five component tokens.
#[derive(Copy, Clone)]
pub struct EClassesToken {
    pub(crate) entries: CircularListToken,
    pub(crate) reprs: SparseSetToken,
    pub(crate) uf: UnionFindToken,
    pub(crate) uses: ListArenaToken,
    pub(crate) pool: VecToken,
}

impl EClassesToken {
    pub open(crate) spec fn frame_idx_spec(self) -> nat {
        self.pool.frame_idx as nat
    }
}

impl<T, L, N, J, const TRACK: bool, const PROOFS: bool> EClasses<T, L, N, J, TRACK, PROOFS>
where
    T: DenseId,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
    J: Tagged + Copy + core::default::Default,
{
    /// Mark the aggregate: one frame on every component, atomically from the
    /// caller's view (a component that cannot mark refuses before the next
    /// one is touched, production's panic-on-depth-exhaustion semantics).
    pub fn mark(&mut self, shrink: ShrinkPolicy) -> (token: EClassesToken)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).n_spec() == old(self).n_spec(),
            final(self).roots_view() == old(self).roots_view(),
            final(self).num_classes_spec() == old(self).num_classes_spec(),
            final(self).min_width_spec() == old(self).min_width_spec(),
            token.frame_idx_spec() == final(self).depth_spec() - 1,
            final(self).depth_spec() == old(self).depth_spec() + 1,
    {
        if !TRACK {
            crate::guard::refuse("EClasses::mark: untracked aggregate");
        }
        let ghost o = *old(self);
        let t_entries = match self.entries.try_mark(shrink) {
            Ok(t) => t,
            Err(_) => crate::guard::refuse("EClasses::mark: ring mark refused"),
        };
        let t_reprs = match self.reprs.try_mark(shrink) {
            Ok(t) => t,
            Err(_) => crate::guard::refuse("EClasses::mark: repr-set mark refused"),
        };
        let t_uf = match self.uf.try_mark(shrink) {
            Ok(t) => t,
            Err(_) => crate::guard::refuse("EClasses::mark: union-find mark refused"),
        };
        let t_uses = match self.uses.try_mark(shrink) {
            Ok(t) => t,
            Err(_) => crate::guard::refuse("EClasses::mark: use-list mark refused"),
        };
        let t_pool = match self.min_pool.try_mark(shrink) {
            Ok(t) => t,
            Err(_) => crate::guard::refuse("EClasses::mark: pool mark refused"),
        };
        proof {
            reveal(eg_archive_agrees);
            assert(eg_archive_agrees::<T, L, N>(
                o.entries.model_snapshots_view(),
                o.entries.entries_snapshots_view(),
                o.uf.roots_snapshots_view(),
                o.reprs.dense_snapshots_view(),
                o.reprs.sparse_snapshots_view(),
                o.reprs.indices_snapshots_view(),
                o.uses.model_snapshots_view(),
                o.uses.nodes_snapshots_view(),
                o.min_pool.snapshots_view(),
                o.min_width as nat));
            let k_new = self.entries.model_snapshots_view().len() - 1;
            // the pushed frame archives the live views; the live joint
            // invariant IS eg_model_wf over them. The payload projection of
            // the pushed cell snapshot is the live payload_seq.
            assert(ring_payloads(self.entries.entries_snapshots_view()[k_new])
                =~= o.entries.payload_seq());
            assert(eg_model_wf::<T, L, N>(
                self.entries.model_snapshots_view()[k_new],
                ring_payloads(self.entries.entries_snapshots_view()[k_new]),
                self.uf.roots_snapshots_view()[k_new],
                self.reprs.dense_snapshots_view()[k_new],
                self.reprs.sparse_snapshots_view()[k_new],
                self.reprs.indices_snapshots_view()[k_new],
                self.uses.model_snapshots_view()[k_new],
                self.uses.nodes_snapshots_view()[k_new],
                self.min_pool.snapshots_view()[k_new],
                self.min_width as nat));
            assert(crate::sparse_set::sparse_set_snap_wf(
                self.reprs.dense_snapshots_view()[k_new],
                self.reprs.sparse_snapshots_view()[k_new],
                self.reprs.indices_snapshots_view()[k_new]));
            assert forall|k: int| 0 <= k < self.entries.model_snapshots_view().len()
                implies eg_model_wf::<T, L, N>(
                    #[trigger] self.entries.model_snapshots_view()[k],
                    ring_payloads(self.entries.entries_snapshots_view()[k]),
                    self.uf.roots_snapshots_view()[k],
                    self.reprs.dense_snapshots_view()[k],
                    self.reprs.sparse_snapshots_view()[k],
                    self.reprs.indices_snapshots_view()[k],
                    self.uses.model_snapshots_view()[k],
                    self.uses.nodes_snapshots_view()[k],
                    self.min_pool.snapshots_view()[k],
                    self.min_width as nat)
                && crate::sparse_set::sparse_set_snap_wf(
                    self.reprs.dense_snapshots_view()[k],
                    self.reprs.sparse_snapshots_view()[k],
                    self.reprs.indices_snapshots_view()[k]) by {
                if k < k_new {
                    assert(self.entries.model_snapshots_view()[k]
                        == o.entries.model_snapshots_view()[k]);
                    assert(self.entries.entries_snapshots_view()[k]
                        == o.entries.entries_snapshots_view()[k]);
                    assert(self.uf.roots_snapshots_view()[k]
                        == o.uf.roots_snapshots_view()[k]);
                    assert(self.reprs.dense_snapshots_view()[k]
                        == o.reprs.dense_snapshots_view()[k]);
                    assert(self.reprs.sparse_snapshots_view()[k]
                        == o.reprs.sparse_snapshots_view()[k]);
                    assert(self.reprs.indices_snapshots_view()[k]
                        == o.reprs.indices_snapshots_view()[k]);
                    assert(self.uses.model_snapshots_view()[k]
                        == o.uses.model_snapshots_view()[k]);
                    assert(self.uses.nodes_snapshots_view()[k]
                        == o.uses.nodes_snapshots_view()[k]);
                    assert(self.min_pool.snapshots_view()[k]
                        == o.min_pool.snapshots_view()[k]);
                }
            }
            // pool monotonicity: old pairs carry; pairs ending at the new
            // frame are bounded by the live length it archives.
            assert forall|k1: int, k2: int|
                0 <= k1 <= k2 < self.min_pool.snapshots_view().len()
                implies (#[trigger] self.min_pool.snapshots_view()[k1]).len()
                    <= (#[trigger] self.min_pool.snapshots_view()[k2]).len() by {
                if k2 < k_new {
                    assert(self.min_pool.snapshots_view()[k1]
                        == o.min_pool.snapshots_view()[k1]);
                    assert(self.min_pool.snapshots_view()[k2]
                        == o.min_pool.snapshots_view()[k2]);
                } else if k1 < k_new {
                    assert(self.min_pool.snapshots_view()[k1]
                        == o.min_pool.snapshots_view()[k1]);
                    assert(self.min_pool.snapshots_view()[k1].len()
                        <= o.min_pool.view().len());
                }
            }
        }
        EClassesToken {
            entries: t_entries,
            reprs: t_reprs,
            uf: t_uf,
            uses: t_uses,
            pool: t_pool,
        }
    }

    /// "Restorable now" for the composite token: every constituent
    /// restorable AND all nine leaf frames name the same mark.
    pub fn is_valid_token(&self, token: &EClassesToken) -> (b: bool)
        requires self.wf(),
    {
        self.entries.is_valid_token(&token.entries)
            && self.reprs.is_valid_token(&token.reprs)
            && self.uf.is_valid_token(&token.uf)
            && self.uses.is_valid_token(&token.uses)
            && self.min_pool.is_valid_token(&token.pool)
            && self.frames_agree(token)
    }

    /// All nine leaf tokens name the same frame (frankentoken defense).
    fn frames_agree(&self, token: &EClassesToken) -> (b: bool)
        ensures b == ({
            &&& token.entries.frame_idx_spec() == token.frame_idx_spec()
            &&& token.reprs.dense_frame_idx_spec() == token.frame_idx_spec()
            &&& token.reprs.sparse_frame_idx_spec() == token.frame_idx_spec()
            &&& token.reprs.indices_frame_idx_spec() == token.frame_idx_spec()
            &&& token.uf.parent_frame_idx_spec() == token.frame_idx_spec()
            &&& token.uf.rank_frame_idx_spec() == token.frame_idx_spec()
            &&& token.uses.heads_frame_idx_spec() == token.frame_idx_spec()
            &&& token.uses.nodes_frame_idx_spec() == token.frame_idx_spec()
        }),
    {
        let f = token.pool.frame_idx;
        token.entries.entries.frame_idx == f
            && token.reprs.dense.frame_idx == f
            && token.reprs.sparse.frame_idx == f
            && token.reprs.indices.frame_idx == f
            && token.uf.parent.frame_idx == f
            && token.uf.rank.frame_idx == f
            && token.uses.heads.frame_idx == f
            && token.uses.nodes.frame_idx == f
    }

    /// Restore the aggregate to the marked frame. Refuses an invalid,
    /// foreign, stale, consumed, or mixed-mark token before any mutation;
    /// `SparseSet::restore`'s snapshot-wellformedness precondition is
    /// discharged from the aggregate's own archive.
    pub fn restore(&mut self, token: EClassesToken)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            final(self).min_width_spec() == old(self).min_width_spec(),
            old(self).is_restorable_full_spec(token) ==> {
                &&& final(self).roots_view() == old(self).roots_archive_view()[
                        token.frame_idx_spec() as int]
                &&& final(self).n_spec() == old(self).roots_archive_view()[
                        token.frame_idx_spec() as int].len()
            },
    {
        if !(self.entries.is_valid_token(&token.entries)
            && self.reprs.is_valid_token(&token.reprs)
            && self.uf.is_valid_token(&token.uf)
            && self.uses.is_valid_token(&token.uses)
            && self.min_pool.is_valid_token(&token.pool)
            && self.frames_agree(&token))
        {
            crate::guard::refuse(
                "EClasses::restore: invalid, foreign, stale, consumed, abandoned, or mixed-mark token");
        }
        let ghost o = *old(self);
        let ghost f = token.pool.frame_idx as int;
        proof {
            reveal(eg_archive_agrees);
            assert(eg_archive_agrees::<T, L, N>(
                o.entries.model_snapshots_view(),
                o.entries.entries_snapshots_view(),
                o.uf.roots_snapshots_view(),
                o.reprs.dense_snapshots_view(),
                o.reprs.sparse_snapshots_view(),
                o.reprs.indices_snapshots_view(),
                o.uses.model_snapshots_view(),
                o.uses.nodes_snapshots_view(),
                o.min_pool.snapshots_view(),
                o.min_width as nat));
            // the archived frame f is a jointly-valid state; in particular
            // the repr triple is sparse-set well-formed, which is
            // SparseSet::restore's precondition.
            assert(crate::sparse_set::sparse_set_snap_wf(
                o.reprs.dense_snapshots_view()[f],
                o.reprs.sparse_snapshots_view()[f],
                o.reprs.indices_snapshots_view()[f]));
        }
        self.entries.restore(token.entries);
        self.reprs.restore(token.reprs);
        self.uf.restore(token.uf);
        self.uses.restore(token.uses);
        self.min_pool.restore(token.pool);
        proof {
            reveal(eg_archive_agrees);
            // restored views are the archived frame-f views.
            assert(self.entries.model_view() == o.entries.model_snapshots_view()[f]);
            assert(self.entries.payload_seq()
                =~= ring_payloads(o.entries.entries_snapshots_view()[f]));
            assert(self.uf.roots_view() == o.uf.roots_snapshots_view()[f]);
            assert(eg_model_wf::<T, L, N>(
                self.entries.model_view(), self.entries.payload_seq(),
                self.uf.roots_view(), self.reprs.dense_view(),
                self.reprs.sparse_view(), self.reprs.indices_view(),
                self.uses.model_view(), self.uses.nodes_view(),
                self.min_pool.view(), self.min_width as nat));
            // truncated stacks agree per frame below f.
            assert forall|k: int| 0 <= k < self.entries.model_snapshots_view().len()
                implies eg_model_wf::<T, L, N>(
                    #[trigger] self.entries.model_snapshots_view()[k],
                    ring_payloads(self.entries.entries_snapshots_view()[k]),
                    self.uf.roots_snapshots_view()[k],
                    self.reprs.dense_snapshots_view()[k],
                    self.reprs.sparse_snapshots_view()[k],
                    self.reprs.indices_snapshots_view()[k],
                    self.uses.model_snapshots_view()[k],
                    self.uses.nodes_snapshots_view()[k],
                    self.min_pool.snapshots_view()[k],
                    self.min_width as nat)
                && crate::sparse_set::sparse_set_snap_wf(
                    self.reprs.dense_snapshots_view()[k],
                    self.reprs.sparse_snapshots_view()[k],
                    self.reprs.indices_snapshots_view()[k]) by {
                assert(self.entries.model_snapshots_view()[k]
                    == o.entries.model_snapshots_view()[k]);
                assert(self.entries.entries_snapshots_view()[k]
                    == o.entries.entries_snapshots_view()[k]);
                assert(self.uf.roots_snapshots_view()[k]
                    == o.uf.roots_snapshots_view()[k]);
                assert(self.reprs.dense_snapshots_view()[k]
                    == o.reprs.dense_snapshots_view()[k]);
                assert(self.reprs.sparse_snapshots_view()[k]
                    == o.reprs.sparse_snapshots_view()[k]);
                assert(self.reprs.indices_snapshots_view()[k]
                    == o.reprs.indices_snapshots_view()[k]);
                assert(self.uses.model_snapshots_view()[k]
                    == o.uses.model_snapshots_view()[k]);
                assert(self.uses.nodes_snapshots_view()[k]
                    == o.uses.nodes_snapshots_view()[k]);
                assert(self.min_pool.snapshots_view()[k]
                    == o.min_pool.snapshots_view()[k]);
            }
            assert forall|k1: int, k2: int|
                0 <= k1 <= k2 < self.min_pool.snapshots_view().len()
                implies (#[trigger] self.min_pool.snapshots_view()[k1]).len()
                    <= (#[trigger] self.min_pool.snapshots_view()[k2]).len() by {
                assert(self.min_pool.snapshots_view()[k1]
                    == o.min_pool.snapshots_view()[k1]);
                assert(self.min_pool.snapshots_view()[k2]
                    == o.min_pool.snapshots_view()[k2]);
            }
            // archived pools below f are bounded by the restored pool
            // (monotonicity at (k, f)).
            assert forall|k: int| 0 <= k < self.min_pool.snapshots_view().len()
                implies (#[trigger] self.min_pool.snapshots_view()[k]).len()
                    <= self.min_pool.view().len() by {
                assert(o.min_pool.snapshots_view()[k].len()
                    <= o.min_pool.snapshots_view()[f].len());
            }
        }
    }

    /// The full runtime-checkable restore precondition (spec counterpart of
    /// `is_valid_token` plus the frame agreement).
    pub open(crate) spec fn is_restorable_full_spec(&self, token: EClassesToken) -> bool {
        &&& self.entries.is_restorable_spec(token.entries)
        &&& self.reprs.is_restorable_spec(token.reprs)
        &&& self.uf.is_restorable_spec(token.uf)
        &&& self.uses.is_restorable_spec(token.uses)
        &&& self.min_pool.is_restorable_spec(token.pool)
        &&& token.entries.frame_idx_spec() == token.frame_idx_spec()
        &&& token.reprs.dense_frame_idx_spec() == token.frame_idx_spec()
        &&& token.reprs.sparse_frame_idx_spec() == token.frame_idx_spec()
        &&& token.reprs.indices_frame_idx_spec() == token.frame_idx_spec()
        &&& token.uf.parent_frame_idx_spec() == token.frame_idx_spec()
        &&& token.uf.rank_frame_idx_spec() == token.frame_idx_spec()
        &&& token.uses.heads_frame_idx_spec() == token.frame_idx_spec()
        &&& token.uses.nodes_frame_idx_spec() == token.frame_idx_spec()
    }

    /// Total restore: an unusable token is `Err(InvalidToken)`.
    pub fn try_restore(&mut self, token: EClassesToken)
        -> (r: Result<(), crate::error::ContainerError>)
        requires old(self).wf(),
        ensures
            final(self).wf(),
            r matches Err(e) ==> e == crate::error::ContainerError::InvalidToken
                && final(self).roots_view() == old(self).roots_view(),
    {
        if self.entries.is_valid_token(&token.entries)
            && self.reprs.is_valid_token(&token.reprs)
            && self.uf.is_valid_token(&token.uf)
            && self.uses.is_valid_token(&token.uses)
            && self.min_pool.is_valid_token(&token.pool)
            && self.frames_agree(&token)
        {
            self.restore(token);
            Ok(())
        } else {
            Err(crate::error::ContainerError::InvalidToken)
        }
    }
}

} // verus!

// ---------------------------------------------------------------------------
// Justified merges and explain (trusted glue; the partition work is the
// verified core, the proof edge and LCA walk are production's algorithms in
// the union-find's glue — doc/design/egraph-class-layer.md).
// ---------------------------------------------------------------------------

impl<T, L, N, J, const TRACK: bool, const PROOFS: bool> EClasses<T, L, N, J, TRACK, PROOFS>
where
    T: DenseId,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
    J: Tagged + Copy + core::default::Default,
{
    /// Merge with justification (records the proof edge `a—b`).
    pub fn merge_justified(&mut self, a: T, b: T, just: J) -> Option<MergeInfo<T, L>> {
        let r = self.merge_with(a, b, false, false);
        if r.is_some() {
            self.uf.record_proof_edge(a, b, just);
        }
        r
    }

    /// Justified counterpart of [`Self::merge_directed`].
    pub fn merge_justified_directed(&mut self, a: T, b: T, just: J) -> Option<MergeInfo<T, L>> {
        let prefer_a = self.prefer_a_by_uses(a, b);
        let r = self.merge_with(a, b, true, prefer_a);
        if r.is_some() {
            self.uf.record_proof_edge(a, b, just);
        }
        r
    }

    /// Justified counterpart of [`Self::merge_directed_with`]: the caller
    /// computed its own survivor policy (`--union-by`).
    pub fn merge_justified_directed_with(
        &mut self,
        a: T,
        b: T,
        prefer_a: bool,
        just: J,
    ) -> Option<MergeInfo<T, L>> {
        let r = self.merge_with(a, b, true, prefer_a);
        if r.is_some() {
            self.uf.record_proof_edge(a, b, just);
        }
        r
    }

    /// Explain why `a ≡ b` by walking the proof tree (production's surface).
    pub fn explain(&self, a: T, b: T, buf: &mut crate::union_find::ProofBuf<T, J>) -> bool {
        self.uf.explain(a, b, buf)
    }

    /// Read-only proof-parent forest for an Euler-tour batch index.
    pub fn proof_parent(&self) -> Option<&crate::VecI<T, T::Index, TRACK>> {
        self.uf.proof_parent()
    }

    /// Extract a proof using an LCA obtained from [`Self::proof_parent`].
    pub fn explain_with_lca(
        &self,
        a: T,
        b: T,
        lca: T,
        buf: &mut crate::union_find::ProofBuf<T, J>,
    ) -> bool {
        self.uf.explain_with_lca(a, b, lca, buf)
    }
}

// prod-parity: the consumer's adapter token derives `Debug` and bundles this
// one; manual because deriving inside `verus!{}` is unsupported.
impl core::fmt::Debug for EClassesToken {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("EClassesToken")
            .field("entries", &self.entries)
            .field("reprs", &self.reprs)
            .field("uf", &self.uf)
            .field("uses", &self.uses)
            .field("pool", &self.pool)
            .finish()
    }
}

// Production-surface parity (the pre-swap class layer shipped Default).
impl<T, L, N, J, const TRACK: bool, const PROOFS: bool> Default
    for EClasses<T, L, N, J, TRACK, PROOFS>
where
    T: DenseId,
    L: DenseId,
    N: DenseId + Tagged + core::default::Default,
    J: Tagged + Copy + core::default::Default,
{
    fn default() -> Self {
        Self::new()
    }
}
