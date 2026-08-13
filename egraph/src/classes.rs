// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Equivalence classes with integrated union-find and parent use-lists.
//!
//! Combines circular linked lists (for class iteration) with a union-find
//! (for fast canonical representative lookup). Each representative owns a
//! use-list tracking which e-nodes reference it as a child.
//!
//! ## The class ring is the verified `CircularList`
//!
//! The per-node ring (`next` pointers partitioning nodes into classes) is
//! **not** hand-rolled here — it is `containers::CircularList`, whose
//! disjoint-ring partition invariant and O(1) `splice` merge are machine-checked
//! (`containers-verus/src/circular_list.rs`). This module supplies only the
//! e-graph-specific *payload* riding in each ring cell: the class's sparse-set
//! `repr_id`, present on a live representative and absent once absorbed.
//!
//! ### Why `Opt<T::Index>` is the payload, and why the layout is unchanged
//!
//! The old hand-rolled `EClassEntry<T> { next: T, repr_stored }` was 12 bytes at
//! 31-bit ids: a 4-byte `next` word whose spare MSB carried the semi-persistence
//! **capture** bit, plus an 8-byte `BoolTagged<u32>` holding the repr key and its
//! **presence** bit. `CircularList<Opt<T::Index>, T, TRACK>` stores exactly the
//! same two fields — `CircularNodeRepr { next_repr: T::Repr, payload: Opt<..> }`
//! — with the same two bits in the same two places: the capture bit in `next`'s
//! spare MSB (the ring owns it, via `T: DenseId: Tagged`), the presence bit in
//! the payload's own tag word (`Opt` owns it). Separate fields, so they cannot
//! collide — the split `opt.rs`'s module doc prescribes. A `size_of` assertion
//! below pins the 12 bytes so a future layout change cannot regress it silently.

use crate::containers::DenseId;
use crate::containers::IndexLike;
use crate::containers::circular_list::{CircularList, CircularListToken};
use crate::containers::list::{ListArena, ListArenaToken};
use crate::containers::sparse_set::{SparseSet, SparseSetToken};
use crate::containers::{self, ShrinkPolicy, VecToken};
use crate::containers::{Opt, Tagged};
use crate::union_find::{Justification, ProofBuf, UnionFind, UnionFindToken};

/// The class ring: one cell per node, carrying its ring successor plus the
/// class's sparse-set key (`Opt::none()` once the class has been absorbed).
///
/// `T` is both the payload-cell index type and the ring's id type, so the ring's
/// storage vector is indexed by `T::Index` (4 bytes at 31-bit ids) — matching
/// what the old `VecI<EClassEntry<T>, T::Index>` did, and keeping each captured
/// write in the semi-persistent diff log at `(cell, T::Index)` rather than
/// `(cell, usize)`.
type ClassRing<T, const TRACK: bool> = CircularList<Opt<<T as DenseId>::Index>, T, TRACK>;

// ---------------------------------------------------------------------------
// ClassData — per-class payload in the `reprs` sparse set
// ---------------------------------------------------------------------------

/// Per-class data stored in the `reprs` sparse set, keyed by `repr_id`.
///
/// - `use_list` — the class's use-list id (parents referencing this class).
/// - `min_row` — a nullable **row number** (`Option<T::Index>`) into `EClasses::min_pool` of
///   this class's row of per-completion-op minimum-monomial nodes (design "the column → op
///   reference array"). `None` means "no row: the class holds no completion monomial yet".
///   It is not a node-derived id, so absence is `None` rather than `T::default()` (id 0 is a
///   real node, so an id-typed sentinel would be unsound). The pool cells, which *are* node
///   ids, use `Opt<T>` (niche) instead. A
///   row's column `k` is the class's `≫_f`-least monomial node for completion op `k`, or
///   `None` if absent. Maintained O(1) on merge by `EGraph` (which has the op→column map and
///   the node access `monomial_cmp` needs); `EClasses` only stores and shuttles the pool.
/// - `atomic` — whether the class is referenced as a child of some node, making the size-1
///   monomial `{classid}` a real term and the class's normal-form representative (§9a). Set
///   on `add_use` and on gaining a non-completion node, OR-combined on merge. The completion
///   rule RHS is `{classid}` if `atomic`, else the relevant column's monomial.
///
/// One slot for all three facts, so they cannot desync and roll back together. The `min_row`
/// number rolls back with the sparse-set entry; the pool row it points at rolls back with the
/// pool's own `mark`/`restore` (they are marked together).
#[derive(Clone, Copy)]
pub struct ClassData<L: DenseId, T: DenseId> {
    pub use_list: L,
    /// This class's **row number** in `EClasses::min_pool`, or `None` if no row is allocated
    /// (the class holds no completion monomial yet). Multiply by `min_width` for the base pool
    /// offset; the pool itself stays `usize`-indexed, because its length is
    /// `rows * min_width` and a product of two populations is bounded by neither.
    ///
    /// A row *number*, not that offset, is what makes `T::Index` the right width here rather
    /// than a new capacity cap. Rows are allocated one per class and never freed, so the row
    /// count is bounded by the class count, which is bounded by `T`'s id capacity — the same
    /// bound `T::Index` is sized for. Storing the offset instead would tie this field to the
    /// *pool's* population, which `T::Index` genuinely cannot bound.
    ///
    /// This is stored per class, so the width is not free: at 31-bit ids the packed `Repr`
    /// below is 12 bytes to a `usize` offset's 16.
    pub min_row: Option<T::Index>,
    pub atomic: bool,
    _t: core::marker::PhantomData<T>,
}

// `Tagged` by delegating the CAPTURE tag to the first field (`use_list`), the same idiom as
// `ListNode` in `containers/list.rs`. `min_row` is stored as `(row, present)`: the row number
// at `T::Index` plus a presence bool, rather than `Option<T::Index>`, because `T::Index` is a
// plain integer with no spare niche — an `Option` of it would spend a whole word on the
// discriminant and undo the narrowing. Both are just `Copy` data in the `Repr` tuple; the
// capture bit lives only on `use_list`, element 0.
impl<L: DenseId, T: DenseId> Tagged for ClassData<L, T> {
    type Repr = (L::Repr, T::Index, bool, bool);

    fn into_repr(self) -> Self::Repr {
        let (row, present) = match self.min_row {
            Some(r) => (r, true),
            None => (<T::Index as IndexLike>::min(), false),
        };
        (self.use_list.into_repr(), row, present, self.atomic)
    }
    fn from_repr(r: &Self::Repr) -> Self {
        Self {
            use_list: L::from_repr(&r.0),
            min_row: if r.2 { Some(r.1) } else { None },
            atomic: r.3,
            _t: core::marker::PhantomData,
        }
    }
    fn tag(r: &Self::Repr) -> bool {
        L::tag(&r.0)
    }
    fn set_tag(r: &mut Self::Repr) {
        L::set_tag(&mut r.0);
    }
    fn clear_tag(r: &mut Self::Repr) {
        L::clear_tag(&mut r.0);
    }
}

impl<L: DenseId, T: DenseId> Default for ClassData<L, T> {
    fn default() -> Self {
        Self {
            use_list: L::default(),
            min_row: None,
            atomic: false,
            _t: core::marker::PhantomData,
        }
    }
}

// ---------------------------------------------------------------------------
// MergeInfo — returned by merge, carries absorbed use-list for rebuild
// ---------------------------------------------------------------------------

pub struct MergeInfo<T: DenseId, L> {
    pub survivor: T,
    pub absorbed: T,
    pub absorbed_uses: L,
    /// The absorbed class's min-monomial pool row number (`None` if it had no row), so the
    /// caller can fold each column into the survivor's row (`EGraph` does the per-column
    /// `monomial_cmp`, §9a). The pool is append-only, so this row stays valid after the
    /// absorbed repr is removed from the sparse set.
    pub absorbed_min_row: Option<T::Index>,
    /// The absorbed class's `atomic` flag, OR-combined into the survivor's (§9a).
    pub absorbed_atomic: bool,
}

// ---------------------------------------------------------------------------
// EClasses
// ---------------------------------------------------------------------------

/// Equivalence classes with integrated union-find and parent use-lists.
///
/// - `T: DenseId` — node type (e.g. `ENodeId`)
/// - `L: DenseId` — use-list id type (e.g. `UseListId`)
/// - `N: DenseId` — use-list node id type (e.g. `UseNodeId`)
/// - `TRACK` — enable mark/restore
/// - `PROOFS` — enable proof tracking in union-find
pub struct EClasses<T: DenseId, L: DenseId, N: DenseId, const TRACK: bool, const PROOFS: bool> {
    /// The verified class ring (see the module doc). Was a hand-rolled
    /// `VecI<EClassEntry<T>, T::Index, TRACK>`; the layout is byte-identical.
    entries: ClassRing<T, TRACK>,
    reprs: SparseSet<
        ClassData<L, T>,
        T::Index,
        containers::InlineStore<ClassData<L, T>, T::Index>,
        TRACK,
    >,
    uf: UnionFind<T, TRACK, PROOFS>,
    uses: ListArena<T, L, N, TRACK>,
    /// Per-class min-monomial pool: flat rows of `min_width` completion columns, `min_row`
    /// (in `ClassData`) locates a class's row. `Opt<T>`: `Opt::none()` = the class holds no
    /// monomial for that column's op; `Opt::some(id)` is a real node id (id 0 included, no
    /// collision — the niche tag encodes None, not a reserved id). Stored in a `VecP`
    /// (out-of-line, `ParallelStore`) rather than `VecI`: `Opt` cannot sit in a bit-stealing
    /// `VecI` (it needs its own tag bit, which VecI would steal — see containers `tagged.rs`),
    /// but `VecP` steals nothing, so `Opt`'s niche encoding is safe and compact here.
    /// Semi-persistent: rows roll back with the pool's own `mark`/`restore`.
    ///
    /// Indexed at `usize`, unlike `min_row`'s `T::Index`: the pool's population is
    /// `rows * min_width`, a product of the class count and the completion-op count, and
    /// `T::Index` bounds only the first factor. Narrowing the pool index would cap the product
    /// at the class capacity, i.e. forbid more than one completion column at a full e-graph.
    min_pool: containers::VecP<Opt<T>, usize, TRACK>,
    /// Fixed row width = number of completion ops (`nb_completion`). Set once by
    /// `set_min_width` before the first row is allocated; 0 until then (no completion ops).
    min_width: usize,
}

impl<T: DenseId, L: DenseId, N: DenseId, const TRACK: bool, const PROOFS: bool> Default
    for EClasses<T, L, N, TRACK, PROOFS>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T: DenseId, L: DenseId, N: DenseId, const TRACK: bool, const PROOFS: bool>
    EClasses<T, L, N, TRACK, PROOFS>
{
    pub fn new() -> Self {
        Self {
            entries: ClassRing::new(),
            reprs: SparseSet::new_inline(),
            uf: UnionFind::new(),
            uses: ListArena::new(),
            min_pool: containers::VecP::new(),
            min_width: 0,
        }
    }

    /// Set the min-monomial pool row width (`nb_completion`). Called once by `EGraph` before
    /// any completion monomial is recorded. Rejects a change after rows exist (declare-before-
    /// build: fixed-width rows cannot be widened in place). A no-op if the width is unchanged.
    pub fn set_min_width(&mut self, width: usize) {
        if self.min_width == width {
            return;
        }
        assert!(
            self.min_pool.is_empty(),
            "min-monomial pool width fixed at {} once rows exist; cannot change to {width} \
             (declare all AC/ACI ops before building terms)",
            self.min_width
        );
        self.min_width = width;
    }

    /// The min-monomial pool row width (`nb_completion`), for the merge fold's column loop.
    pub fn min_width(&self) -> usize {
        self.min_width
    }

    /// Ensure this class has a pool row, allocating one (all-`Opt::none()` cells) on first use.
    /// Returns the row *number* (what `min_row` stores); multiply by `min_width` for the base
    /// pool offset.
    fn ensure_min_row(&mut self, repr_id: T::Index) -> T::Index {
        let mut data = self.reprs.get(repr_id);
        if let Some(row) = data.min_row {
            return row;
        }
        debug_assert!(
            self.min_width > 0,
            "set_min_width must precede row allocation"
        );
        // Rows are appended `min_width` cells at a time and never freed, so the pool length is
        // always an exact multiple of the width and this division is the row's number.
        debug_assert_eq!(self.min_pool.len() % self.min_width, 0);
        // One row per class, so the row count cannot pass the class count, which cannot pass
        // `T`'s id capacity — the bound `T::Index` is sized for. Spelled as a checked
        // conversion anyway: that argument is what makes the narrowing safe, and an `as` cast
        // would bury it and alias a row onto another class's if it ever stopped holding.
        let row = <T::Index as IndexLike>::try_from_usize(self.min_pool.len() / self.min_width)
            .expect("min-monomial rows are one per class, so a row number fits the id index");
        for _ in 0..self.min_width {
            self.min_pool
                .try_push(Opt::none())
                .expect("bounded by the node/class id space the mint paths already check");
        }
        data.min_row = Some(row);
        self.reprs.set(repr_id, data);
        row
    }

    /// Base pool offset of row number `row`.
    ///
    /// `row * min_width` leaves both factors' widths — the product is bounded by the pool's
    /// population, not by either the class count or the column count — so it is computed at
    /// `usize`, the pool's own index type, and never narrowed back.
    #[inline]
    fn min_row_base(&self, row: T::Index) -> usize {
        row.as_usize() * self.min_width
    }

    pub fn len(&self) -> T::Index {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn num_classes(&self) -> T::Index {
        self.reprs.len()
    }

    pub fn add_singleton(&mut self, id: T) -> T::Index {
        self.uf.make_set(id);
        let list_id = self
            .uses
            .try_new_list()
            .expect("bounded by the node/class id space the mint paths already check");
        // No pool row yet (`min_row` is `Opt::none()`): a fresh class holds no completion
        // monomial until its op's column is seeded by `EGraph` (which knows the node's op).
        // Not yet referenced as a child, so not atomic (§9a).
        let repr_id = self
            .reprs
            .try_add(ClassData {
                use_list: list_id,
                min_row: None,
                atomic: false,
                _t: core::marker::PhantomData,
            })
            .expect("bounded by the node/class id space the mint paths already check");
        // The ring allocates the node's cell as its own singleton class
        // (self-loop `next`), carrying the class key as the payload. Its id is
        // the pre-push length, which `id` must equal — the caller allocates node
        // ids densely and in order, the same contract the old `push` relied on.
        let ring_id = self
            .entries
            .try_add_singleton(Opt::some(repr_id))
            .expect("bounded by the node/class id space the mint paths already check");
        debug_assert_eq!(
            ring_id.to_usize(),
            id.to_usize(),
            "add_singleton: node ids must be dense and allocated in order"
        );
        repr_id
    }

    // -- Use-list management ------------------------------------------------

    /// Record that `parent_node` uses the class at `child_repr` as a child. Any such
    /// reference makes the size-1 monomial `{child_repr}` a real term, so the class
    /// becomes `atomic` (its completion rule RHS, §9a).
    pub fn add_use(&mut self, child_repr: T::Index, parent_node: T) {
        let mut data = self.reprs.get(child_repr);
        self.uses
            .try_append(data.use_list, parent_node)
            .expect("bounded by the node/class id space the mint paths already check");
        if !data.atomic {
            data.atomic = true;
            self.reprs.set(child_repr, data);
        }
    }

    /// Get the use-list id for a representative (for saving before merge).
    pub fn use_list_id(&self, repr_id: T::Index) -> L {
        self.reprs.get(repr_id).use_list
    }

    /// Number of parents in a representative's use-list, O(1) (cached in the list header).
    /// Used to choose the merge survivor by parent count (the larger list survives, so the
    /// smaller absorbed set is what gets recanonicalized).
    ///
    /// Returns `usize`, widening from the arena's own `N::Index`. Widening is always sound
    /// and this is the right place for it: the value leaves the container here and is only
    /// ever compared against another one (`merge`, below), so nothing downstream stores it
    /// and nothing pays for the extra bytes. Narrowing would be the error — a `as u32` on a
    /// config whose `Index` is wider truncates a real count into a smaller one and picks
    /// the wrong merge survivor, silently.
    ///
    /// `ListArena::len` itself is `N::Index`-wide, which is what removed the 4-billion cap
    /// on a single use-list: the count is bounded by the node arena's population, so it
    /// belongs in that arena's index type and scales with the config.
    pub fn use_list_len(&self, repr_id: T::Index) -> usize {
        self.uses.len(self.reprs.get(repr_id).use_list).as_usize()
    }

    /// The class's current minimum-monomial node for completion column `col` (the completion
    /// rule RHS for that op when the class is not `atomic`, §9a), or `None` if the class holds
    /// no monomial of that op. `col` is the op's completion column (`EGraph` supplies it via
    /// the registry `completion_column`).
    pub fn min_monomial(&self, repr_id: T::Index, col: usize) -> Option<T> {
        let row = self.reprs.get(repr_id).min_row?;
        debug_assert!(col < self.min_width, "completion column out of range");
        self.min_pool.get(self.min_row_base(row) + col).to_option()
    }

    /// Whether the class is referenced as a child of some node, making `{classid}` its
    /// normal-form representative (§9a).
    pub fn atomic(&self, repr_id: T::Index) -> bool {
        self.reprs.get(repr_id).atomic
    }

    /// Set the class's minimum-monomial node for completion column `col`. Allocates the
    /// class's pool row on first use. Called by `EGraph` after a merge, once it has compared
    /// the two classes' minima with `monomial_cmp`.
    pub fn set_min_monomial(&mut self, repr_id: T::Index, col: usize, node: T) {
        debug_assert!(col < self.min_width, "completion column out of range");
        let row = self.ensure_min_row(repr_id);
        let base = self.min_row_base(row);
        self.min_pool.set(base + col, Opt::some(node));
    }

    /// Read completion column `col` of a row number (as carried in `MergeInfo`), for the merge
    /// fold. Returns `None` if the row is absent (`None`) or the column is empty.
    pub fn min_monomial_at_row(&self, row: Option<T::Index>, col: usize) -> Option<T> {
        let base = self.min_row_base(row?);
        debug_assert!(col < self.min_width, "completion column out of range");
        self.min_pool.get(base + col).to_option()
    }

    /// Mark the class `atomic` (it has a non-AC node, so `{classid}` is its RHS, §9a).
    pub fn set_atomic(&mut self, repr_id: T::Index) {
        let mut data = self.reprs.get(repr_id);
        if !data.atomic {
            data.atomic = true;
            self.reprs.set(repr_id, data);
        }
    }

    /// Iterate the use-list of a representative (parent nodes).
    pub fn iter_uses(&self, repr_id: T::Index) -> impl Iterator<Item = T> + '_ {
        let list_id = self.reprs.get(repr_id).use_list;
        self.uses.iter(list_id)
    }

    /// Direct access to the use-list arena (for iterating by list id).
    pub fn uses(&self) -> &ListArena<T, L, N, TRACK> {
        &self.uses
    }

    /// Splice absorbed class's use-list into survivor's.
    /// Takes list ids directly (absorbed repr may already be removed).
    pub fn splice_uses(&mut self, survivor_list: L, absorbed_list: L) {
        self.uses.splice(survivor_list, absorbed_list);
    }

    // -- Find ---------------------------------------------------------------

    pub fn find(&mut self, x: T) -> T {
        self.uf.find(x)
    }

    pub fn find_const(&self, x: T) -> T {
        self.uf.find_const(x)
    }

    pub fn repr_id(&self, idx: T) -> Option<T::Index> {
        self.entries.payload_of(idx).to_option()
    }

    /// The class key stored in `idx`'s ring cell **ignoring the presence bit** —
    /// valid for an absorbed class, whose key is kept in place so the merge path
    /// can still reach its `ClassData` before removing it from the sparse set.
    fn repr_id_unchecked(&self, idx: T) -> T::Index {
        self.entries.payload_of(idx).get_unchecked()
    }

    // -- Merge (steps 1-2 only: UF + circular list, NOT use-list splice) ----

    /// Merge two classes. Returns survivor, absorbed, and the absorbed class's
    /// use-list id (needed by rebuild to iterate parents before splicing).
    pub fn merge(&mut self, a: T, b: T) -> Option<MergeInfo<T, L>> {
        let (survivor, absorbed) = self.uf.union(a, b)?;
        let absorbed_repr = self.repr_id_unchecked(absorbed);
        let absorbed_data = self.reprs.get(absorbed_repr);
        self.splice_classes((survivor, absorbed));
        Some(MergeInfo {
            survivor,
            absorbed,
            absorbed_uses: absorbed_data.use_list,
            absorbed_min_row: absorbed_data.min_row,
            absorbed_atomic: absorbed_data.atomic,
        })
    }

    pub fn merge_justified(
        &mut self,
        a: T,
        b: T,
        just: Justification<T>,
    ) -> Option<MergeInfo<T, L>> {
        let (survivor, absorbed) = self.uf.union_justified(a, b, just)?;
        let absorbed_repr = self.repr_id_unchecked(absorbed);
        let absorbed_data = self.reprs.get(absorbed_repr);
        self.splice_classes((survivor, absorbed));
        Some(MergeInfo {
            survivor,
            absorbed,
            absorbed_uses: absorbed_data.use_list,
            absorbed_min_row: absorbed_data.min_row,
            absorbed_atomic: absorbed_data.atomic,
        })
    }

    /// Whether `find(a)`'s class has at least as many parents as `find(b)`'s. The directed
    /// merges below keep the larger-use-list class as survivor, so the smaller class is the
    /// one absorbed and recanonicalized.
    fn prefer_a_by_uses(&self, a: T, b: T) -> bool {
        let ra = self.uf.find_const(a);
        let rb = self.uf.find_const(b);
        let len_a = self.repr_id(ra).map_or(0, |r| self.use_list_len(r));
        let len_b = self.repr_id(rb).map_or(0, |r| self.use_list_len(r));
        len_a >= len_b
    }

    /// Like [`merge`], but selects the survivor by parent-count (larger use-list survives)
    /// instead of by union-find rank. Reduces post-merge recanonicalization work, at the cost
    /// of union-by-rank's height optimality (see `UnionFind::union_directed`).
    pub fn merge_directed(&mut self, a: T, b: T) -> Option<MergeInfo<T, L>> {
        let prefer_a = self.prefer_a_by_uses(a, b);
        let (survivor, absorbed) = self.uf.union_directed(a, b, prefer_a)?;
        let absorbed_repr = self.repr_id_unchecked(absorbed);
        let absorbed_data = self.reprs.get(absorbed_repr);
        self.splice_classes((survivor, absorbed));
        Some(MergeInfo {
            survivor,
            absorbed,
            absorbed_uses: absorbed_data.use_list,
            absorbed_min_row: absorbed_data.min_row,
            absorbed_atomic: absorbed_data.atomic,
        })
    }

    /// Justified counterpart of [`merge_directed`].
    pub fn merge_justified_directed(
        &mut self,
        a: T,
        b: T,
        just: Justification<T>,
    ) -> Option<MergeInfo<T, L>> {
        let prefer_a = self.prefer_a_by_uses(a, b);
        let (survivor, absorbed) = self.uf.union_justified_directed(a, b, just, prefer_a)?;
        let absorbed_repr = self.repr_id_unchecked(absorbed);
        let absorbed_data = self.reprs.get(absorbed_repr);
        self.splice_classes((survivor, absorbed));
        Some(MergeInfo {
            survivor,
            absorbed,
            absorbed_uses: absorbed_data.use_list,
            absorbed_min_row: absorbed_data.min_row,
            absorbed_atomic: absorbed_data.atomic,
        })
    }

    /// Merge the survivor's and absorbed class's rings, and mark the absorbed
    /// class's key absent.
    ///
    /// The ring surgery is the verified `CircularList::splice`: it swaps the two
    /// `next` pointers, which is exactly what the previous hand-rolled pair of
    /// full-cell writes did — the same two stores, but with the disjoint-ring
    /// partition invariant proved to be preserved rather than assumed. Each
    /// class's `repr_id` payload stays in its own cell (`splice` provably leaves
    /// every payload untouched), so the survivor needs no payload write at all;
    /// only the absorbed cell's presence bit is cleared.
    ///
    /// The presence-bit clear rides through the splice (`splice_absorb`) rather
    /// than following it as a separate `set_payload`. Folding it in was once
    /// measured as no faster (`examples/splicesplit.rs`: 5.58 vs 5.59 µs over 10k
    /// merges) and the payload-carrying form was reverted — but that measurement
    /// was **untracked**, where the third write is a plain store LLVM can forward.
    /// This ring is tracked, and there every `set_index` runs the capture protocol,
    /// so a third write is a third tag test (plus a diff-log push on the first
    /// write to a cell). Given production's identical write count the verified ring
    /// is ~16% faster; given one extra write it read +2.5% instead.
    fn splice_classes(&mut self, (survivor, absorbed): (T, T)) {
        // One read of the absorbed cell serves both consumers: the sparse-set key
        // `remove` needs, and the payload the splice stores back with the presence
        // bit cleared. (`Opt::set_none` preserves the value, so the key also stays
        // readable through `repr_id_unchecked` afterwards.)
        let mut absorbed_payload = self.entries.payload_of(absorbed);
        let abs_repr = absorbed_payload.get_unchecked();
        absorbed_payload.set_none();

        // Distinct rings is `splice_absorb`'s precondition. Union-find has just
        // told us these are two different classes, which is exactly that — the
        // same discipline the hand-rolled version relied on silently; debug
        // builds now check it (`CircularList::debug_check_different_rings`).
        // Two cell writes per merge, matching the pre-swap hand-rolled ring.
        self.entries
            .splice_absorb(survivor, absorbed, absorbed_payload);

        self.reprs.remove(abs_repr);
    }

    // -- Proofs -------------------------------------------------------------

    pub fn explain(&self, a: T, b: T, buf: &mut ProofBuf<T>) -> bool {
        self.uf.explain(a, b, buf)
    }

    // -- Iteration ----------------------------------------------------------

    /// Iterate `start_idx`'s class: every node in its ring, starting at
    /// `start_idx` and wrapping once. The verified `RingIter` — proven to visit
    /// exactly the ring's nodes, each once, in `next`-pointer order — replaces
    /// the hand-rolled `ClassIter`; its exec body is the same "yield, step,
    /// stop when back at start" loop.
    pub fn iter_class(&self, start_idx: T) -> ClassIter<'_, T, TRACK> {
        self.entries.iter_class(start_idx)
    }

    // -- Semi-persistence ---------------------------------------------------

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> EClassesToken {
        EClassesToken {
            // entries stays on the guarded core: CircularList has no try_mark yet
            // (total-api plan, phase-3 deferrals).
            entries: self.entries.mark(shrink),
            reprs: self
                .reprs
                .try_mark(shrink)
                .expect("mark: frame depth is bounded by the saturation driver"),
            uf: self.uf.mark(shrink),
            uses: self
                .uses
                .try_mark(shrink)
                .expect("mark: frame depth is bounded by the saturation driver"),
            min_pool: self
                .min_pool
                .try_mark(shrink)
                .expect("mark: frame depth is bounded by the saturation driver"),
        }
    }

    pub fn restore(&mut self, token: EClassesToken) {
        // Guarded core: CircularList try_restore is a phase-3 deferral.
        self.entries.restore(token.entries);
        // Guarded core: SparseSet try_restore waits on snapshot-wf archival
        // (total-api plan, phase-3 deferrals).
        self.reprs.restore(token.reprs);
        self.uf.restore(token.uf);
        self.uses
            .try_restore(token.uses)
            .expect("restore: token minted by this container's own mark");
        self.min_pool
            .try_restore(token.min_pool)
            .expect("restore: token minted by this container's own mark");
    }
}

#[derive(Clone, Copy, Debug)]
pub struct EClassesToken {
    entries: CircularListToken,
    reprs: SparseSetToken,
    uf: UnionFindToken,
    min_pool: VecToken,
    uses: ListArenaToken,
}

// ---------------------------------------------------------------------------
// Iterators
// ---------------------------------------------------------------------------

/// Class-ring iterator: the verified `RingIter`, yielding `T` node ids in ring
/// order. Kept under this name so callers (and `iter_class`'s signature) are
/// unchanged from the hand-rolled version.
pub type ClassIter<'a, T, const TRACK: bool> =
    containers::circular_list::RingIter<'a, Opt<<T as DenseId>::Index>, T, TRACK>;

// The ring cell must stay at production's 12 bytes at 31-bit ids: a 4-byte
// `next` word (capture bit in its spare MSB) plus an 8-byte `BoolTagged<u32>`
// payload (repr key + presence bit). See the module doc; this is the memory
// budget the verified ring had to match, so it is asserted, not assumed.
//
// The payload word is written `<ENodeId as DenseId>::Index`, not `u32`: the cell's
// width follows the id family by construction (`ClassRing<T, TRACK>` above), and
// spelling the word out here would leave an assertion that keeps passing while
// silently describing a different type than the one `ClassRing` instantiates.
// `ENodeId` is the 31-bit config, so the expected size is still 12.
#[cfg(target_pointer_width = "64")]
const _: () = assert!(
    core::mem::size_of::<
        containers::circular_list::CircularNodeRepr<
            Opt<<crate::id::ENodeId as DenseId>::Index>,
            crate::id::ENodeId,
        >,
    >() == 12,
    "e-class ring cell must stay 12 bytes at 31-bit ids"
);

// The per-class slot: a use-list head plus `min_row` plus two flags. Asserted because
// `min_row`'s width is the whole reason it stores a row *number* rather than a pool offset
// (see `ClassData::min_row`): at 31-bit ids a `usize` offset made this 16 bytes, and the
// row number packs it into 12 alongside the head word and both bools. Spelled through the
// id types rather than as `(u32, u32, bool, bool)` so the assertion cannot keep passing
// while describing a type `EClasses` no longer instantiates.
//
// This is one slot per class, so the 4 bytes are 4 per class — the reason the narrowing is
// worth stating as a fact instead of a comment. Reintroducing a pointer-width offset here,
// or wrapping the row in an `Option<T::Index>` (no niche, so a whole extra word), fails
// this and not any behavioural test.
#[cfg(target_pointer_width = "64")]
const _: () = assert!(
    core::mem::size_of::<<ClassData<crate::id::UseListId, crate::id::ENodeId> as Tagged>::Repr>()
        == 12,
    "per-class slot must stay 12 bytes at 31-bit ids"
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{ENodeId, UseListId, UseNodeId};

    type EC = EClasses<ENodeId, UseListId, UseNodeId, false, false>;

    #[test]
    fn eclasses_with_use_lists() {
        let mut ec = EC::new();

        // Create 6 nodes: a, b, c, f_a, f_b, g_ab
        let a = ENodeId::new(0);
        let b = ENodeId::new(1);
        let c = ENodeId::new(2);
        let f_a = ENodeId::new(3);
        let f_b = ENodeId::new(4);
        let g_ab = ENodeId::new(5);

        for &id in &[a, b, c, f_a, f_b, g_ab] {
            ec.add_singleton(id);
        }
        eprintln!("Created 6 singletons, {} classes", ec.num_classes());

        // f(a) uses a as child, f(b) uses b, g(a,b) uses both a and b
        let repr_a = ec.repr_id(a).unwrap();
        let repr_b = ec.repr_id(b).unwrap();
        ec.add_use(repr_a, f_a);
        ec.add_use(repr_a, g_ab);
        ec.add_use(repr_b, f_b);
        ec.add_use(repr_b, g_ab);

        eprintln!("\nUse-list of a (repr {:?}):", repr_a);
        for parent in ec.iter_uses(repr_a) {
            eprintln!("  {:?}", parent);
        }
        eprintln!("Use-list of b (repr {:?}):", repr_b);
        for parent in ec.iter_uses(repr_b) {
            eprintln!("  {:?}", parent);
        }

        assert_eq!(ec.iter_uses(repr_a).count(), 2); // f_a, g_ab
        assert_eq!(ec.iter_uses(repr_b).count(), 2); // f_b, g_ab

        // Merge a and b — this does UF + circular list, NOT use-list splice
        let m = ec.merge(a, b).unwrap();
        let (survivor, absorbed) = (m.survivor, m.absorbed);
        eprintln!(
            "\nMerged a,b → survivor={:?}, absorbed={:?}",
            survivor, absorbed
        );
        eprintln!(
            "find(a)={:?}, find(b)={:?}",
            ec.find_const(a),
            ec.find_const(b)
        );
        assert_eq!(ec.find_const(a), ec.find_const(b));

        // Class iteration works (circular list was spliced)
        let class: Vec<_> = ec.iter_class(survivor).collect();
        eprintln!("Class of survivor: {:?}", class);
        assert_eq!(class.len(), 2);

        // Use-lists are still separate (not spliced yet)
        let surv_repr = ec.repr_id(survivor).unwrap();
        eprintln!("\nBefore splice_uses:");
        eprintln!(
            "  survivor uses: {:?}",
            ec.iter_uses(surv_repr).collect::<Vec<_>>()
        );

        // Now simulate what rebuild would do: walk absorbed's use-list, then splice
        // (In real rebuild, we'd recanonize each parent here)
        let abs_repr = ec.repr_id(absorbed);
        eprintln!(
            "  absorbed repr_id: {:?} (None = already removed)",
            abs_repr
        );

        // The absorbed repr was removed from the sparse set during merge.
        // But the use-list id is still valid in the arena.
        // We need to get the absorbed list id before merge, or store it.
        // For this test, let's show the pattern with a fresh setup:

        eprintln!("\n--- Fresh setup to show full splice pattern ---");
        let mut ec2 = EC::new();
        let x = ENodeId::new(0);
        let y = ENodeId::new(1);
        let px = ENodeId::new(2); // parent of x
        let py = ENodeId::new(3); // parent of y
        let pxy = ENodeId::new(4); // parent of both
        for &id in &[x, y, px, py, pxy] {
            ec2.add_singleton(id);
        }
        let rx = ec2.repr_id(x).unwrap();
        let ry = ec2.repr_id(y).unwrap();
        ec2.add_use(rx, px);
        ec2.add_use(rx, pxy);
        ec2.add_use(ry, py);
        ec2.add_use(ry, pxy);

        // Save absorbed list id before merge
        // (now returned by merge via MergeInfo)

        eprintln!("Before merge:");
        eprintln!("  x uses: {:?}", ec2.iter_uses(rx).collect::<Vec<_>>());
        eprintln!("  y uses: {:?}", ec2.iter_uses(ry).collect::<Vec<_>>());

        let m2 = ec2.merge(x, y).unwrap();
        let surv = m2.survivor;
        let absorbed_list = m2.absorbed_uses;
        let surv_repr = ec2.repr_id(surv).unwrap();

        eprintln!("\nAfter merge (before splice_uses):");
        eprintln!(
            "  survivor uses: {:?}",
            ec2.iter_uses(surv_repr).collect::<Vec<_>>()
        );
        eprintln!(
            "  absorbed list (via saved id): {:?}",
            ec2.uses.iter(absorbed_list).collect::<Vec<_>>()
        );

        // Now splice: absorbed's use-list into survivor's
        let surv_list = ec2.reprs.get(surv_repr).use_list;
        ec2.uses.splice(surv_list, absorbed_list);

        eprintln!("\nAfter splice_uses:");
        let all_uses: Vec<_> = ec2.iter_uses(surv_repr).collect();
        eprintln!("  survivor uses: {:?}", all_uses);
        assert_eq!(all_uses.len(), 4); // px, pxy, py, pxy
        eprintln!(
            "  absorbed list (should be empty): {:?}",
            ec2.uses.iter(absorbed_list).collect::<Vec<_>>()
        );

        eprintln!("\n✓ All checks passed");
    }

    #[test]
    fn use_list_len_is_o1_and_matches_iteration() {
        let mut ec = EC::new();
        let x = ENodeId::new(0);
        let p0 = ENodeId::new(1);
        let p1 = ENodeId::new(2);
        let p2 = ENodeId::new(3);
        for &id in &[x, p0, p1, p2] {
            ec.add_singleton(id);
        }
        let rx = ec.repr_id(x).unwrap();
        assert_eq!(ec.use_list_len(rx), 0);
        ec.add_use(rx, p0);
        ec.add_use(rx, p1);
        ec.add_use(rx, p2);
        assert_eq!(ec.use_list_len(rx), 3);
        assert_eq!(ec.use_list_len(rx), ec.iter_uses(rx).count());
    }

    #[test]
    fn merge_directed_keeps_larger_use_list_as_survivor() {
        // `big` has two parents, `small` has one; `merge_directed` must keep `big` as the
        // survivor regardless of argument order, so the smaller class is the one absorbed.
        let mut ec = EC::new();
        let big = ENodeId::new(0);
        let small = ENodeId::new(1);
        let pb0 = ENodeId::new(2);
        let pb1 = ENodeId::new(3);
        let ps0 = ENodeId::new(4);
        for &id in &[big, small, pb0, pb1, ps0] {
            ec.add_singleton(id);
        }
        let rb = ec.repr_id(big).unwrap();
        let rs = ec.repr_id(small).unwrap();
        ec.add_use(rb, pb0);
        ec.add_use(rb, pb1);
        ec.add_use(rs, ps0);
        assert_eq!(ec.use_list_len(rb), 2);
        assert_eq!(ec.use_list_len(rs), 1);

        // Pass the smaller class first to prove order-independence.
        let m = ec.merge_directed(small, big).unwrap();
        assert_eq!(m.survivor, big, "larger use-list should survive");
        assert_eq!(m.absorbed, small);
        assert_eq!(ec.find_const(small), big);
    }
}
