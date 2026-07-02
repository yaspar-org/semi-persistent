// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Equivalence classes with integrated union-find and parent use-lists.
//!
//! Combines circular linked lists (for class iteration) with a union-find
//! (for fast canonical representative lookup). Each representative owns a
//! use-list tracking which e-nodes reference it as a child.

use crate::containers::DenseId;
use crate::containers::list::{ListArena, ListArenaToken};
use crate::containers::sparse_set::{SparseSet, SparseSetToken};
use crate::containers::{self, ShrinkPolicy, VecToken};
use crate::containers::{Opt, Tagged};
use crate::union_find::{Justification, ProofBuf, UnionFind, UnionFindToken};

// ---------------------------------------------------------------------------
// EClassEntry — per-node: next pointer in circular list + sparse set key
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub struct EClassEntry<T: DenseId> {
    pub next: T,
    repr_stored: <T::Index as Tagged>::Repr,
}

// Filler for `resize_default` during restore; never observed. Routes the id
// through `new`/`into_repr` rather than fabricating a raw `Repr`.
impl<T: DenseId> Default for EClassEntry<T> {
    fn default() -> Self {
        Self::new(T::default(), T::Index::default())
    }
}

impl<T: DenseId> EClassEntry<T> {
    fn new(next: T, repr_id: T::Index) -> Self {
        Self {
            next,
            repr_stored: repr_id.into_repr(),
        }
    }

    pub fn repr_id(&self) -> Option<T::Index> {
        if T::Index::tag(&self.repr_stored) {
            None
        } else {
            Some(T::Index::from_repr(&self.repr_stored))
        }
    }

    fn repr_id_unchecked(&self) -> T::Index {
        T::Index::from_repr(&self.repr_stored)
    }

    fn set_absent(&mut self) {
        T::Index::set_tag(&mut self.repr_stored);
    }
}

impl<T: DenseId> Tagged for EClassEntry<T> {
    type Repr = (T::Repr, <T::Index as Tagged>::Repr);

    fn into_repr(self) -> Self::Repr {
        (self.next.into_repr(), self.repr_stored)
    }
    fn from_repr(s: &Self::Repr) -> Self {
        Self {
            next: T::from_repr(&s.0),
            repr_stored: s.1,
        }
    }
    fn tag(s: &Self::Repr) -> bool {
        T::tag(&s.0)
    }
    fn set_tag(s: &mut Self::Repr) {
        T::set_tag(&mut s.0);
    }
    fn clear_tag(s: &mut Self::Repr) {
        T::clear_tag(&mut s.0);
    }
}

// ---------------------------------------------------------------------------
// ClassData — per-class payload in the `reprs` sparse set
// ---------------------------------------------------------------------------

/// Per-class data stored in the `reprs` sparse set, keyed by `repr_id`.
///
/// - `use_list` — the class's use-list id (parents referencing this class).
/// - `min_row` — a nullable **plain offset** (`Option<usize>`) into `EClasses::min_pool` of
///   this class's row of per-completion-op minimum-monomial nodes (design "the column → op
///   reference array"). `None` means "no row: the class holds no completion monomial yet".
///   It is a pool offset, not a node-derived id, so it is a plain `Option<usize>` — not
///   `T::default()` (id 0 is a real node, so an id-typed sentinel would be unsound) and not an
///   id index type. The pool cells, which *are* node ids, use `Opt<T>` (niche) instead. A
///   row's column `k` is the class's `≫_f`-least monomial node for completion op `k`, or
///   `None` if absent. Maintained O(1) on merge by `EGraph` (which has the op→column map and
///   the node access `monomial_cmp` needs); `EClasses` only stores and shuttles the pool.
/// - `atomic` — whether the class is referenced as a child of some node, making the size-1
///   monomial `{classid}` a real term and the class's normal-form representative (§9a). Set
///   on `add_use` and on gaining a non-completion node, OR-combined on merge. The completion
///   rule RHS is `{classid}` if `atomic`, else the relevant column's monomial.
///
/// One slot for all three facts, so they cannot desync and roll back together. The `min_row`
/// offset rolls back with the sparse-set entry; the pool row it points at rolls back with the
/// pool's own `mark`/`restore` (they are marked together).
#[derive(Clone, Copy)]
pub struct ClassData<L: DenseId, T: DenseId> {
    pub use_list: L,
    /// Base offset of this class's row in `EClasses::min_pool`, or `None` if no row is
    /// allocated (the class holds no completion monomial yet). This is a **plain pool
    /// offset**, not a node-derived id: `usize`, `None` for absent — not `T::default()` (id 0
    /// is a real node) and not an id index type. The pool itself is `usize`-indexed.
    pub min_row: Option<usize>,
    pub atomic: bool,
    _t: core::marker::PhantomData<T>,
}

// `Tagged` by delegating the CAPTURE tag to the first field (`use_list`), the same idiom as
// `ListNode` in `containers/list.rs`. `min_row` is stored as `(offset, present)`: a plain
// `usize` offset plus a presence bool (both are just `Copy` data in the `Repr` tuple — the
// capture bit lives only on `use_list`, element 0).
impl<L: DenseId, T: DenseId> Tagged for ClassData<L, T> {
    type Repr = (L::Repr, usize, bool, bool);

    fn into_repr(self) -> Self::Repr {
        let (off, present) = match self.min_row {
            Some(o) => (o, true),
            None => (0, false),
        };
        (self.use_list.into_repr(), off, present, self.atomic)
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

pub struct MergeInfo<T, L> {
    pub survivor: T,
    pub absorbed: T,
    pub absorbed_uses: L,
    /// The absorbed class's min-monomial pool row offset (`None` if it had no row), so the
    /// caller can fold each column into the survivor's row (`EGraph` does the per-column
    /// `monomial_cmp`, §9a). The pool is append-only, so this offset stays valid after the
    /// absorbed repr is removed from the sparse set.
    pub absorbed_min_row: Option<usize>,
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
    entries: containers::VecI<EClassEntry<T>, T::Index, TRACK>,
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
            entries: containers::VecI::new(),
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
    /// Returns the row's base pool offset (a plain `usize`; `min_row` stores it as
    /// `Some(offset)`).
    fn ensure_min_row(&mut self, repr_id: T::Index) -> usize {
        let mut data = self.reprs.get(repr_id);
        if let Some(off) = data.min_row {
            return off;
        }
        debug_assert!(
            self.min_width > 0,
            "set_min_width must precede row allocation"
        );
        let off = self.min_pool.len();
        for _ in 0..self.min_width {
            self.min_pool.push(Opt::none());
        }
        data.min_row = Some(off);
        self.reprs.set(repr_id, data);
        off
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
        let list_id = self.uses.new_list();
        // No pool row yet (`min_row` is `Opt::none()`): a fresh class holds no completion
        // monomial until its op's column is seeded by `EGraph` (which knows the node's op).
        // Not yet referenced as a child, so not atomic (§9a).
        let repr_id = self.reprs.add(ClassData {
            use_list: list_id,
            min_row: None,
            atomic: false,
            _t: core::marker::PhantomData,
        });
        self.entries.push(EClassEntry::new(id, repr_id));
        repr_id
    }

    // -- Use-list management ------------------------------------------------

    /// Record that `parent_node` uses the class at `child_repr` as a child. Any such
    /// reference makes the size-1 monomial `{child_repr}` a real term, so the class
    /// becomes `atomic` (its completion rule RHS, §9a).
    pub fn add_use(&mut self, child_repr: T::Index, parent_node: T) {
        let mut data = self.reprs.get(child_repr);
        self.uses.append(data.use_list, parent_node);
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
    pub fn use_list_len(&self, repr_id: T::Index) -> u32 {
        self.uses.len(self.reprs.get(repr_id).use_list)
    }

    /// The class's current minimum-monomial node for completion column `col` (the completion
    /// rule RHS for that op when the class is not `atomic`, §9a), or `None` if the class holds
    /// no monomial of that op. `col` is the op's completion column (`EGraph` supplies it via
    /// the registry `completion_column`).
    pub fn min_monomial(&self, repr_id: T::Index, col: usize) -> Option<T> {
        let row = self.reprs.get(repr_id).min_row?;
        debug_assert!(col < self.min_width, "completion column out of range");
        self.min_pool.get(row + col).get()
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
        self.min_pool.set(row + col, Opt::some(node));
    }

    /// Read completion column `col` of a raw pool row offset (as carried in `MergeInfo`), for
    /// the merge fold. Returns `None` if the offset is absent (`None`) or the column is empty.
    pub fn min_monomial_at_row(&self, row: Option<usize>, col: usize) -> Option<T> {
        let base = row?;
        debug_assert!(col < self.min_width, "completion column out of range");
        self.min_pool.get(base + col).get()
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
        self.entries.get(idx).repr_id()
    }

    // -- Merge (steps 1-2 only: UF + circular list, NOT use-list splice) ----

    /// Merge two classes. Returns survivor, absorbed, and the absorbed class's
    /// use-list id (needed by rebuild to iterate parents before splicing).
    pub fn merge(&mut self, a: T, b: T) -> Option<MergeInfo<T, L>> {
        let (survivor, absorbed) = self.uf.union(a, b)?;
        let absorbed_repr = self.entries.get(absorbed).repr_id_unchecked();
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
        let absorbed_repr = self.entries.get(absorbed).repr_id_unchecked();
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
        let absorbed_repr = self.entries.get(absorbed).repr_id_unchecked();
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
        let absorbed_repr = self.entries.get(absorbed).repr_id_unchecked();
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

    fn splice_classes(&mut self, (survivor, absorbed): (T, T)) {
        let surv = self.entries.get(survivor);
        let abs = self.entries.get(absorbed);
        let abs_repr = abs.repr_id_unchecked();

        self.entries.set(
            survivor,
            EClassEntry::new(abs.next, surv.repr_id_unchecked()),
        );

        let mut absorbed_entry = EClassEntry::new(surv.next, abs_repr);
        absorbed_entry.set_absent();
        self.entries.set(absorbed, absorbed_entry);

        self.reprs.remove(abs_repr);
    }

    // -- Proofs -------------------------------------------------------------

    pub fn explain(&self, a: T, b: T, buf: &mut ProofBuf<T>) -> bool {
        self.uf.explain(a, b, buf)
    }

    // -- Iteration ----------------------------------------------------------

    pub fn iter_class(&self, start_idx: T) -> ClassIter<'_, T, TRACK> {
        ClassIter {
            entries: &self.entries,
            start_idx,
            current_idx: start_idx,
            done: false,
        }
    }

    // -- Semi-persistence ---------------------------------------------------

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> EClassesToken {
        EClassesToken {
            entries: self.entries.mark(shrink),
            reprs: self.reprs.mark(shrink),
            uf: self.uf.mark(shrink),
            uses: self.uses.mark(shrink),
            min_pool: self.min_pool.mark(shrink),
        }
    }

    pub fn restore(&mut self, token: EClassesToken) {
        self.entries.restore(token.entries);
        self.reprs.restore(token.reprs);
        self.uf.restore(token.uf);
        self.uses.restore(token.uses);
        self.min_pool.restore(token.min_pool);
    }
}

#[derive(Clone, Copy, Debug)]
pub struct EClassesToken {
    entries: VecToken,
    reprs: SparseSetToken,
    uf: UnionFindToken,
    min_pool: VecToken,
    uses: ListArenaToken,
}

// ---------------------------------------------------------------------------
// Iterators
// ---------------------------------------------------------------------------

pub struct ClassIter<'a, T: DenseId, const TRACK: bool> {
    entries: &'a containers::VecI<EClassEntry<T>, T::Index, TRACK>,
    start_idx: T,
    current_idx: T,
    done: bool,
}

impl<T: DenseId, const TRACK: bool> Iterator for ClassIter<'_, T, TRACK> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.done {
            return None;
        }
        let result = self.current_idx;
        self.current_idx = self.entries.get(self.current_idx).next;
        if self.current_idx == self.start_idx {
            self.done = true;
        }
        Some(result)
    }
}

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
        assert_eq!(ec.use_list_len(rx) as usize, ec.iter_uses(rx).count());
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
