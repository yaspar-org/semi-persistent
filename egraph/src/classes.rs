// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Equivalence classes with integrated union-find and parent use-lists.
//!
//! Combines circular linked lists (for class iteration) with a union-find
//! (for fast canonical representative lookup). Each representative owns a
//! use-list tracking which e-nodes reference it as a child.

use crate::containers::DenseId;
use crate::containers::Tagged;
use crate::containers::list::{ListArena, ListArenaToken};
use crate::containers::sparse_set::{SparseSet, SparseSetToken};
use crate::containers::{self, ShrinkPolicy, VecToken};
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
/// - `ac_min` — the class's current AC minimum-monomial node: the member node
///   whose monomial is `≫_f`-least (see `doc/design/ac-congruence-completeness.md`
///   §9a). Maintained O(1) on merge by `EGraph` (which has the node access
///   `monomial_cmp` needs); `EClasses` only stores and shuttles it.
/// - `atomic` — whether the class is referenced as a child of some node, making
///   the size-1 monomial `{classid}` a real term and the class's normal-form
///   representative (§9a). Set on `add_use` and on gaining a non-AC node,
///   OR-combined on merge. The completion rule RHS is `{classid}` if `atomic`,
///   else `ac_min`'s monomial.
///
/// One slot for all three facts, so they cannot desync and roll back together.
#[derive(Clone, Copy)]
pub struct ClassData<L: DenseId, T: DenseId> {
    pub use_list: L,
    pub ac_min: T,
    pub atomic: bool,
}

// `Tagged` by delegating the tag to the first field (`use_list`), the same idiom
// as `ListNode` in `containers/list.rs`. No bit-packing: `Repr` is a tuple of the
// component reprs (and `bool`, which is `Copy`), so it works at any id width.
impl<L: DenseId, T: DenseId> Tagged for ClassData<L, T> {
    type Repr = (L::Repr, T::Repr, bool);

    fn into_repr(self) -> Self::Repr {
        (
            self.use_list.into_repr(),
            self.ac_min.into_repr(),
            self.atomic,
        )
    }
    fn from_repr(r: &Self::Repr) -> Self {
        Self {
            use_list: L::from_repr(&r.0),
            ac_min: T::from_repr(&r.1),
            atomic: r.2,
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
            ac_min: T::default(),
            atomic: false,
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
    /// The absorbed class's AC minimum-monomial node, so the caller can fold it
    /// into the survivor's `ac_min` (`EGraph` does the `monomial_cmp`, §9a).
    pub absorbed_ac_min: T,
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
        }
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
        // Seed ac_min to the node itself: a singleton class's only member is its
        // own minimum monomial. Not yet referenced as a child, so not atomic (§9a).
        let repr_id = self.reprs.add(ClassData {
            use_list: list_id,
            ac_min: id,
            atomic: false,
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

    /// The class's current AC minimum-monomial node (the completion rule RHS when the
    /// class is not `atomic`, §9a).
    pub fn ac_min(&self, repr_id: T::Index) -> T {
        self.reprs.get(repr_id).ac_min
    }

    /// Whether the class is referenced as a child of some node, making `{classid}` its
    /// normal-form representative (§9a).
    pub fn ac_atomic(&self, repr_id: T::Index) -> bool {
        self.reprs.get(repr_id).atomic
    }

    /// Overwrite the class's AC minimum-monomial node. Called by `EGraph` after a
    /// merge, once it has compared the two classes' minima with `monomial_cmp`.
    pub fn set_ac_min(&mut self, repr_id: T::Index, node: T) {
        let mut data = self.reprs.get(repr_id);
        data.ac_min = node;
        self.reprs.set(repr_id, data);
    }

    /// Mark the class `atomic` (it has a non-AC node, so `{classid}` is its RHS, §9a).
    pub fn set_ac_atomic(&mut self, repr_id: T::Index) {
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
            absorbed_ac_min: absorbed_data.ac_min,
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
            absorbed_ac_min: absorbed_data.ac_min,
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
        }
    }

    pub fn restore(&mut self, token: EClassesToken) {
        self.entries.restore(token.entries);
        self.reprs.restore(token.reprs);
        self.uf.restore(token.uf);
        self.uses.restore(token.uses);
    }
}

#[derive(Clone, Copy, Debug)]
pub struct EClassesToken {
    entries: VecToken,
    reprs: SparseSetToken,
    uf: UnionFindToken,
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
}
