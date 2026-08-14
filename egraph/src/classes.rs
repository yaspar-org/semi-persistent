// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Equivalence classes with integrated union-find and parent use-lists.
//!
//! ## The class layer is the verified aggregate
//!
//! `EClasses` here is an adapter over
//! `containers::eclasses::EClasses`, the verified aggregate whose `wf()`
//! carries the e-graph's class-layer invariants W1-W6
//! (`containers-verus/doc/future/egraph-wf.md`): the union-find's ghost root
//! map (W1), the root/payload/key bijection (W2), ring-partition agreement
//! with the union-find (W3), use-list ownership (W4), allocated use-list
//! entries (W5), and pool geometry (W6). Every mutation of the aggregate is
//! PROVED to preserve them, which retires the stage-0 debug monitor this
//! module used to carry: what the monitor asserted per merge, the verifier
//! now rejects at compile time if violated.
//!
//! The adapter adds exactly one thing the kernel does not model: the proof
//! forest (`parent_proof`, `justification` columns) behind `merge_justified`
//! and `explain`. Proof edges are metadata: no W-invariant reads them, and
//! they are stored in the same two semi-persistent `VecI` columns, with the
//! same re-rooting algorithm, as before the swap.
//!
//! Layout is unchanged: the ring cell is still `next` word plus
//! `Opt<T::Index>` payload (12 bytes at 31-bit ids, asserted below), the
//! per-class slot is still 12 bytes (asserted below), and the component
//! stores are the same `InlineStore`/`ParallelStore` columns at the same
//! index widths. The struct nesting differs (the five components live inside
//! the kernel; the two proof columns beside it), which moves no bytes.

use crate::containers::eclasses::EClasses as VerifiedEClasses;
use crate::containers::eclasses::EClassesToken as KernelToken;
use crate::containers::list::ListArena;
use crate::containers::{self, DenseId, IndexLike, Opt, ShrinkPolicy, Tagged, VecToken};
use crate::union_find::{Justification, ProofBuf};

/// Per-class data (the verified kernel's; same fields, same 12-byte repr).
pub use crate::containers::eclasses::ClassData;
/// Returned by `merge`: survivor, absorbed, and the absorbed class's data.
pub use crate::containers::eclasses::MergeInfo;

/// Equivalence classes with integrated union-find and parent use-lists.
///
/// - `T: DenseId` — node type (e.g. `ENodeId`)
/// - `L: DenseId` — use-list id type (e.g. `UseListId`)
/// - `N: DenseId` — use-list node id type (e.g. `UseNodeId`)
/// - `TRACK` — enable mark/restore
/// - `PROOFS` — enable proof tracking (justified merges + `explain`)
pub struct EClasses<T: DenseId, L: DenseId, N: DenseId, const TRACK: bool, const PROOFS: bool> {
    kernel: VerifiedEClasses<T, L, N, TRACK>,
    /// Proof forest: per-node proof parent (`None` unless `PROOFS`).
    parent_proof: Option<containers::VecI<T, <T as DenseId>::Index, TRACK>>,
    /// Per-node justification of the proof edge to its proof parent.
    justification: Option<containers::VecI<Justification<T>, <T as DenseId>::Index, TRACK>>,
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
            kernel: VerifiedEClasses::new(),
            parent_proof: if PROOFS {
                Some(containers::VecI::new())
            } else {
                None
            },
            justification: if PROOFS {
                Some(containers::VecI::new())
            } else {
                None
            },
        }
    }

    /// Set the min-monomial pool row width (`nb_completion`); frozen once
    /// rows exist (the kernel refuses a change).
    pub fn set_min_width(&mut self, width: usize) {
        self.kernel.set_min_width(width);
    }

    /// The min-monomial pool row width, for the merge fold's column loop.
    pub fn min_width(&self) -> usize {
        self.kernel.min_width()
    }

    pub fn len(&self) -> <T as DenseId>::Index {
        self.kernel.len()
    }

    pub fn is_empty(&self) -> bool {
        self.kernel.is_empty()
    }

    pub fn num_classes(&self) -> <T as DenseId>::Index {
        self.kernel.num_classes()
    }

    /// Allocate `id` as its own singleton class; `id` must be the next dense
    /// node id (the same contract the caller has always held).
    pub fn add_singleton(&mut self, id: T) -> <T as DenseId>::Index {
        assert!(
            id.to_usize() == self.kernel.len().as_usize(),
            "add_singleton: node ids must be dense and allocated in order"
        );
        let (_nid, key) = self.kernel.add_singleton();
        if let (Some(pp), Some(j)) = (&mut self.parent_proof, &mut self.justification) {
            pp.try_push(id).expect("push: within index word");
            j.try_push(Justification::Filler)
                .expect("push: within index word");
        }
        key
    }

    // -- Use-list management ------------------------------------------------

    /// Record that `parent_node` uses the class at `child_repr` as a child
    /// (marks the class atomic, §9a).
    pub fn add_use(&mut self, child_repr: <T as DenseId>::Index, parent_node: T) {
        self.kernel.add_use(child_repr, parent_node);
    }

    pub fn use_list_id(&self, repr_id: <T as DenseId>::Index) -> L {
        self.kernel.use_list_id(repr_id)
    }

    /// O(1) use-list length, widened to `usize` at the boundary.
    pub fn use_list_len(&self, repr_id: <T as DenseId>::Index) -> usize {
        self.kernel.use_list_len(repr_id)
    }

    /// The class's minimum-monomial node for completion column `col` (§9a).
    pub fn min_monomial(&self, repr_id: <T as DenseId>::Index, col: usize) -> Option<T> {
        self.kernel.min_monomial(repr_id, col)
    }

    /// Whether the class is referenced as a child of some node (§9a).
    pub fn atomic(&self, repr_id: <T as DenseId>::Index) -> bool {
        self.kernel.atomic(repr_id)
    }

    /// Set the class's minimum-monomial node for completion column `col`,
    /// allocating the class's pool row on first use.
    pub fn set_min_monomial(&mut self, repr_id: <T as DenseId>::Index, col: usize, node: T) {
        self.kernel.set_min_monomial(repr_id, col, node);
    }

    /// Read completion column `col` of a row number (as carried in
    /// `MergeInfo`), for the merge fold.
    pub fn min_monomial_at_row(
        &self,
        row: Option<<T as DenseId>::Index>,
        col: usize,
    ) -> Option<T> {
        self.kernel.min_monomial_at_row(row, col)
    }

    /// Mark the class `atomic` (§9a).
    pub fn set_atomic(&mut self, repr_id: <T as DenseId>::Index) {
        self.kernel.set_atomic(repr_id);
    }

    /// Iterate the use-list of a representative (parent nodes).
    pub fn iter_uses(&self, repr_id: <T as DenseId>::Index) -> impl Iterator<Item = T> + '_ {
        self.kernel.iter_uses(repr_id)
    }

    /// Direct access to the use-list arena (for iterating by list id).
    pub fn uses(&self) -> &ListArena<T, L, N, TRACK> {
        self.kernel.uses()
    }

    /// Splice absorbed class's use-list into survivor's. Takes list ids
    /// directly (the absorbed repr may already be removed).
    pub fn splice_uses(&mut self, survivor_list: L, absorbed_list: L) {
        self.kernel.splice_uses(survivor_list, absorbed_list);
    }

    // -- Find ---------------------------------------------------------------

    pub fn find(&mut self, x: T) -> T {
        self.kernel.find(x)
    }

    pub fn find_const(&self, x: T) -> T {
        self.kernel.find_const(x)
    }

    pub fn repr_id(&self, idx: T) -> Option<<T as DenseId>::Index> {
        self.kernel.repr_id(idx)
    }

    // -- Merge (steps 1-2 only: UF + circular list, NOT use-list splice) ----

    /// Merge two classes by rank. Only available when `PROOFS=false`.
    pub fn merge(&mut self, a: T, b: T) -> Option<MergeInfo<T, L>> {
        assert!(
            !PROOFS,
            "union() called on a PROOFS=true UnionFind; use union_justified() instead"
        );
        self.kernel.merge(a, b)
    }

    /// Merge with justification (records the proof edge `a—b`).
    pub fn merge_justified(
        &mut self,
        a: T,
        b: T,
        just: Justification<T>,
    ) -> Option<MergeInfo<T, L>> {
        let r = self.kernel.merge(a, b);
        if r.is_some() {
            self.record_proof_edge(a, b, just);
        }
        r
    }

    /// Whether `find(a)`'s class has at least as many parents as `find(b)`'s.
    fn prefer_a_by_uses(&self, a: T, b: T) -> bool {
        let ra = self.kernel.find_const(a);
        let rb = self.kernel.find_const(b);
        let len_a = self
            .kernel
            .repr_id(ra)
            .map_or(0, |r| self.kernel.use_list_len(r));
        let len_b = self
            .kernel
            .repr_id(rb)
            .map_or(0, |r| self.kernel.use_list_len(r));
        len_a >= len_b
    }

    /// Like [`merge`], but keeps the larger-use-list class as survivor.
    pub fn merge_directed(&mut self, a: T, b: T) -> Option<MergeInfo<T, L>> {
        assert!(
            !PROOFS,
            "union_directed() called on a PROOFS=true UnionFind; use union_justified_directed()"
        );
        let prefer_a = self.prefer_a_by_uses(a, b);
        self.kernel.merge_directed(a, b, prefer_a)
    }

    /// Justified counterpart of [`merge_directed`].
    pub fn merge_justified_directed(
        &mut self,
        a: T,
        b: T,
        just: Justification<T>,
    ) -> Option<MergeInfo<T, L>> {
        let prefer_a = self.prefer_a_by_uses(a, b);
        let r = self.kernel.merge_directed(a, b, prefer_a);
        if r.is_some() {
            self.record_proof_edge(a, b, just);
        }
        r
    }

    // -- Proof forest (metadata; no W-invariant reads it) --------------------

    /// Record the proof edge `a—b`: re-root `b`'s proof tree so `b` becomes
    /// the child of `a` (production's `union_inner` proof step, verbatim).
    fn record_proof_edge(&mut self, a: T, b: T, just: Justification<T>) {
        if let (Some(pp), Some(j)) = (&mut self.parent_proof, &mut self.justification) {
            Self::reroot_proof(pp, j, b);
            pp.set(b, a);
            j.set(b, just);
        }
    }

    /// Reverse the parent_proof path from `x` to its root, making `x` the new
    /// root (production's `reroot_proof`, verbatim).
    fn reroot_proof(
        pp: &mut containers::VecI<T, <T as DenseId>::Index, TRACK>,
        j: &mut containers::VecI<Justification<T>, <T as DenseId>::Index, TRACK>,
        x: T,
    ) {
        let mut path = vec![x];
        let mut cur = x;
        loop {
            let p = pp.get(cur);
            if p == cur {
                break;
            }
            path.push(p);
            cur = p;
        }
        // path = [x, ..., root]. Reverse the edges.
        for i in (0..path.len() - 1).rev() {
            let child = path[i + 1];
            let parent = path[i];
            pp.set(child, parent);
            j.set(child, j.get(parent));
        }
        // x is now the root
        pp.set(x, x);
    }

    /// Explain why `a ≡ b` by walking the proof tree. Appends steps to
    /// `buf.steps`. Returns false if not equivalent or `PROOFS=false`
    /// (production's `UnionFind::explain`, verbatim over the adapter's
    /// columns and the kernel's `find_const`).
    pub fn explain(&self, a: T, b: T, buf: &mut ProofBuf<T>) -> bool {
        if !PROOFS {
            return false;
        }
        if self.kernel.find_const(a) != self.kernel.find_const(b) {
            return false;
        }
        let pp = self.parent_proof.as_ref().unwrap();
        let j = self.justification.as_ref().unwrap();

        // Walk a → root into path_a
        buf.path_a.clear();
        Self::walk_to_root(pp, a, &mut buf.path_a);

        // Walk b → root into path_b
        buf.path_b.clear();
        Self::walk_to_root(pp, b, &mut buf.path_b);

        // Find LCA
        buf.seen.clear();
        for id in &buf.path_a {
            buf.seen.insert(id.as_usize());
        }
        let mut lca = self.kernel.find_const(a);
        for &node in &buf.path_b {
            if buf.seen.contains(&node.as_usize()) {
                lca = node;
                break;
            }
        }

        // a → lca
        let mut cur = a;
        while cur != lca {
            let parent = pp.get(cur);
            let just = j.get(cur);
            buf.steps.push((cur, parent, just));
            cur = parent;
        }
        // lca → b (collect reversed into rev, then extend steps)
        let rev_start = buf.rev.len();
        cur = b;
        while cur != lca {
            let parent = pp.get(cur);
            let just = j.get(cur);
            buf.rev.push((parent, cur, just));
            cur = parent;
        }
        buf.rev[rev_start..].reverse();
        buf.steps.extend_from_slice(&buf.rev[rev_start..]);
        buf.rev.truncate(rev_start);
        true
    }

    fn walk_to_root(
        pp: &containers::VecI<T, <T as DenseId>::Index, TRACK>,
        x: T,
        path: &mut Vec<T>,
    ) {
        path.push(x);
        let mut cur = x;
        loop {
            let p = pp.get(cur);
            if p == cur {
                break;
            }
            path.push(p);
            cur = p;
        }
    }

    // -- Iteration ----------------------------------------------------------

    /// Iterate `start_idx`'s class: every node in its ring, starting at
    /// `start_idx` and wrapping once (the verified `RingIter`).
    pub fn iter_class(&self, start_idx: T) -> ClassIter<'_, T, TRACK> {
        self.kernel.iter_class(start_idx)
    }

    // -- Semi-persistence ---------------------------------------------------

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> EClassesToken {
        EClassesToken {
            kernel: self.kernel.mark(shrink),
            proof: match (&mut self.parent_proof, &mut self.justification) {
                (Some(pp), Some(j)) => Some((
                    pp.try_mark(shrink)
                        .expect("mark: frame depth is bounded by the saturation driver"),
                    j.try_mark(shrink)
                        .expect("mark: frame depth is bounded by the saturation driver"),
                )),
                _ => None,
            },
        }
    }

    pub fn restore(&mut self, token: EClassesToken) {
        self.kernel
            .try_restore(token.kernel)
            .expect("restore: token minted by this container's own mark");
        if let Some((tp, tj)) = token.proof {
            self.parent_proof
                .as_mut()
                .expect("restore: proof token on a PROOFS=false EClasses")
                .try_restore(tp)
                .expect("restore: token minted by this container's own mark");
            self.justification
                .as_mut()
                .expect("restore: proof token on a PROOFS=false EClasses")
                .try_restore(tj)
                .expect("restore: token minted by this container's own mark");
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct EClassesToken {
    kernel: KernelToken,
    proof: Option<(VecToken, VecToken)>,
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
// payload (repr key + presence bit). The verified kernel instantiates the
// same `CircularList<Opt<T::Index>, T>`, so the assertion is unchanged.
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

// The per-class slot: a use-list head plus `min_row` plus two flags, packed to
// 12 bytes at 31-bit ids (the row NUMBER, not a pointer-width offset — see the
// kernel's `ClassData::min_row` doc). The kernel stores the same fields; its
// named repr struct has the same layout the old tuple had.
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
            ec2.uses().iter(absorbed_list).collect::<Vec<_>>()
        );

        // Now splice: absorbed's use-list into survivor's
        let surv_list = ec2.use_list_id(surv_repr);
        ec2.splice_uses(surv_list, absorbed_list);

        eprintln!("\nAfter splice_uses:");
        let all_uses: Vec<_> = ec2.iter_uses(surv_repr).collect();
        eprintln!("  survivor uses: {:?}", all_uses);
        assert_eq!(all_uses.len(), 4); // px, pxy, py, pxy
        eprintln!(
            "  absorbed list (should be empty): {:?}",
            ec2.uses().iter(absorbed_list).collect::<Vec<_>>()
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
