// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Equivalence classes with integrated union-find and parent use-lists.
//!
//! ## The class layer IS the verified aggregate
//!
//! `EClasses` here is a type alias of `containers::eclasses::EClasses` with
//! this crate's [`Justification`] as the proof payload: same parameters
//! (`T, L, N, TRACK, PROOFS`), same method surface (including
//! `add_singleton(id)`, the justified merge family, and `explain`), same
//! panic messages, same 12-byte ring cell and class slot (asserted below).
//! The class-layer invariants W1-W6
//! (`containers-verus/doc/future/egraph-wf.md`) are machine-checked: every
//! mutation carries `requires wf, ensures wf`, and the build fails if a
//! change breaks preservation. Under `PROOFS` the kernel's union-find
//! carries the dual, uncompressed proof forest exactly as the hand-rolled
//! one did; the re-rooting and LCA logic is the same algorithm, hosted as
//! the kernel's trusted glue over verified columns
//! (`containers-verus/doc/design/egraph-class-layer-parity.md`).

use crate::containers::{self, DenseId, Opt, Tagged};
use crate::union_find::Justification;

/// Per-class data (the verified kernel's; same fields, same 12-byte repr).
pub use crate::containers::eclasses::ClassData;
/// Opaque token for [`EClasses::mark`] / [`EClasses::restore`].
pub use crate::containers::eclasses::EClassesToken;
/// Returned by `merge`: survivor, absorbed, and the absorbed class's data.
pub use crate::containers::eclasses::MergeInfo;

/// Equivalence classes with integrated union-find and parent use-lists
/// (the verified aggregate).
pub type EClasses<T, L, N, const TRACK: bool, const PROOFS: bool> =
    containers::eclasses::EClasses<T, L, N, Justification<T>, TRACK, PROOFS>;

/// Class-ring iterator: the verified `RingIter`, yielding `T` node ids in
/// ring order.
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

// The per-class slot: a use-list head, `min_row`, the member-count word (the
// `--union-by` policy input, `T::Index`-wide so it follows the id
// configuration), and two flags — 16 bytes at 31-bit ids. Was 12 before the
// verified size counter landed; the count word is the deliberate growth.
#[cfg(target_pointer_width = "64")]
const _: () = assert!(
    core::mem::size_of::<<ClassData<crate::id::UseListId, crate::id::ENodeId> as Tagged>::Repr>()
        == 16,
    "per-class slot must stay 16 bytes at 31-bit ids"
);

// The 63-bit configuration's slot: the same fields at 8-byte words.
#[cfg(target_pointer_width = "64")]
const _: () = assert!(
    core::mem::size_of::<
        <ClassData<crate::nodes::UseListId64, crate::nodes::ENodeId64> as Tagged>::Repr,
    >() <= 32,
    "per-class slot exceeds 32 bytes at 63-bit ids"
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
