// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Transient sorted indices for leapfrog triejoin, bulk-rebuilt from e-graph state.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::literal::LitVal;
use std::collections::HashMap;

/// Hasher for the index maps.
///
/// Their keys are dense ids — node ids, op ids, `(id, position)` pairs — and the
/// maps are rebuilt every round and probed on every join step. std's default
/// SipHash is DoS-resistant, which is not a property any of these keys needs
/// (they are internal, never attacker-chosen) and costs several times a
/// multiply-shift on a `u32`.
///
/// foldhash rather than `rustc-hash` or a bespoke passthrough because it is
/// already the workspace's hasher: hashbrown 0.17's default, hence what
/// production `Map` and verified `SpMap` both hash with (see the note on
/// `foldhash` in the workspace `Cargo.toml`). One hasher across the workspace is
/// worth more than a marginal per-probe difference between the fast options.
pub type FastMap<K, V> = HashMap<K, V, foldhash::fast::RandomState>;

/// Sorted index over node ids, backed by a contiguous `Vec<G>`.
/// Supports O(log n) seek and O(1) step for leapfrog join.
#[derive(Clone, Debug)]
pub struct SortedVec<G> {
    pub data: Vec<G>,
}

impl<G: DenseId> SortedVec<G> {
    pub fn len(&self) -> usize {
        self.data.len()
    }
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
    pub fn iter(&self) -> SortedVecCursor<'_, G> {
        SortedVecCursor::new(&self.data)
    }
}

/// Cursor into a `SortedVec<G>`. Implements seek/step for leapfrog.
pub struct SortedVecCursor<'a, G> {
    data: &'a [G],
    pos: usize,
}

impl<'a, G: DenseId> SortedVecCursor<'a, G> {
    pub fn new(data: &'a [G]) -> Self {
        Self { data, pos: 0 }
    }

    #[inline]
    pub fn is_valid(&self) -> bool {
        self.pos < self.data.len()
    }

    #[inline]
    pub fn key(&self) -> G {
        self.data[self.pos]
    }

    #[inline]
    pub fn step(&mut self) {
        self.pos += 1;
    }

    /// Advance to the first element >= target.
    ///
    /// Galloping (exponential) search from the cursor, so the cost is
    /// O(log *d*) in the distance actually advanced rather than O(log *rem*)
    /// in the size of the remaining slice. Leapfrog seeks are overwhelmingly
    /// short: measured over the saturation workloads, 56-67% of AC-row seeks
    /// advance by at most one element and 83-86% by at most three, against a
    /// remaining slice averaging 2^4.7 to 2^7.9 elements. A plain
    /// `partition_point` over the whole remainder pays its full 5-8 probes for
    /// each of those.
    ///
    /// The probe-then-bisect structure is what keeps the long-jump case from
    /// regressing: the gallop overshoots by at most a factor of two, so the
    /// bisection that follows runs over a window no larger than the distance
    /// covered, and the total stays within one probe of a direct binary search.
    #[inline]
    pub fn seek(&mut self, target: G) {
        let data = &self.data;
        let n = data.len();

        // The common case, checked before any bounding work: the cursor already
        // satisfies the seek. 25-31% of semi-naive seeks are this, because the
        // `Difference` combinator seeks both sides to the same key.
        if self.pos >= n || data[self.pos] >= target {
            return;
        }

        // Gallop: double the offset until it lands on or past the target, so
        // `lo` stays strictly below it and `hi` is the first known bound.
        let mut step = 1usize;
        let mut lo = self.pos;
        while lo + step < n && data[lo + step] < target {
            lo += step;
            step *= 2;
        }
        let hi = (lo + step).min(n);

        // `lo` is known to be below the target and `hi` to be at or past it, so
        // bisect the open interval between them.
        self.pos = lo + 1 + data[lo + 1..hi].partition_point(|x| *x < target);
    }
}

/// All sorted indices for leapfrog join, bulk-rebuilt after each e-graph rebuild.
pub struct IndexStore<Cfg: EGraphConfig> {
    /// by_op[op] → sorted vec of node ids with that operator
    pub by_op: FastMap<Cfg::O, SortedVec<Cfg::G>>,
    /// by_repr[repr] → sorted vec of node ids in that e-class
    pub by_repr: FastMap<Cfg::G, SortedVec<Cfg::G>>,
    /// by_child_pos[(child_repr, position)] → sorted vec of parent node ids
    pub by_child_pos: FastMap<(Cfg::G, u32), SortedVec<Cfg::G>>,
    /// by_contains[child_repr] → sorted vec of variadic parent node ids (A/AC/ACI/PlainN)
    pub by_contains: FastMap<Cfg::G, SortedVec<Cfg::G>>,
}

impl<Cfg: EGraphConfig> IndexStore<Cfg>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    /// Bulk-rebuild all indices from the current e-graph state.
    /// Call after `eg.rebuild()`.
    pub fn build<L: LitVal, const TRACK: bool, const PROOFS: bool>(
        eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    ) -> Self {
        Self::build_from(eg, (0..eg.node_count()).map(Cfg::G::from_usize))
    }

    /// Build the per-round **delta** index from the touched-node log: the
    /// same four crosscutting maps as [`build`](Self::build), but restricted
    /// to the nodes that were created or recanonicalized this round.
    ///
    /// `touched` may contain duplicates (a node added then recanonicalized);
    /// they are deduplicated here. Subsumed nodes are skipped, exactly as in
    /// `build`, so for every key `k` the delta is a subset of the full
    /// index's `k` bucket — `build_delta(eg, eg.touched())` ⊆ `build(eg)`.
    pub fn build_delta<L: LitVal, const TRACK: bool, const PROOFS: bool>(
        eg: &EGraph<Cfg, L, TRACK, PROOFS>,
        touched: &[Cfg::G],
    ) -> Self {
        let mut ids: Vec<Cfg::G> = touched.to_vec();
        ids.sort_unstable();
        ids.dedup();
        Self::build_from(eg, ids.into_iter())
    }

    /// Shared bucketing core for [`build`](Self::build) and
    /// [`build_delta`](Self::build_delta): index the given node ids into the
    /// four crosscutting maps. Skips subsumed nodes.
    fn build_from<L: LitVal, const TRACK: bool, const PROOFS: bool>(
        eg: &EGraph<Cfg, L, TRACK, PROOFS>,
        ids: impl Iterator<Item = Cfg::G>,
    ) -> Self {
        let mut by_op: FastMap<Cfg::O, Vec<Cfg::G>> = FastMap::default();
        let mut by_repr: FastMap<Cfg::G, Vec<Cfg::G>> = FastMap::default();
        let mut by_child_pos: FastMap<(Cfg::G, u32), Vec<Cfg::G>> = FastMap::default();
        let mut by_contains: FastMap<Cfg::G, Vec<Cfg::G>> = FastMap::default();

        for gid in ids {
            if eg.node_flags(gid) & crate::node_types::FLAG_SUBSUMED != 0 {
                continue;
            }
            let op = eg.node_op(gid);
            let repr = eg.class_repr(gid);

            by_op.entry(op).or_default().push(gid);
            by_repr.entry(repr).or_default().push(gid);

            let mut pos = 0u32;
            let is_variadic = eg.for_each_child(gid, |child, _mult| {
                let child_repr = eg.class_repr(child);
                by_child_pos.entry((child_repr, pos)).or_default().push(gid);
                pos += 1;
            });
            // For variadic nodes (arity > 0 from PlainN/A/AC/ACI), also populate by_contains
            if is_variadic > 3
                || matches!(
                    eg.node_ref(gid),
                    crate::typed_routing::NodeRef::Seq(_)
                        | crate::typed_routing::NodeRef::MSet(_)
                        | crate::typed_routing::NodeRef::Set(_)
                        | crate::typed_routing::NodeRef::PlainN(_)
                )
            {
                let mut seen = Vec::new(); // dedup within one node
                eg.for_each_child(gid, |child, _mult| {
                    let cr = eg.class_repr(child);
                    if !seen.contains(&cr) {
                        seen.push(cr);
                        by_contains.entry(cr).or_default().push(gid);
                    }
                });
            }
        }

        fn finalize<K: Eq + std::hash::Hash, G: DenseId>(
            map: FastMap<K, Vec<G>>,
        ) -> FastMap<K, SortedVec<G>> {
            map.into_iter()
                .map(|(k, mut v)| {
                    v.sort_unstable();
                    v.dedup();
                    (k, SortedVec { data: v })
                })
                .collect()
        }

        Self {
            by_op: finalize(by_op),
            by_repr: finalize(by_repr),
            by_child_pos: finalize(by_child_pos),
            by_contains: finalize(by_contains),
        }
    }

    /// Get an iterator over nodes with the given operator.
    pub fn iter_by_op(&self, op: Cfg::O) -> SortedVecCursor<'_, Cfg::G> {
        match self.by_op.get(&op) {
            Some(sv) => SortedVecCursor::new(&sv.data),
            None => SortedVecCursor::new(&[]),
        }
    }

    /// Get an iterator over nodes in the given e-class.
    pub fn iter_by_repr(&self, repr: Cfg::G) -> SortedVecCursor<'_, Cfg::G> {
        match self.by_repr.get(&repr) {
            Some(sv) => SortedVecCursor::new(&sv.data),
            None => SortedVecCursor::new(&[]),
        }
    }

    /// Get an iterator over parent nodes that have `child_repr` at position `pos`.
    pub fn iter_by_child_pos(&self, child_repr: Cfg::G, pos: u32) -> SortedVecCursor<'_, Cfg::G> {
        match self.by_child_pos.get(&(child_repr, pos)) {
            Some(sv) => SortedVecCursor::new(&sv.data),
            None => SortedVecCursor::new(&[]),
        }
    }

    /// Get an iterator over variadic nodes containing `child_repr`.
    pub fn iter_by_contains(&self, child_repr: Cfg::G) -> SortedVecCursor<'_, Cfg::G> {
        match self.by_contains.get(&child_repr) {
            Some(sv) => SortedVecCursor::new(&sv.data),
            None => SortedVecCursor::new(&[]),
        }
    }
}

// ---------------------------------------------------------------------------
// Semi-naive: per-variant index view
// ---------------------------------------------------------------------------

/// Which slice an atom reads, in a given semi-naive variant.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IndexMode {
    /// Read the full index (naive, or an atom after the delta atom).
    Full,
    /// Read the delta index (the variant's delta atom).
    Delta,
    /// Read full minus delta (an atom before the delta atom — "old only").
    FullMinusDelta,
}

/// The context one semi-naive variant needs: the full and delta indices,
/// and which atom (by stable `atom_id`) is the delta-restricted one.
///
/// Not a new abstraction — just the bundle the matcher needs in place of a
/// bare `&IndexStore`. A `delta_atom` of `None` is the **naive** view: every
/// atom reads `full` (and `delta` is never consulted).
#[derive(Clone, Copy)]
pub struct VariantIndex<'a, Cfg: EGraphConfig> {
    pub full: &'a IndexStore<Cfg>,
    pub delta: &'a IndexStore<Cfg>,
    pub delta_atom: Option<usize>,
}

impl<'a, Cfg: EGraphConfig> VariantIndex<'a, Cfg> {
    /// Naive view: every atom reads `full`. `delta` is aliased to `full` and
    /// never read (mode is always `Full`).
    pub fn naive(full: &'a IndexStore<Cfg>) -> Self {
        Self {
            full,
            delta: full,
            delta_atom: None,
        }
    }

    /// Variant `i`: atom `i` reads delta, atoms `< i` read full∖delta, atoms
    /// `> i` read full.
    pub fn variant(
        full: &'a IndexStore<Cfg>,
        delta: &'a IndexStore<Cfg>,
        delta_atom: usize,
    ) -> Self {
        Self {
            full,
            delta,
            delta_atom: Some(delta_atom),
        }
    }

    /// Mode for an atom given its stable `atom_id`. Independent of the
    /// scheduler's execution order — purely a function of the numbering.
    #[inline]
    pub fn mode(&self, atom_id: usize) -> IndexMode {
        match self.delta_atom {
            None => IndexMode::Full,
            Some(i) if atom_id == i => IndexMode::Delta,
            Some(i) if atom_id < i => IndexMode::FullMinusDelta,
            Some(_) => IndexMode::Full,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

    #[test]
    fn by_op_index() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let g = eg.register_op1("g", int, int);
        let x_op = eg.register_op0("x", int);

        let x = eg.add(x_op, &[]);
        let fx = eg.add(f, &[x]);
        let gx = eg.add(g, &[x]);
        let ffx = eg.add(f, &[fx]);

        let idx = IndexStore::build(&eg);

        // Two f-nodes: fx, ffx
        let f_nodes = &idx.by_op[&f];
        assert_eq!(f_nodes.len(), 2);
        assert!(f_nodes.data.contains(&fx));
        assert!(f_nodes.data.contains(&ffx));

        // One g-node
        assert_eq!(idx.by_op[&g].len(), 1);
        assert!(idx.by_op[&g].data.contains(&gx));

        // One x-node
        assert_eq!(idx.by_op[&x_op].len(), 1);
    }

    #[test]
    fn by_repr_after_merge() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);

        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        eg.merge(x, y);
        eg.rebuild();

        let idx = IndexStore::build(&eg);
        let repr = eg.class_repr(x);
        let class_nodes = &idx.by_repr[&repr];
        assert_eq!(class_nodes.len(), 2);
    }

    #[test]
    fn by_child_pos_index() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let g = eg.register_op2("g", int, int, int);
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);

        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        let fx = eg.add(f, &[x]);
        let gxy = eg.add(g, &[x, y]);

        let idx = IndexStore::build(&eg);

        // x is child at pos 0 of both fx and gxy
        let parents_x_0 = &idx.by_child_pos[&(x, 0)];
        assert_eq!(parents_x_0.len(), 2);
        assert!(parents_x_0.data.contains(&fx));
        assert!(parents_x_0.data.contains(&gxy));

        // y is child at pos 1 of gxy only
        let parents_y_1 = &idx.by_child_pos[&(y, 1)];
        assert_eq!(parents_y_1.len(), 1);
        assert!(parents_y_1.data.contains(&gxy));
    }

    #[test]
    fn seek_and_step() {
        let data = vec![
            crate::id::ENodeId::from_usize(2),
            crate::id::ENodeId::from_usize(5),
            crate::id::ENodeId::from_usize(8),
            crate::id::ENodeId::from_usize(12),
        ];
        let mut it = SortedVecCursor::new(&data);
        assert!(it.is_valid());
        assert_eq!(it.key().to_usize(), 2);

        it.seek(crate::id::ENodeId::from_usize(5));
        assert_eq!(it.key().to_usize(), 5);

        it.seek(crate::id::ENodeId::from_usize(7));
        assert_eq!(it.key().to_usize(), 8);

        it.step();
        assert_eq!(it.key().to_usize(), 12);

        it.step();
        assert!(!it.is_valid());
    }

    /// Property tests for the galloping `seek` (perf doc E7).
    ///
    /// `seek` is the one place in the join layer that does index arithmetic —
    /// a doubling ladder, a `min`, and a bisection over a computed window — so
    /// it is the one place an off-by-one silently drops join results instead of
    /// panicking. These pin the four properties the join relies on:
    ///
    /// 1. **Correctness**: `seek(t)` lands on the first key ≥ `t`, or exhausts.
    /// 2. **Monotonicity**: `pos` never decreases, so leapfrog's forward-only
    ///    contract holds and `Difference`'s delta cursor cannot rewind.
    /// 3. **No skipping**: stepping through a cursor after any seek sequence
    ///    yields exactly the tail of the data, in order — nothing is jumped over.
    /// 4. **In-bounds**: `pos` stays ≤ `len`, and no index arithmetic overflows,
    ///    including on the widest ids and on empty slices.
    ///
    /// Both id widths are covered, since `ENodeId` is 31-bit and `ENodeId64` is
    /// 63-bit and the bisection arithmetic is over `usize`.
    mod seek_props {
        use super::*;
        use crate::containers::DenseId;
        use proptest::prelude::*;

        /// A sorted, duplicate-free key vector — the representation invariant of
        /// `SortedVec`, which `IndexStore::build_from` establishes by sorting and
        /// deduping each bucket.
        fn sorted_unique() -> impl Strategy<Value = Vec<usize>> {
            proptest::collection::vec(0usize..200, 0..64).prop_map(|mut v| {
                v.sort_unstable();
                v.dedup();
                v
            })
        }

        /// Targets drawn from beyond the data's range as well as inside it, so
        /// the "no such key" path and the `hi = n` clamp are both hit.
        fn targets() -> impl Strategy<Value = Vec<usize>> {
            proptest::collection::vec(0usize..220, 0..16)
        }

        /// The reference implementation: linear scan from the cursor.
        fn expected_pos(data: &[usize], from: usize, target: usize) -> usize {
            let mut p = from;
            while p < data.len() && data[p] < target {
                p += 1;
            }
            p
        }

        fn run_seek_lands_on_first_ge<G: DenseId>(vals: &[usize], ts: &[usize]) {
            let data: Vec<G> = vals.iter().map(|&v| G::from_usize(v)).collect();
            for &t in ts {
                let mut c = SortedVecCursor::new(&data);
                c.seek(G::from_usize(t));
                assert_eq!(
                    c.pos,
                    expected_pos(vals, 0, t),
                    "seek({t}) on {vals:?} landed at {}",
                    c.pos
                );
                if c.is_valid() {
                    assert!(c.key().to_usize() >= t, "landed below target");
                    // First such key: the predecessor must be strictly below.
                    if c.pos > 0 {
                        assert!(vals[c.pos - 1] < t, "skipped a key ≥ target");
                    }
                }
            }
        }

        fn run_seek_sequence_is_monotone<G: DenseId>(vals: &[usize], ts: &[usize]) {
            let data: Vec<G> = vals.iter().map(|&v| G::from_usize(v)).collect();
            let mut c = SortedVecCursor::new(&data);
            let mut prev = c.pos;
            let mut from = 0usize;
            for &t in ts {
                c.seek(G::from_usize(t));
                assert!(c.pos >= prev, "pos went backwards: {prev} -> {}", c.pos);
                assert!(c.pos <= data.len(), "pos {} out of bounds", c.pos);
                // Against the linear reference, from wherever the cursor was.
                assert_eq!(c.pos, expected_pos(vals, from, t), "seek({t}) mid-sequence");
                prev = c.pos;
                from = c.pos;
            }
        }

        /// Interleave seeks and steps, then drain: the keys observed must be
        /// exactly the surviving tail of `vals`, with nothing skipped and
        /// nothing repeated.
        fn run_no_keys_are_skipped<G: DenseId>(vals: &[usize], ops: &[(bool, usize)]) {
            let data: Vec<G> = vals.iter().map(|&v| G::from_usize(v)).collect();
            let mut c = SortedVecCursor::new(&data);
            let mut model = 0usize;

            for &(is_seek, arg) in ops {
                if is_seek {
                    c.seek(G::from_usize(arg));
                    model = expected_pos(vals, model, arg);
                } else if c.is_valid() {
                    c.step();
                    model += 1;
                }
                assert_eq!(c.pos, model, "cursor diverged from the model");
            }

            // Draining from here must yield exactly vals[model..].
            let mut seen = Vec::new();
            while c.is_valid() {
                seen.push(c.key().to_usize());
                c.step();
            }
            assert_eq!(seen, vals[model.min(vals.len())..], "tail mismatch");
        }

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(2000))]

            #[test]
            fn seek_lands_on_first_ge_31(vals in sorted_unique(), ts in targets()) {
                run_seek_lands_on_first_ge::<crate::id::ENodeId>(&vals, &ts);
            }

            #[test]
            fn seek_lands_on_first_ge_63(vals in sorted_unique(), ts in targets()) {
                run_seek_lands_on_first_ge::<crate::nodes::ENodeId64>(&vals, &ts);
            }

            #[test]
            fn seek_sequence_is_monotone_31(vals in sorted_unique(), ts in targets()) {
                run_seek_sequence_is_monotone::<crate::id::ENodeId>(&vals, &ts);
            }

            #[test]
            fn seek_sequence_is_monotone_63(vals in sorted_unique(), ts in targets()) {
                run_seek_sequence_is_monotone::<crate::nodes::ENodeId64>(&vals, &ts);
            }

            #[test]
            fn no_keys_are_skipped_31(
                vals in sorted_unique(),
                ops in proptest::collection::vec((any::<bool>(), 0usize..220), 0..24),
            ) {
                run_no_keys_are_skipped::<crate::id::ENodeId>(&vals, &ops);
            }

            #[test]
            fn no_keys_are_skipped_63(
                vals in sorted_unique(),
                ops in proptest::collection::vec((any::<bool>(), 0usize..220), 0..24),
            ) {
                run_no_keys_are_skipped::<crate::nodes::ENodeId64>(&vals, &ops);
            }
        }

        /// The gallop ladder doubles `step` without bound and computes
        /// `lo + step`, so a long run of misses on a large slice is where an
        /// overflow would live. 4096 keys forces ~12 doublings.
        #[test]
        fn long_gallop_does_not_overflow() {
            let data: Vec<crate::id::ENodeId> = (0..4096)
                .map(|i| crate::id::ENodeId::from_usize(i * 2))
                .collect();
            let mut c = SortedVecCursor::new(&data);
            // Target past every key: the ladder runs to the end and clamps.
            c.seek(crate::id::ENodeId::from_usize(100_000));
            assert_eq!(c.pos, data.len());
            assert!(!c.is_valid());

            // And a target reachable only after a full-length gallop.
            let mut c = SortedVecCursor::new(&data);
            c.seek(crate::id::ENodeId::from_usize(8190));
            assert_eq!(c.key().to_usize(), 8190);
        }

        /// Degenerate shapes, each of which exercises a different early exit.
        #[test]
        fn edge_shapes() {
            let empty: [crate::id::ENodeId; 0] = [];
            let mut c = SortedVecCursor::new(&empty);
            c.seek(crate::id::ENodeId::from_usize(7));
            assert_eq!(c.pos, 0);
            assert!(!c.is_valid());

            let one = [crate::id::ENodeId::from_usize(5)];
            for (t, want) in [(0usize, 0usize), (5, 0), (6, 1)] {
                let mut c = SortedVecCursor::new(&one);
                c.seek(crate::id::ENodeId::from_usize(t));
                assert_eq!(c.pos, want, "single-element seek({t})");
            }

            // Seeking on an already-exhausted cursor is a no-op, not a panic.
            let mut c = SortedVecCursor::new(&one);
            c.step();
            assert!(!c.is_valid());
            c.seek(crate::id::ENodeId::from_usize(0));
            assert_eq!(c.pos, 1);
            c.seek(crate::id::ENodeId::from_usize(99));
            assert_eq!(c.pos, 1);
        }

        /// The largest id each width admits, seeked to and past. `from_usize` is
        /// the id's own constructor, so this is the top of its representable
        /// range rather than an arbitrary large number.
        #[test]
        fn saturated_ids() {
            fn run<G: DenseId>(max: usize) {
                let data: Vec<G> = [max - 2, max - 1, max]
                    .iter()
                    .map(|&v| G::from_usize(v))
                    .collect();
                let mut c = SortedVecCursor::new(&data);
                c.seek(G::from_usize(max));
                assert_eq!(c.pos, 2);
                assert_eq!(c.key().to_usize(), max);
                c.step();
                assert!(!c.is_valid());

                let mut c = SortedVecCursor::new(&data);
                c.seek(G::from_usize(max - 1));
                assert_eq!(c.key().to_usize(), max - 1);
            }
            run::<crate::id::ENodeId>((1usize << 31) - 1);
            run::<crate::nodes::ENodeId64>((1usize << 63) - 1);
        }
    }

    #[test]
    fn by_child_pos_after_merge() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);

        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        let fx = eg.add(f, &[x]);
        let _fy = eg.add(f, &[y]);
        eg.merge(x, y);
        eg.rebuild();

        let idx = IndexStore::build(&eg);
        let repr = eg.class_repr(x);

        // Both fx and fy should appear under the canonical repr at pos 0
        let parents = &idx.by_child_pos[&(repr, 0)];
        // After merge, fx and fy are congruent — same node. So 1 entry.
        assert!(parents.data.contains(&eg.find_const(fx)));
    }

    #[test]
    fn by_contains_variadic() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let plus = eg.register_mset("plus", int, int);
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);
        let z_op = eg.register_op0("z", int);

        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        let z = eg.add(z_op, &[]);
        let pxy = eg.add(plus, &[x, y]);
        let pxz = eg.add(plus, &[x, z]);

        let idx = IndexStore::build(&eg);

        // x is contained in both pxy and pxz
        let contains_x = &idx.by_contains[&x];
        assert_eq!(contains_x.len(), 2);
        assert!(contains_x.data.contains(&pxy));
        assert!(contains_x.data.contains(&pxz));

        // y is contained only in pxy
        let contains_y = &idx.by_contains[&y];
        assert_eq!(contains_y.len(), 1);
    }
}
