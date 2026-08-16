// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Transient sorted indices for leapfrog triejoin, bulk-rebuilt from e-graph state.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::{DenseId, IndexLike};
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

/// Cursor into a `SortedVec<G>`: the **verified** galloping cursor from
/// `containers-verus`, re-exported so this module's public surface is unchanged.
///
/// The seek is proven, not just tested: it lands on the first key `>= target`
/// and skips no present key, for every slice and every target, with every slice
/// index in bounds and no arithmetic overflow. The proof is stated against the
/// same `seek_target_idx` spec function the verified B+tree cursor uses, which
/// is what makes the two substitutable at the `SortedCursor` boundary.
///
/// See `containers-verus/doc/design/12-sorted-vec-cursor.md`. The algorithm and
/// the `#[inline]` attributes match what this module previously defined inline;
/// the erased build compiles the same doubling ladder and bounded bisection.
pub use semi_persistent_containers::SortedVecCursor;

/// Sorted index over node ids, backed by a contiguous `Vec<G>`.
/// Supports O(log n) seek and O(1) step for leapfrog join.
///
/// The field is private on purpose: `SortedVecCursor::new`'s `requires` is
/// strict sortedness, and Verus erases it at runtime — an unsorted vector
/// here would not panic, it would silently drop join matches. Construction
/// goes through the two constructors below, so the invariant is carried by
/// the type instead of by the discipline of one call site.
#[derive(Clone, Debug)]
pub struct SortedVec<G> {
    data: Vec<G>,
}

impl<G> Default for SortedVec<G> {
    fn default() -> Self {
        SortedVec { data: Vec::new() }
    }
}

impl<G: DenseId> SortedVec<G> {
    /// Wrap a vector the caller has already sorted and deduplicated.
    /// Debug builds re-check; release trusts the caller within this module's
    /// review boundary.
    pub fn from_sorted_dedup(v: Vec<G>) -> Self {
        debug_assert!(
            v.windows(2).all(|w| w[0] < w[1]),
            "SortedVec: input not strictly sorted"
        );
        SortedVec { data: v }
    }
    /// Sort + dedup, then wrap. For callers with unordered input.
    pub fn from_unsorted(mut v: Vec<G>) -> Self {
        v.sort_unstable();
        v.dedup();
        SortedVec { data: v }
    }
    /// Append without re-establishing the order, for a builder that will call
    /// [`sort_dedup`](Self::sort_dedup) before anyone reads the bucket.
    ///
    /// The invariant is suspended between the two calls, so this pair is
    /// private to `IndexStore::build_from`: filling the buckets in place is
    /// what lets the build skip rebuilding a two-million-key map to change the
    /// value type from `Vec<G>` to `SortedVec<G>`.
    fn push_unordered(&mut self, g: G) {
        self.data.push(g);
    }
    /// Re-establish the order after a run of [`push_unordered`](Self::push_unordered).
    fn sort_dedup(&mut self) {
        self.data.sort_unstable();
        self.data.dedup();
    }
    pub fn as_slice(&self) -> &[G] {
        &self.data
    }
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

/// Mean fan-out of each access path, measured on the nodes this index holds.
///
/// The scheduler charges a join by how many candidate nodes one probe yields,
/// and the three probe kinds differ by orders of magnitude on the same
/// e-graph: on `math-microbenchmark` at iteration 8, enumerating a bound
/// class's nodes yields 2.51 and enumerating a bound child's parents yields
/// 1,239 (`comparison/throughput-gap-ours.md`, Q2). Charging both the same
/// fixed halving underestimated one join by 2,479x and cost 95.3% of an
/// 11.6 s run. These are the measured replacements; chapter 20 states the
/// model they feed.
///
/// Each number is the **size-biased** mean bucket size, `sum(b^2) / sum(b)`
/// over the path's buckets, not the plain mean `sum(b) / count(b)`. A probe key
/// is a variable the join bound from the data, so it lands in a bucket with
/// probability proportional to that bucket's size: a class that is the child of
/// a thousand nodes is probed a thousand times and a class that is the child of
/// one is probed once. The plain mean answers "how big is a bucket picked at
/// random", which no probe does, and on a distribution with one hub bucket of
/// size H among K singletons it reports about 1 where the size-biased mean
/// reports about H. Chapter 20's Fact 2 still applies: this is one number per
/// path, so it prices the *expected* probe and not the individual one, and the
/// variance is what per-binding driver selection (S3) is for.
#[derive(Clone, Debug)]
pub struct FanOuts<O> {
    /// Nodes in the class a `ByRepr` probe lands in.
    pub by_repr: f64,
    /// `(op, position)` -> `op`-nodes in the bucket a `ByChildPos` probe lands
    /// in, after its intersection with `by_op[op]`. Keyed per op because the
    /// whole defect is that the two ops of one query differ here by three
    /// orders of magnitude, and per position because an operator's arguments
    /// are not drawn from the same classes.
    pub by_child_pos: FastMap<(O, usize), f64>,
    /// `op` -> variadic `op`-nodes in the bucket a `ByContains` probe lands in.
    pub by_contains: FastMap<O, f64>,
    /// Nodes the index holds, the denominator [`by_repr`](Self::by_repr) is a
    /// fraction of.
    pub nodes: usize,
}

impl<O> Default for FanOuts<O> {
    fn default() -> Self {
        Self {
            by_repr: 1.0,
            by_child_pos: FastMap::default(),
            by_contains: FastMap::default(),
            nodes: 0,
        }
    }
}

/// All sorted indices for leapfrog join, bulk-rebuilt after each e-graph rebuild.
pub struct IndexStore<Cfg: EGraphConfig> {
    /// by_op[op] → sorted vec of node ids with that operator
    pub by_op: FastMap<Cfg::O, SortedVec<Cfg::G>>,
    /// by_repr[repr] → sorted vec of node ids in that e-class
    pub by_repr: FastMap<Cfg::G, SortedVec<Cfg::G>>,
    /// by_child_pos[(child_repr, position)] → sorted vec of parent node ids.
    /// The position is [`Cfg::Index`](crate::config::EGraphConfig::Index)-wide: it is an
    /// offset into one node's children, and a variadic node's children are a span in the
    /// child pool, which that word already sizes. See [`IndexLookup::ByChildPos`].
    ///
    /// [`IndexLookup::ByChildPos`]: crate::schedule::IndexLookup::ByChildPos
    pub by_child_pos: FastMap<(Cfg::G, Cfg::Index), SortedVec<Cfg::G>>,
    /// by_contains[child_repr] → sorted vec of variadic parent node ids (A/AC/ACI/PlainN)
    pub by_contains: FastMap<Cfg::G, SortedVec<Cfg::G>>,
    /// `repr[id]` — the class representative of every node id as of this build.
    ///
    /// The three keyed maps above are keyed by *this* canonicalization, and it
    /// stops being the e-graph's the moment the round's first rule merges a
    /// class. A matcher that canonicalizes a lookup key with the live
    /// union-find and then probes a bucket keyed at build time reads a bucket
    /// that belongs to some other class, so the answer depends on which access
    /// path the join order happened to use. Keeping the build's mapping makes
    /// every access path agree; see [`round_repr`](Self::round_repr) and
    /// chapter 09's snapshot contract.
    ///
    /// Filled by [`build`](Self::build) only. [`build_delta`](Self::build_delta)
    /// leaves it empty: a delta is built in the same instant as its full index
    /// and shares that index's canonicalization, so the mapping is stored once.
    pub repr: Vec<Cfg::G>,
    /// `op[id]` — the operator of every node id as of this build.
    ///
    /// A join that demotes its `ByOp` lookup to a per-candidate operator test
    /// (`ematch::run_join`) reads this instead of [`EGraph::node_op`], which
    /// resolves the routing table and then the arity-specific arena: two
    /// dependent random loads over 10 MB and 20 MB against one over `4 ·
    /// node_count` bytes. The build pays for it with a sequential pass, where
    /// the same two loads stream.
    ///
    /// Filled by [`build`](Self::build) only, like [`repr`](Self::repr): the
    /// delta's ids are a subset of the full index's, so one table serves both.
    pub op: Vec<Cfg::O>,
    /// Measured selectivity of each access path, read by the scheduler through
    /// [`IndexStats::from_index`](crate::schedule::IndexStats::from_index).
    ///
    /// Filled by [`build`](Self::build) only, for the same reason as
    /// [`repr`](Self::repr): a variant prices its delta atom by the delta's
    /// cardinality against the full index's fan-outs, so measuring the delta's
    /// own would buy nothing and cost a pass per round.
    pub fanouts: FanOuts<Cfg::O>,
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
        // `node_ids`, not a bare `from_usize` scan: the bound argument (every
        // routing entry was minted through `TypedRouting::reserve`'s checked
        // path) lives with `node_ids`; an inline scan here would restate the
        // unchecked spelling without the justification.
        Self::build_from(eg, eg.node_ids(), true)
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
        Self::build_from(eg, ids.into_iter(), false)
    }

    /// Shared bucketing core for [`build`](Self::build) and
    /// [`build_delta`](Self::build_delta): index the given node ids into the
    /// four crosscutting maps. Skips subsumed nodes. `full` additionally
    /// records the per-id [`repr`](Self::repr) and [`op`](Self::op) tables and
    /// accumulates [`FanOuts`], which only the full index needs; it is sound
    /// only for the whole-graph id stream, whose ids arrive in ascending order
    /// with no gaps.
    fn build_from<L: LitVal, const TRACK: bool, const PROOFS: bool>(
        eg: &EGraph<Cfg, L, TRACK, PROOFS>,
        ids: impl Iterator<Item = Cfg::G>,
        full: bool,
    ) -> Self {
        let mut by_op: FastMap<Cfg::O, SortedVec<Cfg::G>> = FastMap::default();
        let mut by_repr: FastMap<Cfg::G, SortedVec<Cfg::G>> = FastMap::default();
        let mut by_child_pos: FastMap<(Cfg::G, Cfg::Index), SortedVec<Cfg::G>> = FastMap::default();
        let mut by_contains: FastMap<Cfg::G, SortedVec<Cfg::G>> = FastMap::default();
        let mut indexed = 0usize;

        // Per-id tables, filled only for the whole-graph stream. Both reads are
        // made anyway for the bucketing below, so recording them here costs a
        // push; a separate pass would repeat 1.2 M routing-table walks a round.
        // A subsumed node is skipped for bucketing but still needs its slot, so
        // the tables stay indexable by node id.
        let mut repr_tab: Vec<Cfg::G> = Vec::new();
        let mut op_tab: Vec<Cfg::O> = Vec::new();
        if full {
            repr_tab.reserve(eg.node_count());
            op_tab.reserve(eg.node_count());
        }

        for gid in ids {
            let op = eg.node_op(gid);
            let repr = eg.class_repr(gid);
            if full {
                debug_assert_eq!(repr_tab.len(), gid.to_usize());
                repr_tab.push(repr);
                op_tab.push(op);
            }
            if eg.node_flags(gid) & crate::node_types::FLAG_SUBSUMED != 0 {
                continue;
            }

            by_op.entry(op).or_default().push_unordered(gid);
            by_repr.entry(repr).or_default().push_unordered(gid);
            indexed += 1;

            // The counter is `Cfg::Index`-wide and checked. A variadic node's arity is
            // a span in the child pool, so it is bounded by this word and by nothing
            // narrower; as a `u32` this wrapped, and the child at position 2^32 was filed
            // in bucket 0 — where a pattern written for the first argument would match it.
            let mut pos = <Cfg::Index as IndexLike>::min();
            let is_variadic = eg.for_each_child(gid, |child, _mult| {
                let child_repr = eg.class_repr(child);
                by_child_pos
                    .entry((child_repr, pos))
                    .or_default()
                    .push_unordered(gid);
                pos = crate::containers::index_like::checked_incr(pos)
                    .expect("node arity exceeds EGraphConfig::Index; configure a wider index word");
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
                        by_contains.entry(cr).or_default().push_unordered(gid);
                    }
                });
            }
        }

        fn finalize<K: Eq + std::hash::Hash, G: DenseId>(map: &mut FastMap<K, SortedVec<G>>) {
            for v in map.values_mut() {
                v.sort_dedup();
            }
        }

        finalize(&mut by_op);
        finalize(&mut by_repr);
        finalize(&mut by_child_pos);
        finalize(&mut by_contains);
        let fanouts = if full {
            Self::measure_fanouts(&op_tab, &by_repr, &by_child_pos, &by_contains, indexed)
        } else {
            FanOuts::default()
        };

        Self {
            by_op,
            by_repr,
            by_child_pos,
            by_contains,
            repr: repr_tab,
            op: op_tab,
            fanouts,
        }
    }

    /// Measure each access path's size-biased mean bucket size from the
    /// finished buckets.
    ///
    /// One pass over `by_child_pos` and `by_contains`, tallying each bucket's
    /// parents by operator, because those two maps are keyed by child class
    /// alone while the join always intersects them with `by_op[op]`: the
    /// quantity the scheduler needs is the bucket restricted to one operator,
    /// and on `math-microbenchmark` the two operators of one query differ in it
    /// by three orders of magnitude. The tally is an array indexed by the
    /// operator's dense id, so a bucket costs one increment per parent and no
    /// hashing.
    ///
    /// The operator of each bucket entry comes from `op_tab` — the [`op`](Self::op)
    /// table this build just filled — rather than from `EGraph::node_op`: the
    /// pass visits every bucket entry, which is several times the node count.
    fn measure_fanouts(
        op_tab: &[Cfg::O],
        by_repr: &FastMap<Cfg::G, SortedVec<Cfg::G>>,
        by_child_pos: &FastMap<(Cfg::G, Cfg::Index), SortedVec<Cfg::G>>,
        by_contains: &FastMap<Cfg::G, SortedVec<Cfg::G>>,
        indexed: usize,
    ) -> FanOuts<Cfg::O> {
        // (sum of bucket sizes, sum of their squares) per key set.
        let mut cp: FastMap<(Cfg::O, usize), (u128, u128)> = FastMap::default();
        let mut ct: FastMap<Cfg::O, (u128, u128)> = FastMap::default();
        // Indexed by the operator's dense id, grown on demand rather than sized
        // from the registry: the registry exposes no count, and the ids that
        // occur here are exactly the ones the buckets hold.
        let mut tally: Vec<u32> = Vec::new();
        let mut touched: Vec<usize> = Vec::new();

        let tally_bucket =
            |bucket: &SortedVec<Cfg::G>, tally: &mut Vec<u32>, touched: &mut Vec<usize>| {
                touched.clear();
                for &gid in bucket.as_slice() {
                    let o = op_tab[gid.to_usize()].to_usize();
                    if o >= tally.len() {
                        tally.resize(o + 1, 0);
                    }
                    if tally[o] == 0 {
                        touched.push(o);
                    }
                    tally[o] += 1;
                }
            };

        for (&(_child, pos), bucket) in by_child_pos.iter() {
            tally_bucket(bucket, &mut tally, &mut touched);
            for &o in touched.iter() {
                let c = u128::from(tally[o]);
                let e = cp
                    .entry((Cfg::O::from_usize(o), pos.as_usize()))
                    .or_insert((0, 0));
                e.0 += c;
                e.1 += c * c;
                tally[o] = 0;
            }
        }
        for bucket in by_contains.values() {
            tally_bucket(bucket, &mut tally, &mut touched);
            for &o in touched.iter() {
                let c = u128::from(tally[o]);
                let e = ct.entry(Cfg::O::from_usize(o)).or_insert((0, 0));
                e.0 += c;
                e.1 += c * c;
                tally[o] = 0;
            }
        }

        let biased = |(sum, sq): &(u128, u128)| -> f64 {
            if *sum == 0 {
                1.0
            } else {
                *sq as f64 / *sum as f64
            }
        };
        let (class_sum, class_sq) = by_repr.values().fold((0u128, 0u128), |(s, q), b| {
            let c = b.len() as u128;
            (s + c, q + c * c)
        });

        FanOuts {
            by_repr: biased(&(class_sum, class_sq)),
            by_child_pos: cp.iter().map(|(&k, v)| (k, biased(v))).collect(),
            by_contains: ct.iter().map(|(&k, v)| (k, biased(v))).collect(),
            nodes: indexed,
        }
    }

    /// This build's class representative for `id`, or `None` for an id minted
    /// after the build (and so present in no bucket) or on a delta store, which
    /// defers the mapping to its full index.
    #[inline]
    pub fn round_repr(&self, id: Cfg::G) -> Option<Cfg::G> {
        self.repr.get(id.to_usize()).copied()
    }

    /// The operator of `id` as of this build, or `None` when the table is not
    /// filled (a delta store) or `id` postdates the build. See [`op`](Self::op).
    #[inline]
    pub fn round_op(&self, id: Cfg::G) -> Option<Cfg::O> {
        self.op.get(id.to_usize()).copied()
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
    pub fn iter_by_child_pos(
        &self,
        child_repr: Cfg::G,
        pos: Cfg::Index,
    ) -> SortedVecCursor<'_, Cfg::G> {
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
    // The inherent cursor `step` is now crate-private in containers-verus
    // (it shadowed this guarded trait impl); tests step through the trait.
    use crate::egraph::EGraph31;
    use crate::leapfrog::SortedCursor;
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
                    c.pos(),
                    expected_pos(vals, 0, t),
                    "seek({t}) on {vals:?} landed at {}",
                    c.pos()
                );
                if c.is_valid() {
                    assert!(c.key().to_usize() >= t, "landed below target");
                    // First such key: the predecessor must be strictly below.
                    if c.pos() > 0 {
                        assert!(vals[c.pos() - 1] < t, "skipped a key ≥ target");
                    }
                }
            }
        }

        fn run_seek_sequence_is_monotone<G: DenseId>(vals: &[usize], ts: &[usize]) {
            let data: Vec<G> = vals.iter().map(|&v| G::from_usize(v)).collect();
            let mut c = SortedVecCursor::new(&data);
            let mut prev = c.pos();
            let mut from = 0usize;
            for &t in ts {
                c.seek(G::from_usize(t));
                assert!(c.pos() >= prev, "pos went backwards: {prev} -> {}", c.pos());
                assert!(c.pos() <= data.len(), "pos {} out of bounds", c.pos());
                // Against the linear reference, from wherever the cursor was.
                assert_eq!(
                    c.pos(),
                    expected_pos(vals, from, t),
                    "seek({t}) mid-sequence"
                );
                prev = c.pos();
                from = c.pos();
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
                assert_eq!(c.pos(), model, "cursor diverged from the model");
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
            assert_eq!(c.pos(), data.len());
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
            assert_eq!(c.pos(), 0);
            assert!(!c.is_valid());

            let one = [crate::id::ENodeId::from_usize(5)];
            for (t, want) in [(0usize, 0usize), (5, 0), (6, 1)] {
                let mut c = SortedVecCursor::new(&one);
                c.seek(crate::id::ENodeId::from_usize(t));
                assert_eq!(c.pos(), want, "single-element seek({t})");
            }

            // Seeking on an already-exhausted cursor is a no-op, not a panic.
            let mut c = SortedVecCursor::new(&one);
            c.step();
            assert!(!c.is_valid());
            c.seek(crate::id::ENodeId::from_usize(0));
            assert_eq!(c.pos(), 1);
            c.seek(crate::id::ENodeId::from_usize(99));
            assert_eq!(c.pos(), 1);
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
                assert_eq!(c.pos(), 2);
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
