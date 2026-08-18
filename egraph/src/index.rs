// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Transient sorted indices for leapfrog triejoin, bulk-rebuilt from e-graph state.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::{DenseId, IndexLike};
use crate::egraph::EGraph;
use crate::literal::LitVal;
use semi_persistent_containers::{DenseSpanMap, SpanArena};
use std::collections::HashMap;

/// Hasher for the statistics maps.
///
/// The index families themselves are no longer hashed: they are keyed by a
/// dense integer and read by array index (see [`IndexStore`]). What is left
/// hashed is per-operator bookkeeping, whose keys are dense op ids, and there
/// std's default SipHash still buys DoS resistance no internal key needs.
///
/// foldhash rather than `rustc-hash` or a bespoke passthrough because it is
/// already the workspace's hasher: hashbrown 0.17's default, hence what
/// production `Map` and verified `SpMap` both hash with (see the note on
/// `foldhash` in the workspace `Cargo.toml`). One hasher across the workspace is
/// worth more than a marginal per-probe difference between the fast options.
pub type FastMap<K, V> = HashMap<K, V, foldhash::fast::RandomState>;

/// Cursor into a bucket slice: the **verified** galloping cursor from
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
/// path, so it prices the *expected* probe and not the individual one. Two
/// refinements attack that from opposite ends: per-binding driver selection
/// (S3) at execution, and sampled cross-index selectivity (S5) at plan time,
/// which replaces this number with the mean bucket the emitter atom's own keys
/// select. See [`IndexSampler`].
#[derive(Clone, Debug)]
pub struct FanOuts<O> {
    /// Nodes in the class a `ByRepr` probe lands in.
    pub by_repr: f64,
    /// Skew of each access path: size-biased mean over plain mean bucket size.
    /// 1 on a flat distribution, about H*K/N on one hub bucket of size H among
    /// K near-empty buckets. Drives per-rule scheduling-mode auto-selection
    /// (`saturate::rule_skew`): a skewed path is where a per-round static atom
    /// order is wrong for the bindings that hit the hub.
    pub by_child_pos_skew: FastMap<(O, usize), f64>,
    /// Skew counterpart of [`by_contains`](Self::by_contains).
    pub by_contains_skew: FastMap<O, f64>,
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
            by_child_pos_skew: FastMap::default(),
            by_contains_skew: FastMap::default(),
            by_child_pos: FastMap::default(),
            by_contains: FastMap::default(),
            nodes: 0,
        }
    }
}

/// The `(key, value)` streams the four families are built from, kept alive
/// across rounds.
///
/// A round builds a full index and, under semi-naive evaluation, a delta index;
/// both are dropped at the end of the round. The streams are proportional to the
/// node count and to the total arity, so allocating them per build would mean
/// faulting in tens of megabytes eleven times over a saturation of
/// `math-microbenchmark`. One scratch threaded through the round loop keeps the
/// pages resident and the capacity at the high-water mark.
///
/// The stream buffers hold no state between builds: [`IndexStore::build_with`]
/// clears them on entry, and the built [`DenseSpanMap`]s own copies of what they
/// held. The **span arenas** are the opposite: they are kept precisely so their
/// allocation and their generation stamp survive, and their leftover content is
/// what the stamp invalidates.
///
/// Two index stores are alive at once under semi-naive evaluation (the full
/// index and the round's delta), so the arenas are kept in two sets of four
/// rather than one: a family's key space is stable across rounds, so pairing
/// each family with its own arena keeps the table at the size that family needs
/// instead of thrashing it between a 2 M-key and a 100-key build.
///
/// An arena is handed out by [`IndexStore::build_from`] and comes back through
/// [`IndexStore::recycle_into`]. A caller that forgets to recycle loses only the
/// reuse: the next build allocates a fresh arena and is correct, just slower.
pub struct IndexScratch<Cfg: EGraphConfig> {
    by_op: Vec<(usize, Cfg::G)>,
    by_repr: Vec<(usize, Cfg::G)>,
    by_child_pos: Vec<(usize, Cfg::G)>,
    by_contains: Vec<(usize, Cfg::G)>,
    /// Child classes already filed for the node being visited, so a variadic
    /// node contributes each distinct child to `by_contains` once.
    seen: Vec<Cfg::G>,
    /// Span arenas for the full index's four families, indexed by
    /// [`FAM_OP`]..[`FAM_CONTAINS`].
    arenas_full: [Option<SpanArena>; 4],
    /// Span arenas for the delta index's four families.
    arenas_delta: [Option<SpanArena>; 4],
}

/// Family slots in [`IndexScratch`]'s arena arrays, in the order the build
/// visits them.
pub(crate) const FAM_OP: usize = 0;
pub(crate) const FAM_REPR: usize = 1;
pub(crate) const FAM_CHILD_POS: usize = 2;
pub(crate) const FAM_CONTAINS: usize = 3;

impl<Cfg: EGraphConfig> Default for IndexScratch<Cfg> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Cfg: EGraphConfig> IndexScratch<Cfg> {
    pub fn new() -> Self {
        Self {
            by_op: Vec::new(),
            by_repr: Vec::new(),
            by_child_pos: Vec::new(),
            by_contains: Vec::new(),
            seen: Vec::new(),
            arenas_full: [None, None, None, None],
            arenas_delta: [None, None, None, None],
        }
    }

    fn clear(&mut self) {
        self.by_op.clear();
        self.by_repr.clear();
        self.by_child_pos.clear();
        self.by_contains.clear();
        self.seen.clear();
    }

    /// The arena for one family, or a fresh one the first time round.
    fn take_arena(&mut self, full: bool, fam: usize) -> SpanArena {
        let slot = if full {
            &mut self.arenas_full[fam]
        } else {
            &mut self.arenas_delta[fam]
        };
        slot.take().unwrap_or_default()
    }

    /// Put a family's arena back for the next round to reuse.
    fn put_arena(&mut self, full: bool, fam: usize, arena: SpanArena) {
        let slot = if full {
            &mut self.arenas_full[fam]
        } else {
            &mut self.arenas_delta[fam]
        };
        *slot = Some(arena);
    }

    /// Total span-table capacity held across all eight arenas, in entries.
    ///
    /// Read by `phase_timing` so the memory the reuse keeps resident is
    /// reported rather than assumed; a recycled table is held for the whole run
    /// where a per-build table was freed each round.
    pub fn arena_capacity(&self) -> usize {
        self.arenas_full
            .iter()
            .chain(self.arenas_delta.iter())
            .filter_map(|a| a.as_ref())
            .map(|a| a.capacity())
            .sum()
    }
}

/// All indices for leapfrog join, bulk-rebuilt after each e-graph rebuild.
///
/// Each family is a [`DenseSpanMap`]: one flat pool of node ids per family, plus
/// a span table saying where each key's run starts and how long it is. Every key
/// is a dense integer (an op id, a class id, or a `(position, class)` pair
/// flattened into one), so a probe is an array index and a slice, not a hash and
/// a pointer chase into a per-key `Vec`. The container's `refines()` pins each
/// key's slice to the order-preserving filter of the build stream down to that
/// key, which is what makes the two-pass counting build substitutable for the
/// per-key push it replaces.
pub struct IndexStore<Cfg: EGraphConfig> {
    /// `by_op[op]` -> node ids with that operator, keyed by the op's dense id.
    pub by_op: DenseSpanMap<Cfg::G>,
    /// `by_repr[repr]` -> node ids in that e-class, keyed by the class
    /// representative's id (see [`repr`](Self::repr) for which
    /// canonicalization).
    pub by_repr: DenseSpanMap<Cfg::G>,
    /// `by_child_pos[pos * stride + child_repr]` -> parent node ids with
    /// `child_repr` at `pos`.
    ///
    /// The two-dimensional key is flattened by `DenseSpanMap::composite_key`,
    /// whose injectivity for a second component below the stride is
    /// `lemma_composite_key_injective`. Position-major rather than class-major
    /// so that one pattern position's keys are one contiguous run of the span
    /// table, and so that the key is computable during the build's single walk:
    /// the stride is the node bound, known before the walk, whereas the number
    /// of distinct positions is only known after it.
    ///
    /// The position is [`Cfg::Index`](crate::config::EGraphConfig::Index)-wide: it is an
    /// offset into one node's children, and a variadic node's children are a span in the
    /// child pool, which that word already sizes. See [`IndexLookup::ByChildPos`].
    ///
    /// [`IndexLookup::ByChildPos`]: crate::schedule::IndexLookup::ByChildPos
    pub by_child_pos: DenseSpanMap<Cfg::G>,
    /// `by_contains[child_repr]` -> variadic parent node ids (A/AC/ACI/PlainN).
    pub by_contains: DenseSpanMap<Cfg::G>,
    /// Stride of the [`by_child_pos`](Self::by_child_pos) composite key: the
    /// node bound this index was built at. A probe class at or above it belongs
    /// to no bucket of this build and resolves to the empty slice, which is what
    /// an absent key resolved to when the family was a hash map.
    pub child_pos_stride: usize,
    /// `repr[id]` — the class representative of every node id as of this build.
    ///
    /// The three keyed families above are keyed by *this* canonicalization, and
    /// it stops being the e-graph's the moment the round's first rule merges a
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

/// Build one family from its stream into a caller-owned span arena.
///
/// `num_keys` is the largest key the stream carries plus one, accumulated as the
/// stream is written, so `try_build_in`'s range check cannot fail and the span
/// table is no longer than the keys in use.
///
/// The arena is the recycled span table: it outlives the map built into it, and
/// a build bumps its generation stamp and writes only the keys its stream
/// carries, so a key an earlier build left behind carries an older stamp and
/// reads as empty. That is what makes the build proportional to the stream and
/// the keys it occupies rather than to the key space — the term
/// `comparison/span-table-sparsity.md` measures. The container states the
/// stale-reads-empty property in `build_in`'s ensures, so nothing here has to
/// clear the table to be correct.
fn build_family<G: DenseId>(
    arena: SpanArena,
    stream: &[(usize, G)],
    num_keys: usize,
) -> DenseSpanMap<G> {
    DenseSpanMap::try_build_in(arena, stream, num_keys).unwrap_or_else(|_| {
        panic!("num_keys is the stream's own key bound, accumulated as it was written")
    })
}

/// Visit every key with at least one value.
///
/// Iterates the map's occupancy list rather than scanning `0..len()`, so the
/// pass costs the occupied keys and not the key space — the last place the
/// stamped build's `O(stream + occupied)` shape was not carried through to the
/// consumer. `occupied_keys` ensures the list holds exactly the occupied keys
/// and that every one of them is in range, and `lemma_occ_injective` that it
/// holds each of them once, so this visits what the scan visited.
///
/// The order is first occurrence in the build stream rather than ascending key.
/// Every caller here is a count or a sum over the buckets, so the order does not
/// reach the result; a caller that needed ascending keys would have to sort.
#[inline]
fn for_each_occupied<G: DenseId>(m: &DenseSpanMap<G>, mut f: impl FnMut(usize, &[G])) {
    for &k in m.occupied_keys() {
        f(k, m.get(k));
    }
}

/// Debug-only check that every bucket is ascending in node id.
///
/// The join relies on it: `SortedVecCursor::seek` is specified against a sorted
/// slice, and `Difference`'s delta cursor and chapter 20's delta-suffix logic
/// both assume a bucket is a monotone run. It holds by construction, because the
/// build stream is written in ascending node id and `lemma_view_sorted` carries
/// any ordering of the stream into every per-key slice: the slice *is* the
/// stream's order-preserving filter. So this asserts the hypothesis of that
/// lemma's conclusion rather than re-deriving it. Strictness additionally
/// records that no node is filed under one key twice, which is what makes the
/// per-bucket `dedup` this build no longer performs unnecessary.
#[inline]
fn debug_assert_id_sorted<G: DenseId>(m: &DenseSpanMap<G>, family: &str) {
    #[cfg(debug_assertions)]
    for_each_occupied(m, |k, b| {
        debug_assert!(
            b.windows(2).all(|w| w[0] < w[1]),
            "{family}: bucket {k} is not strictly ascending in node id \
             (lemma_view_sorted's hypothesis, the ascending build stream, was violated)"
        );
    });
    #[cfg(not(debug_assertions))]
    let _ = (m, family);
}

impl<Cfg: EGraphConfig> IndexStore<Cfg>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    /// Bulk-rebuild all indices from the current e-graph state.
    /// Call after `eg.rebuild()`.
    ///
    /// Allocates its own scratch; a caller that builds an index per round should
    /// use [`build_with`](Self::build_with) and keep one.
    pub fn build<L: LitVal, const TRACK: bool, const PROOFS: bool>(
        eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    ) -> Self {
        Self::build_with(eg, &mut IndexScratch::new())
    }

    /// [`build`](Self::build), reusing `scratch`'s stream buffers.
    pub fn build_with<L: LitVal, const TRACK: bool, const PROOFS: bool>(
        eg: &EGraph<Cfg, L, TRACK, PROOFS>,
        scratch: &mut IndexScratch<Cfg>,
    ) -> Self {
        // `node_ids`, not a bare `from_usize` scan: the bound argument (every
        // routing entry was minted through `TypedRouting::reserve`'s checked
        // path) lives with `node_ids`; an inline scan here would restate the
        // unchecked spelling without the justification.
        Self::build_from(eg, eg.node_ids(), true, scratch)
    }

    /// Build the per-round **delta** index from the touched-node log: the
    /// same four crosscutting families as [`build`](Self::build), but restricted
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
        Self::build_delta_with(eg, touched, &mut IndexScratch::new())
    }

    /// [`build_delta`](Self::build_delta), reusing `scratch`'s stream buffers.
    pub fn build_delta_with<L: LitVal, const TRACK: bool, const PROOFS: bool>(
        eg: &EGraph<Cfg, L, TRACK, PROOFS>,
        touched: &[Cfg::G],
        scratch: &mut IndexScratch<Cfg>,
    ) -> Self {
        let ids: Vec<Cfg::G> = {
            let _t = crate::phase_timing::Timer::start(crate::phase_timing::DELTA_DEDUP);
            let mut ids: Vec<Cfg::G> = touched.to_vec();
            ids.sort_unstable();
            ids.dedup();
            ids
        };
        Self::build_from(eg, ids.into_iter(), false, scratch)
    }

    /// Hand this store's four span arenas back to `scratch` for the next round.
    ///
    /// `full` says which set of slots they came from, which the caller knows
    /// because it chose which build produced this store. Consuming `self` is
    /// what makes the hand-back safe: the maps' pools and the arenas' span
    /// tables are separate allocations, and only the arenas survive.
    ///
    /// Not calling this is a performance bug and not a correctness one — the
    /// next build allocates a fresh arena — so it is deliberately an ordinary
    /// method rather than a `Drop` impl, which could not name the scratch.
    pub fn recycle_into(self, scratch: &mut IndexScratch<Cfg>, full: bool) {
        scratch.put_arena(full, FAM_OP, self.by_op.recycle());
        scratch.put_arena(full, FAM_REPR, self.by_repr.recycle());
        scratch.put_arena(full, FAM_CHILD_POS, self.by_child_pos.recycle());
        scratch.put_arena(full, FAM_CONTAINS, self.by_contains.recycle());
    }

    /// Shared bucketing core for [`build`](Self::build) and
    /// [`build_delta`](Self::build_delta): stream the given node ids into the
    /// four families' `(key, value)` buffers, then hand each buffer to the
    /// container's two-pass counting build.
    ///
    /// Skips subsumed nodes. `full` additionally records the per-id
    /// [`repr`](Self::repr) and [`op`](Self::op) tables and accumulates
    /// [`FanOuts`], which only the full index needs; it is sound only for the
    /// whole-graph id stream, whose ids arrive in ascending order with no gaps.
    ///
    /// Ids are visited in ascending order in both callers, because `node_ids()`
    /// is ascending and `build_delta` sorts, so every family's stream is
    /// ascending in its value and the container's filter refinement hands that
    /// ordering to each bucket unchanged (see [`debug_assert_id_sorted`]).
    fn build_from<L: LitVal, const TRACK: bool, const PROOFS: bool>(
        eg: &EGraph<Cfg, L, TRACK, PROOFS>,
        ids: impl Iterator<Item = Cfg::G>,
        full: bool,
        scratch: &mut IndexScratch<Cfg>,
    ) -> Self {
        scratch.clear();
        // Stride of the `by_child_pos` composite key. Read before the walk,
        // because the key must be computable as each child is visited.
        let stride = eg.node_count();
        let mut indexed = 0usize;

        // Largest key each family's stream carries, plus one. Accumulated
        // rather than assumed so the span tables are no longer than the keys in
        // use: an op registry of 113 entries gets 113 spans, not one per node.
        let (mut op_keys, mut repr_keys, mut cp_keys, mut ct_keys) = (0usize, 0, 0, 0);

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

        let (walk_slot, span_base) = if full {
            (
                crate::phase_timing::FULL_WALK,
                crate::phase_timing::FULL_SPAN_OP,
            )
        } else {
            (
                crate::phase_timing::DELTA_WALK,
                crate::phase_timing::DELTA_SPAN_OP,
            )
        };
        let walk_timer = crate::phase_timing::Timer::start(walk_slot);

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

            let ok = op.to_usize();
            op_keys = op_keys.max(ok + 1);
            scratch.by_op.push((ok, gid));
            let rk = repr.to_usize();
            repr_keys = repr_keys.max(rk + 1);
            scratch.by_repr.push((rk, gid));
            indexed += 1;

            // The position counter is `Cfg::Index`-wide and checked. A variadic node's
            // arity is a span in the child pool, so it is bounded by this word and by
            // nothing narrower; as a `u32` this wrapped, and the child at position 2^32
            // was filed in bucket 0, where a pattern written for the first argument
            // would match it.
            let arity = {
                let cp = &mut scratch.by_child_pos;
                let mut pos = <Cfg::Index as IndexLike>::min();
                eg.for_each_child(gid, |child, _mult| {
                    let child_repr = eg.class_repr(child).to_usize();
                    let key =
                        DenseSpanMap::<Cfg::G>::composite_key(pos.as_usize(), child_repr, stride)
                            .expect("child class is below the node bound and the product fits");
                    cp_keys = cp_keys.max(key + 1);
                    cp.push((key, gid));
                    pos = crate::containers::index_like::checked_incr(pos).expect(
                        "node arity exceeds EGraphConfig::Index; configure a wider index word",
                    );
                })
            };
            // For variadic nodes (arity > 3 from PlainN/A/AC/ACI), also populate by_contains
            if arity > 3
                || matches!(
                    eg.node_ref(gid),
                    crate::typed_routing::NodeRef::Seq(_)
                        | crate::typed_routing::NodeRef::MSet(_)
                        | crate::typed_routing::NodeRef::Set(_)
                        | crate::typed_routing::NodeRef::PlainN(_)
                )
            {
                let seen = &mut scratch.seen;
                let ct = &mut scratch.by_contains;
                seen.clear(); // dedup within one node
                eg.for_each_child(gid, |child, _mult| {
                    let cr = eg.class_repr(child);
                    if !seen.contains(&cr) {
                        seen.push(cr);
                        let k = cr.to_usize();
                        ct_keys = ct_keys.max(k + 1);
                        ct.push((k, gid));
                    }
                });
            }
        }

        walk_timer.stop();

        // Take all four arenas before the builds: each build borrows its stream
        // out of the same scratch, so the mutable borrows have to be finished
        // first.
        let (a_op, a_repr, a_cp, a_ct) = (
            scratch.take_arena(full, FAM_OP),
            scratch.take_arena(full, FAM_REPR),
            scratch.take_arena(full, FAM_CHILD_POS),
            scratch.take_arena(full, FAM_CONTAINS),
        );
        let by_op = {
            let _t = crate::phase_timing::Timer::start(span_base);
            build_family(a_op, &scratch.by_op, op_keys)
        };
        let by_repr = {
            let _t = crate::phase_timing::Timer::start(span_base + 1);
            build_family(a_repr, &scratch.by_repr, repr_keys)
        };
        let by_child_pos = {
            let _t = crate::phase_timing::Timer::start(span_base + 2);
            build_family(a_cp, &scratch.by_child_pos, cp_keys)
        };
        let by_contains = {
            let _t = crate::phase_timing::Timer::start(span_base + 3);
            build_family(a_ct, &scratch.by_contains, ct_keys)
        };
        Self::record_shape(full, indexed, &by_child_pos);
        debug_assert_id_sorted(&by_op, "by_op");
        debug_assert_id_sorted(&by_repr, "by_repr");
        debug_assert_id_sorted(&by_child_pos, "by_child_pos");
        debug_assert_id_sorted(&by_contains, "by_contains");

        let fanouts = if full {
            let _t = crate::phase_timing::Timer::start(crate::phase_timing::FULL_FANOUTS);
            Self::measure_fanouts(
                &op_tab,
                &by_repr,
                &by_child_pos,
                &by_contains,
                stride,
                indexed,
            )
        } else {
            FanOuts::default()
        };

        Self {
            by_op,
            by_repr,
            by_child_pos,
            by_contains,
            child_pos_stride: stride,
            repr: repr_tab,
            op: op_tab,
            fanouts,
        }
    }

    /// Record the `by_child_pos` key-space shape for `phase_timing`.
    ///
    /// The span table is dense over the composite key space, so its length is
    /// what a build pays whether or not the keys occur, and the ratio of that
    /// length to the values it addresses is the sparsity this measures. The
    /// occupied-key count is a pass over the map's occupancy list, so the whole
    /// helper is still skipped unless the accounting is switched on.
    #[inline]
    fn record_shape(full: bool, indexed: usize, by_child_pos: &DenseSpanMap<Cfg::G>) {
        use crate::phase_timing as pt;
        if !pt::enabled() {
            return;
        }
        let (nodes, keys, values, nonempty) = if full {
            (
                pt::C_FULL_NODES,
                pt::C_FULL_CP_KEYS,
                pt::C_FULL_CP_VALUES,
                pt::C_FULL_CP_NONEMPTY,
            )
        } else {
            (
                pt::C_DELTA_IDS,
                pt::C_DELTA_CP_KEYS,
                pt::C_DELTA_CP_VALUES,
                pt::C_DELTA_CP_NONEMPTY,
            )
        };
        pt::count(nodes, indexed as u64);
        pt::count(keys, by_child_pos.len() as u64);
        pt::count(values, by_child_pos.total() as u64);
        let mut occupied = 0u64;
        for_each_occupied(by_child_pos, |_, _| occupied += 1);
        pt::count(nonempty, occupied);
    }

    /// Measure each access path's size-biased mean bucket size from the
    /// finished families.
    ///
    /// One pass over the occupied keys of `by_child_pos` and `by_contains`,
    /// tallying each bucket's parents by operator, because those two families
    /// are keyed by child class
    /// alone (`by_contains`) or by child class and position (`by_child_pos`)
    /// while the join always intersects them with `by_op[op]`: the quantity the
    /// scheduler needs is the bucket restricted to one operator, and on
    /// `math-microbenchmark` the two operators of one query differ in it by
    /// three orders of magnitude. The tally is an array indexed by the
    /// operator's dense id, so a bucket costs one increment per parent and no
    /// hashing.
    ///
    /// `by_repr`'s number reads no bucket entry: a size-biased mean over bucket
    /// sizes is a sum of span lengths over the occupied keys.
    ///
    /// The operator of each bucket entry comes from `op_tab` — the [`op`](Self::op)
    /// table this build just filled — rather than from `EGraph::node_op`: the
    /// pass visits every bucket entry, which is several times the node count.
    fn measure_fanouts(
        op_tab: &[Cfg::O],
        by_repr: &DenseSpanMap<Cfg::G>,
        by_child_pos: &DenseSpanMap<Cfg::G>,
        by_contains: &DenseSpanMap<Cfg::G>,
        stride: usize,
        indexed: usize,
    ) -> FanOuts<Cfg::O> {
        // (sum of bucket sizes, sum of their squares, bucket count) per key set.
        let mut cp: FastMap<(Cfg::O, usize), (u128, u128, u128)> = FastMap::default();
        let mut ct: FastMap<Cfg::O, (u128, u128, u128)> = FastMap::default();
        // Indexed by the operator's dense id, grown on demand rather than sized
        // from the registry: the registry exposes no count, and the ids that
        // occur here are exactly the ones the buckets hold.
        // u64, not u32: a bucket's per-op count is bounded by the node count,
        // which the 63-bit configuration allows past 2^32.
        let mut tally: Vec<u64> = Vec::new();
        let mut touched: Vec<usize> = Vec::new();

        let tally_bucket = |bucket: &[Cfg::G], tally: &mut Vec<u64>, touched: &mut Vec<usize>| {
            touched.clear();
            for &gid in bucket {
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

        for_each_occupied(by_child_pos, |k, bucket| {
            // Position-major key: the position is the quotient, and `stride` is
            // nonzero because a non-empty bucket means the graph has a node.
            let pos = k / stride;
            tally_bucket(bucket, &mut tally, &mut touched);
            for &o in touched.iter() {
                let c = u128::from(tally[o]);
                let e = cp.entry((Cfg::O::from_usize(o), pos)).or_insert((0, 0, 0));
                e.0 += c;
                e.1 += c * c;
                e.2 += 1;
                tally[o] = 0;
            }
        });
        for_each_occupied(by_contains, |_, bucket| {
            tally_bucket(bucket, &mut tally, &mut touched);
            for &o in touched.iter() {
                let c = u128::from(tally[o]);
                let e = ct.entry(Cfg::O::from_usize(o)).or_insert((0, 0, 0));
                e.0 += c;
                e.1 += c * c;
                e.2 += 1;
                tally[o] = 0;
            }
        });

        let biased = |(sum, sq, _): &(u128, u128, u128)| -> f64 {
            if *sum == 0 {
                1.0
            } else {
                *sq as f64 / *sum as f64
            }
        };
        // Skew = size-biased mean / plain mean = sq * count / sum^2.
        let skew = |(sum, sq, count): &(u128, u128, u128)| -> f64 {
            if *sum == 0 {
                1.0
            } else {
                (*sq as f64 * *count as f64) / (*sum as f64 * *sum as f64)
            }
        };
        let (mut class_sum, mut class_sq) = (0u128, 0u128);
        for_each_occupied(by_repr, |_, b| {
            let c = b.len() as u128;
            class_sum += c;
            class_sq += c * c;
        });

        FanOuts {
            by_repr: biased(&(class_sum, class_sq, 0)),
            by_child_pos_skew: cp.iter().map(|(&k, v)| (k, skew(v))).collect(),
            by_contains_skew: ct.iter().map(|(&k, v)| (k, skew(v))).collect(),
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

    /// Nodes with the given operator; empty when the operator files no node.
    #[inline]
    pub fn nodes_by_op(&self, op: Cfg::O) -> &[Cfg::G] {
        self.by_op.try_get(op.to_usize()).unwrap_or(&[])
    }

    /// Nodes in the given e-class, as this build canonicalized it.
    #[inline]
    pub fn nodes_by_repr(&self, repr: Cfg::G) -> &[Cfg::G] {
        self.by_repr.try_get(repr.to_usize()).unwrap_or(&[])
    }

    /// Parent nodes that have `child_repr` at position `pos`.
    ///
    /// A class at or above the stride, or a position past the deepest one this
    /// build saw, names no key of the span table and yields the empty slice: the
    /// same answer the hash-map family gave for a key it had never inserted.
    #[inline]
    pub fn nodes_by_child_pos(&self, child_repr: Cfg::G, pos: Cfg::Index) -> &[Cfg::G] {
        match DenseSpanMap::<Cfg::G>::composite_key(
            pos.as_usize(),
            child_repr.to_usize(),
            self.child_pos_stride,
        ) {
            Some(k) => self.by_child_pos.try_get(k).unwrap_or(&[]),
            None => &[],
        }
    }

    /// Variadic nodes containing `child_repr`.
    #[inline]
    pub fn nodes_by_contains(&self, child_repr: Cfg::G) -> &[Cfg::G] {
        self.by_contains
            .try_get(child_repr.to_usize())
            .unwrap_or(&[])
    }

    /// Get an iterator over nodes with the given operator.
    pub fn iter_by_op(&self, op: Cfg::O) -> SortedVecCursor<'_, Cfg::G> {
        SortedVecCursor::new(self.nodes_by_op(op))
    }

    /// Get an iterator over nodes in the given e-class.
    pub fn iter_by_repr(&self, repr: Cfg::G) -> SortedVecCursor<'_, Cfg::G> {
        SortedVecCursor::new(self.nodes_by_repr(repr))
    }

    /// Get an iterator over parent nodes that have `child_repr` at position `pos`.
    pub fn iter_by_child_pos(
        &self,
        child_repr: Cfg::G,
        pos: Cfg::Index,
    ) -> SortedVecCursor<'_, Cfg::G> {
        SortedVecCursor::new(self.nodes_by_child_pos(child_repr, pos))
    }

    /// Get an iterator over variadic nodes containing `child_repr`.
    pub fn iter_by_contains(&self, child_repr: Cfg::G) -> SortedVecCursor<'_, Cfg::G> {
        SortedVecCursor::new(self.nodes_by_contains(child_repr))
    }

    /// Per-operator driver-scan cardinalities, for
    /// [`IndexStats`](crate::schedule::IndexStats).
    ///
    /// Only operators that file at least one node are listed, so an absent
    /// operator stays absent rather than arriving with a zero, which is the
    /// distinction the cost model's `or_else` chain reads.
    pub fn op_cardinalities(&self) -> impl Iterator<Item = (Cfg::O, usize)> + '_ {
        (0..self.by_op.len()).filter_map(|k| {
            let n = self.by_op.key_len(k);
            (n > 0).then(|| (Cfg::O::from_usize(k), n))
        })
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
pub struct VariantIndex<'a, Cfg: EGraphConfig> {
    pub full: &'a IndexStore<Cfg>,
    pub delta: &'a IndexStore<Cfg>,
    pub delta_atom: Option<usize>,
}

// Hand-written rather than derived: a derive would bound `Cfg: Clone`, and the
// view is three references whatever `Cfg` is.
impl<Cfg: EGraphConfig> Clone for VariantIndex<'_, Cfg> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<Cfg: EGraphConfig> Copy for VariantIndex<'_, Cfg> {}

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

// ---------------------------------------------------------------------------
// Plan-time sampling
// ---------------------------------------------------------------------------

/// Entries of a bucket read to estimate its operator-restricted length.
///
/// `by_child_pos` and `by_contains` are keyed by child class while every
/// join intersects them with `by_op[op]`, so the length the scheduler needs is
/// the bucket restricted to one operator — the same quantity
/// [`IndexStore::measure_fanouts`] tallies, and for the same reason: the two
/// operators of one query differ in it by three orders of magnitude. Counting
/// it exactly is a pass over the bucket, which on a hub class is hundreds of
/// thousands of loads for one sampled key. Past this many entries the count is
/// taken over an evenly-strided subsample of the bucket and scaled back up,
/// which is the estimator the emitter draw already is, applied once more.
const PROBE_SCAN_CAP: usize = 256;

/// [`CrossSampler`] over one round's indices: the implementation the scheduler
/// gets its samples from.
///
/// Emitter draws come from the slice the atom's semi-naive mode reads, which is
/// the relation it will actually enumerate. Probe buckets come from the full
/// index in every mode, matching [`FanOuts`], which the full build measures and
/// every variant prices against: a variant's delta shows up in the atom's base
/// cardinality, and applying it again to the probe would charge it twice.
///
/// [`CrossSampler`]: crate::schedule::CrossSampler
pub struct IndexSampler<'a, Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool> {
    eg: &'a EGraph<Cfg, L, TRACK, PROOFS>,
    index: VariantIndex<'a, Cfg>,
}

impl<'a, Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    IndexSampler<'a, Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    pub fn new(eg: &'a EGraph<Cfg, L, TRACK, PROOFS>, index: VariantIndex<'a, Cfg>) -> Self {
        Self { eg, index }
    }

    /// The class of `id` as the round's buckets are keyed, mirroring
    /// `ematch::canon`: the build's mapping where it has one, the live
    /// union-find for an id minted after the build.
    #[inline]
    fn canon(&self, id: Cfg::G) -> Cfg::G {
        match self.index.full.round_repr(id) {
            Some(r) => r,
            None => self.eg.find_const(id),
        }
    }

    /// Nodes of `op` in `bucket`, exactly when the bucket is short enough and
    /// by a strided subsample scaled to the bucket's length when it is not.
    fn op_restricted(&self, s: &[Cfg::G], op: Cfg::O) -> usize {
        let n = s.len();
        let op_tab = &self.index.full.op;
        let hits = |g: &Cfg::G| op_tab.get(g.to_usize()).is_some_and(|&o| o == op);
        if n <= PROBE_SCAN_CAP {
            return s.iter().filter(|g| hits(g)).count();
        }
        let seen = (0..PROBE_SCAN_CAP)
            .filter(|j| hits(&s[j * n / PROBE_SCAN_CAP]))
            .count();
        seen * n / PROBE_SCAN_CAP
    }
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    crate::schedule::CrossSampler<Cfg::O> for IndexSampler<'_, Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    fn driver_sample(&self, atom_id: usize, op: Cfg::O, k: usize, out: &mut Vec<usize>) {
        out.clear();
        // `FullMinusDelta` draws from the full side, an upper bound on
        // `full ∖ delta`, for the reason `ematch::cursor_len` gives: a tighter
        // draw would cost the overlap, which is the work being priced.
        let store = match self.index.mode(atom_id) {
            IndexMode::Delta => self.index.delta,
            IndexMode::Full | IndexMode::FullMinusDelta => self.index.full,
        };
        let s = store.nodes_by_op(op);
        let n = s.len();
        if n == 0 || k == 0 {
            return;
        }
        let take = k.min(n);
        out.extend((0..take).map(|j| s[j * n / take].to_usize()));
    }

    fn key_classes(&self, node: usize, site: crate::schedule::KeySite, out: &mut Vec<usize>) {
        use crate::schedule::KeySite;
        let g = Cfg::G::from_usize(node);
        match site {
            KeySite::Node => out.push(self.canon(g).to_usize()),
            // Read through `for_each_child` with a position counter, the same
            // walk `IndexStore::build_from` keys `by_child_pos` with, rather
            // than `EGraph::child_at`, which panics on a multiset node.
            KeySite::Child(pos) => {
                let mut i = 0usize;
                self.eg.for_each_child(g, |c, _| {
                    if i == pos {
                        out.push(self.canon(c).to_usize());
                    }
                    i += 1;
                });
            }
            KeySite::Element => {
                self.eg.for_each_child(g, |c, _| {
                    let cr = self.canon(c).to_usize();
                    if !out.contains(&cr) {
                        out.push(cr);
                    }
                });
            }
        }
    }

    fn probe_len(&self, class: usize, path: crate::schedule::ProbePath, op: Cfg::O) -> usize {
        use crate::schedule::ProbePath;
        let c = Cfg::G::from_usize(class);
        let bucket = match path {
            ProbePath::ChildPos(pos) => {
                let Some(p) = <Cfg::Index as IndexLike>::try_from_usize(pos) else {
                    return 0;
                };
                self.index.full.nodes_by_child_pos(c, p)
            }
            ProbePath::Contains => self.index.full.nodes_by_contains(c),
        };
        self.op_restricted(bucket, op)
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
        let f_nodes = idx.nodes_by_op(f);
        assert_eq!(f_nodes.len(), 2);
        assert!(f_nodes.contains(&fx));
        assert!(f_nodes.contains(&ffx));

        // One g-node
        assert_eq!(idx.nodes_by_op(g).len(), 1);
        assert!(idx.nodes_by_op(g).contains(&gx));

        // One x-node
        assert_eq!(idx.nodes_by_op(x_op).len(), 1);
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
        let class_nodes = idx.nodes_by_repr(repr);
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
        let parents_x_0 = idx.nodes_by_child_pos(x, 0);
        assert_eq!(parents_x_0.len(), 2);
        assert!(parents_x_0.contains(&fx));
        assert!(parents_x_0.contains(&gxy));

        // y is child at pos 1 of gxy only
        let parents_y_1 = idx.nodes_by_child_pos(y, 1);
        assert_eq!(parents_y_1.len(), 1);
        assert!(parents_y_1.contains(&gxy));
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

        /// A sorted, duplicate-free key vector: the shape of every bucket the
        /// build produces, `IndexStore::build_from` streams ids in ascending order
        /// and files each id under a key at most once, and the container's filter
        /// refinement hands that order to the bucket.
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

    /// The `by_child_pos` key is `position * stride + class`, flattened by
    /// `DenseSpanMap::composite_key`; `lemma_composite_key_injective` is why a
    /// parent filed at one position never surfaces in another position's
    /// bucket. A wide node stretches the key space past the binary ops beside
    /// it, which is where a stride mistake would show, and the two negative
    /// cases are the ones an absent hash-map key used to cover: a position
    /// deeper than any node has, and a class at or above the build's node bound.
    #[test]
    fn child_pos_key_separates_positions_and_absent_keys() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let wide = eg.register_opn("w", &[int; 6], int);
        let g = eg.register_op2("g", int, int, int);
        let leaves: Vec<_> = ["a", "b", "c", "d", "e", "f"]
            .iter()
            .map(|n| {
                let o = eg.register_op0(n, int);
                eg.add(o, &[])
            })
            .collect();
        let w = eg.add(wide, &leaves);
        let gg = eg.add(g, &[leaves[0], leaves[5]]);

        let idx = IndexStore::build(&eg);
        // `a` is child 0 of both parents; buckets are ascending in node id.
        assert_eq!(idx.nodes_by_child_pos(leaves[0], 0), &[w, gg]);
        // Position 1 of the wide node is `b`, of `gg` is `f`: neither leaks.
        assert_eq!(idx.nodes_by_child_pos(leaves[1], 1), &[w]);
        assert_eq!(idx.nodes_by_child_pos(leaves[5], 1), &[gg]);
        // The deepest position in use, and the same class one position off it.
        assert_eq!(idx.nodes_by_child_pos(leaves[5], 5), &[w]);
        assert!(idx.nodes_by_child_pos(leaves[0], 5).is_empty());
        // Past the deepest position, and past the node bound.
        assert!(idx.nodes_by_child_pos(leaves[0], 6).is_empty());
        assert!(
            idx.nodes_by_child_pos(crate::id::ENodeId::from_usize(eg.node_count()), 0)
                .is_empty()
        );
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
        let parents = idx.nodes_by_child_pos(repr, 0);
        // After merge, fx and fy are congruent — same node. So 1 entry.
        assert!(parents.contains(&eg.find_const(fx)));
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
        let contains_x = idx.nodes_by_contains(x);
        assert_eq!(contains_x.len(), 2);
        assert!(contains_x.contains(&pxy));
        assert!(contains_x.contains(&pxz));

        // y is contained only in pxy
        let contains_y = idx.nodes_by_contains(y);
        assert_eq!(contains_y.len(), 1);
    }
}
