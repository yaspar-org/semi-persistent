// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Monte-Carlo Graph Search for anti-unification (§3.3).
//!
//! Playout = selection (UCT at OR nodes, a configurable effort selector at
//! AND nodes), expansion, initial rollout (§A.4) for first estimates, then
//! path-only backpropagation: every AND node on the traversed path recomputes
//! its value idempotently from its children (§2.6), composes its children's
//! stored best results into a candidate term, and offers it to its parent's
//! best-result entry (§3.3). That composition step is what lets the search
//! improve past the initial rollout and converge to the exact optimum on
//! exhausted graphs.
//!
//! Implemented policies: UCT selection at OR nodes and three AND-node effort
//! selectors (`lct_and` default, `uct_and`, `round_robin`; §3.3.5). PUCT,
//! priors, and an incremental completion counter are future work; see
//! doc/future/au-associative-operators.md.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::{
    AppendOnlyVec, DenseId, IndexLike, Map, MapToken, ShrinkPolicy, VecP, VecToken,
};
use crate::literal::LitVal;

use super::AuIds31;
use super::ac_repr;
use super::actions::{ActionCache, generate_actions};
use super::egraph_api::{AuSnapshot, ClassOf};
use super::results::BestResults;
use super::space::{CycleMode, SearchSpace};
use super::terms::{TermOp, TermPool, build_best_term, evaluate_generalize_action};
use super::transport::{
    Cell, TransportProblem, TransportProblemF64, solve_transport, solve_transport_f64,
};
use crate::config::AuIds;

/// Effort-allocation selector at AND nodes (§3.3.5). An AND node does not
/// choose an outcome — all children must be solved — so its selector decides
/// where the next unit of refinement effort goes.
///
/// Fairness (§2.5.1 F): `RoundRobin` gives every child equal visits by
/// rotation. `UctAnd`/`LctAnd` are fair through their exploration term,
/// `C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))`, which diverges for any neglected
/// child, so every child is still refined infinitely often.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AndSelector {
    /// `i = counter mod arity; counter += 1` — equal effort by rotation.
    /// Halves playout flux at every 2-child AND level, so certifying a
    /// depth-d branching spine needs ~2^d playouts.
    RoundRobin,
    /// `argmax_i (1 − normalize(Q(child_i))) + C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))`
    /// — refines the most promising (best-normalized-value) child first.
    UctAnd,
    /// `argmin_i (1 − normalize(Q(child_i))) − C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))`
    /// — selects by lower confidence bound, deliberately visiting the weakest
    /// child (an AND result's size is a sum, so its quality is limited by its
    /// worst child). Default: it routes effort to the least-certain child, so
    /// unexpanded/incomplete subtrees receive nearly all flux until they
    /// close, making certification cost proportional to graph size instead of
    /// exponential in depth.
    #[default]
    LctAnd,
}

/// MCGS configuration.
#[derive(Debug, Clone)]
pub struct McgsConfig {
    pub playouts: u64,
    pub cycle_mode: CycleMode,
    /// UCT exploration constant C (§3.3.4). Default √2.
    pub exploration_constant: f64,
    /// Normalization target (§2.5). Default 0.8.
    pub x_target: f64,
    /// Effort allocation at AND nodes (§3.3.5). Default `LctAnd`.
    pub and_selector: AndSelector,
}

impl Default for McgsConfig {
    fn default() -> Self {
        McgsConfig {
            playouts: 1000,
            cycle_mode: CycleMode::AncestorOnly,
            exploration_constant: std::f64::consts::SQRT_2,
            x_target: 0.8,
            and_selector: AndSelector::default(),
        }
    }
}

/// Builder payload for one OR-statistics node. The arena flattens edge state
/// into typed pools when this value is pushed.
struct OrStatsData<AS> {
    /// U(n): the node's first rollout estimate, one permanent unit-weight sample.
    initial_value: f64,
    /// Q(n), recomputed from children on every backpropagation through this node.
    value: f64,
    /// min(best_size(l), best_size(r)): the shared normalization basis.
    min_size: f64,
    /// max(best_size(l), best_size(r)): the shared normalization scale.
    max_size: f64,
    /// Terminal: l == r, exact, or no surviving actions.
    terminal: bool,
    /// Per-action edge visits N(n,a).
    edge_visits: Vec<u64>,
    /// Realized AND statistics per action (None = unrealized).
    edge_and: Vec<Option<AS>>,
}

/// Builder payload for one AND-statistics node. Child arrays are flattened into
/// pools when pushed. Transport map entries are positions in this payload's
/// child list and are converted to absolute typed child-pool IDs by the arena.
struct AndStatsData<OS, O> {
    parent: OS,
    op: O,
    commutative: bool,
    value: f64,
    child_or_stats: Vec<OS>,
    child_counts: Vec<u32>,
    child_visits: Vec<u64>,
    round_robin: u64,
    transport_rows: Vec<u32>,
    transport_cols: Vec<u32>,
    transport_cell_map: Vec<Option<usize>>,
}

/// Borrowed OR-statistics node assembled from aligned arena fields.
struct OrStatsRef<'a, AS> {
    initial_value: f64,
    value: f64,
    min_size: f64,
    max_size: f64,
    terminal: bool,
    edge_visits: &'a [u64],
    edge_and: &'a [Option<AS>],
}

/// Borrowed AND-statistics node assembled from aligned arena fields.
struct AndStatsRef<'a, OS, O, CS> {
    parent: OS,
    op: O,
    commutative: bool,
    value: f64,
    child_or_stats: &'a [OS],
    child_counts: &'a [u32],
    child_visits: &'a [u64],
    round_robin: u64,
    transport_rows: &'a [u32],
    transport_cols: &'a [u32],
    transport_cell_map: &'a [Option<CS>],
}

/// Token for the OR-statistics arena. It contains only tokens issued by the
/// standard semi-persistent containers that own each aligned field.
#[derive(Clone, Copy, Debug)]
struct OrStatsToken {
    or_ids: VecToken,
    min_size: VecToken,
    max_size: VecToken,
    terminal: VecToken,
    edge_spans: VecToken,
    initial_value: VecToken,
    value: VecToken,
    edge_visits: VecToken,
    edge_and: VecToken,
    transport_descs: VecToken,
}

/// OR statistics stored in aligned semi-persistent arenas. Node structure is
/// append-only; mutable values and flattened edge state use VecP.
struct OrStatsArena<A: AuIds, O: DenseId> {
    or_ids: AppendOnlyVec<A::Or>,
    min_size: AppendOnlyVec<f64>,
    max_size: AppendOnlyVec<f64>,
    terminal: AppendOnlyVec<bool>,
    edge_spans: AppendOnlyVec<super::Span<A::OrEdgeStat>>,
    initial_value: VecP<f64, A::Index>,
    value: VecP<f64, A::Index>,
    edge_visits: VecP<u64, A::Index>,
    edge_and: VecP<Option<A::AndStats>, A::Index>,
    transport_descs: AppendOnlyVec<Vec<TransportActionDesc<O, A::Class>>>,
}

/// Preconstruct a typed span and validate its exclusive end and final typed
/// position before any owning arena is mutated.
fn checked_pool_span<I: DenseId>(start: usize, len: usize, pool: &str) -> super::Span<I> {
    let end = start
        .checked_add(len)
        .unwrap_or_else(|| panic!("{pool} span end overflows usize"));
    I::Index::try_from_usize(end)
        .unwrap_or_else(|| panic!("{pool} span end exceeds configured index width"));
    let span = super::Span::new(start, len);
    if len != 0 {
        let _ = I::from_usize(end - 1);
    }
    span
}

impl<A: AuIds, O: DenseId> OrStatsArena<A, O> {
    fn new() -> Self {
        Self {
            or_ids: AppendOnlyVec::new(),
            min_size: AppendOnlyVec::new(),
            max_size: AppendOnlyVec::new(),
            terminal: AppendOnlyVec::new(),
            edge_spans: AppendOnlyVec::new(),
            initial_value: VecP::new(),
            value: VecP::new(),
            edge_visits: VecP::new(),
            edge_and: VecP::new(),
            transport_descs: AppendOnlyVec::new(),
        }
    }

    #[inline]
    fn index<I: DenseId<Index = A::Index>>(id: I) -> A::Index {
        A::Index::try_from_usize(id.to_usize()).expect("MCGS id exceeds configured index width")
    }

    fn len(&self) -> usize {
        self.or_ids.len()
    }

    fn push(
        &mut self,
        or_id: A::Or,
        data: OrStatsData<A::AndStats>,
        transport_descs: Vec<TransportActionDesc<O, A::Class>>,
    ) -> A::OrStats {
        assert_eq!(data.edge_visits.len(), data.edge_and.len());

        let node_len = self.len();
        assert_eq!(self.min_size.len(), node_len);
        assert_eq!(self.max_size.len(), node_len);
        assert_eq!(self.terminal.len(), node_len);
        assert_eq!(self.edge_spans.len(), node_len);
        assert_eq!(self.initial_value.len().as_usize(), node_len);
        assert_eq!(self.value.len().as_usize(), node_len);
        assert_eq!(self.transport_descs.len(), node_len);

        let edge_start = self.edge_visits.len().as_usize();
        assert_eq!(self.edge_and.len().as_usize(), edge_start);
        let id = A::OrStats::from_usize(node_len);
        let edge_span = checked_pool_span::<A::OrEdgeStat>(
            edge_start,
            data.edge_visits.len(),
            "OR edge-statistics pool",
        );

        for visit in data.edge_visits {
            self.edge_visits.push(visit);
        }
        for and_id in data.edge_and {
            self.edge_and.push(and_id);
        }
        self.or_ids.push(or_id);
        self.min_size.push(data.min_size);
        self.max_size.push(data.max_size);
        self.terminal.push(data.terminal);
        self.edge_spans.push(edge_span);
        self.initial_value.push(data.initial_value);
        self.value.push(data.value);
        self.transport_descs.push(transport_descs);
        id
    }

    #[inline]
    fn or_id(&self, id: A::OrStats) -> A::Or {
        *self.or_ids.get(id.to_usize())
    }

    #[inline]
    fn edge_span(&self, id: A::OrStats) -> super::Span<A::OrEdgeStat> {
        *self.edge_spans.get(id.to_usize())
    }

    #[inline]
    fn edge_id(&self, id: A::OrStats, action: usize) -> A::OrEdgeStat {
        let span = self.edge_span(id);
        assert!(action < span.len_usize(), "OR action index out of bounds");
        A::OrEdgeStat::from_usize(span.start_usize() + action)
    }

    fn get(&self, id: A::OrStats) -> OrStatsRef<'_, A::AndStats> {
        let node = Self::index(id);
        let span = self.edge_span(id);
        let range = span.start_usize()..span.end_usize();
        OrStatsRef {
            initial_value: self.initial_value.get(node),
            value: self.value.get(node),
            min_size: *self.min_size.get(id.to_usize()),
            max_size: *self.max_size.get(id.to_usize()),
            terminal: *self.terminal.get(id.to_usize()),
            edge_visits: &self.edge_visits.as_slice().expect("VecP is contiguous")[range.clone()],
            edge_and: &self.edge_and.as_slice().expect("VecP is contiguous")[range],
        }
    }

    #[inline]
    fn transport_descs(&self, id: A::OrStats) -> &[TransportActionDesc<O, A::Class>] {
        self.transport_descs.get(id.to_usize())
    }

    fn set_initial_value(&mut self, id: A::OrStats, value: f64) {
        self.initial_value.set(Self::index(id), value);
    }

    fn set_value(&mut self, id: A::OrStats, value: f64) {
        self.value.set(Self::index(id), value);
    }

    fn bump_edge_visit(&mut self, id: A::OrStats, action: usize) {
        let edge = Self::index(self.edge_id(id, action));
        self.edge_visits.set(edge, self.edge_visits.get(edge) + 1);
    }

    fn set_edge_and(&mut self, id: A::OrStats, action: usize, value: Option<A::AndStats>) {
        let edge = Self::index(self.edge_id(id, action));
        self.edge_and.set(edge, value);
    }

    fn mark(&mut self) -> OrStatsToken {
        OrStatsToken {
            or_ids: self.or_ids.mark(ShrinkPolicy::Never),
            min_size: self.min_size.mark(ShrinkPolicy::Never),
            max_size: self.max_size.mark(ShrinkPolicy::Never),
            terminal: self.terminal.mark(ShrinkPolicy::Never),
            edge_spans: self.edge_spans.mark(ShrinkPolicy::Never),
            initial_value: self.initial_value.mark(ShrinkPolicy::Never),
            value: self.value.mark(ShrinkPolicy::Never),
            edge_visits: self.edge_visits.mark(ShrinkPolicy::Never),
            edge_and: self.edge_and.mark(ShrinkPolicy::Never),
            transport_descs: self.transport_descs.mark(ShrinkPolicy::Never),
        }
    }

    fn is_valid_token(&self, token: &OrStatsToken) -> bool {
        self.or_ids.is_valid_token(&token.or_ids)
            && self.min_size.is_valid_token(&token.min_size)
            && self.max_size.is_valid_token(&token.max_size)
            && self.terminal.is_valid_token(&token.terminal)
            && self.edge_spans.is_valid_token(&token.edge_spans)
            && self.initial_value.is_valid_token(&token.initial_value)
            && self.value.is_valid_token(&token.value)
            && self.edge_visits.is_valid_token(&token.edge_visits)
            && self.edge_and.is_valid_token(&token.edge_and)
            && self.transport_descs.is_valid_token(&token.transport_descs)
    }

    fn restore(&mut self, token: OrStatsToken) {
        assert!(self.is_valid_token(&token), "OrStatsArena: invalid token");
        self.transport_descs.restore(token.transport_descs);
        self.edge_and.restore(token.edge_and);
        self.edge_visits.restore(token.edge_visits);
        self.value.restore(token.value);
        self.initial_value.restore(token.initial_value);
        self.edge_spans.restore(token.edge_spans);
        self.terminal.restore(token.terminal);
        self.max_size.restore(token.max_size);
        self.min_size.restore(token.min_size);
        self.or_ids.restore(token.or_ids);
    }
}

/// Token for the AND-statistics arena. It contains only tokens issued by the
/// standard semi-persistent containers that own each aligned field.
#[derive(Clone, Copy, Debug)]
struct AndStatsToken {
    parent: VecToken,
    op: VecToken,
    commutative: VecToken,
    child_spans: VecToken,
    child_or_stats: VecToken,
    value: VecToken,
    child_counts: VecToken,
    child_visits: VecToken,
    round_robin: VecToken,
    transport_rows: VecToken,
    transport_cols: VecToken,
    transport_cell_map: VecToken,
}

/// AND statistics stored in aligned semi-persistent arenas. Child state is
/// flattened and addressed by `A::AndChildStat` spans and IDs.
struct AndStatsArena<A: AuIds, O: DenseId> {
    parent: AppendOnlyVec<A::OrStats>,
    op: AppendOnlyVec<O>,
    commutative: AppendOnlyVec<bool>,
    child_spans: AppendOnlyVec<super::Span<A::AndChildStat>>,
    child_or_stats: AppendOnlyVec<A::OrStats>,
    value: VecP<f64, A::Index>,
    child_counts: VecP<u32, A::Index>,
    child_visits: VecP<u64, A::Index>,
    round_robin: VecP<u64, A::Index>,
    transport_rows: AppendOnlyVec<Vec<u32>>,
    transport_cols: AppendOnlyVec<Vec<u32>>,
    transport_cell_map: AppendOnlyVec<Vec<Option<A::AndChildStat>>>,
}

impl<A: AuIds, O: DenseId> AndStatsArena<A, O> {
    fn new() -> Self {
        Self {
            parent: AppendOnlyVec::new(),
            op: AppendOnlyVec::new(),
            commutative: AppendOnlyVec::new(),
            child_spans: AppendOnlyVec::new(),
            child_or_stats: AppendOnlyVec::new(),
            value: VecP::new(),
            child_counts: VecP::new(),
            child_visits: VecP::new(),
            round_robin: VecP::new(),
            transport_rows: AppendOnlyVec::new(),
            transport_cols: AppendOnlyVec::new(),
            transport_cell_map: AppendOnlyVec::new(),
        }
    }

    #[inline]
    fn index<I: DenseId<Index = A::Index>>(id: I) -> A::Index {
        A::Index::try_from_usize(id.to_usize()).expect("MCGS id exceeds configured index width")
    }

    fn len(&self) -> usize {
        self.parent.len()
    }

    fn push(&mut self, data: AndStatsData<A::OrStats, O>) -> A::AndStats {
        assert_eq!(data.child_or_stats.len(), data.child_counts.len());
        assert_eq!(data.child_or_stats.len(), data.child_visits.len());

        let node_len = self.len();
        assert_eq!(self.op.len(), node_len);
        assert_eq!(self.commutative.len(), node_len);
        assert_eq!(self.child_spans.len(), node_len);
        assert_eq!(self.value.len().as_usize(), node_len);
        assert_eq!(self.round_robin.len().as_usize(), node_len);
        assert_eq!(self.transport_rows.len(), node_len);
        assert_eq!(self.transport_cols.len(), node_len);
        assert_eq!(self.transport_cell_map.len(), node_len);

        let child_start = self.child_or_stats.len();
        assert_eq!(self.child_counts.len().as_usize(), child_start);
        assert_eq!(self.child_visits.len().as_usize(), child_start);
        let child_len = data.child_or_stats.len();
        let id = A::AndStats::from_usize(node_len);
        let child_span = checked_pool_span::<A::AndChildStat>(
            child_start,
            child_len,
            "AND child-statistics pool",
        );
        let typed_cell_map: Vec<Option<A::AndChildStat>> = data
            .transport_cell_map
            .iter()
            .map(|&position| {
                position.map(|position| {
                    assert!(
                        position < child_len,
                        "transport child position out of bounds"
                    );
                    let absolute = child_start
                        .checked_add(position)
                        .expect("transport child position overflows usize");
                    A::AndChildStat::from_usize(absolute)
                })
            })
            .collect();

        for child in data.child_or_stats {
            self.child_or_stats.push(child);
        }
        for count in data.child_counts {
            self.child_counts.push(count);
        }
        for visits in data.child_visits {
            self.child_visits.push(visits);
        }
        self.parent.push(data.parent);
        self.op.push(data.op);
        self.commutative.push(data.commutative);
        self.child_spans.push(child_span);
        self.value.push(data.value);
        self.round_robin.push(data.round_robin);
        self.transport_rows.push(data.transport_rows);
        self.transport_cols.push(data.transport_cols);
        self.transport_cell_map.push(typed_cell_map);
        id
    }

    #[inline]
    fn child_span(&self, id: A::AndStats) -> super::Span<A::AndChildStat> {
        *self.child_spans.get(id.to_usize())
    }

    #[inline]
    fn child_id(&self, id: A::AndStats, position: usize) -> A::AndChildStat {
        let span = self.child_span(id);
        assert!(position < span.len_usize(), "AND child index out of bounds");
        A::AndChildStat::from_usize(span.start_usize() + position)
    }

    #[inline]
    fn child_or(&self, child: A::AndChildStat) -> A::OrStats {
        *self.child_or_stats.get(child.to_usize())
    }

    #[cfg(test)]
    fn child_visits(&self, id: A::AndStats) -> &[u64] {
        let span = self.child_span(id);
        &self.child_visits.as_slice().expect("VecP is contiguous")
            [span.start_usize()..span.end_usize()]
    }

    fn get(&self, id: A::AndStats) -> AndStatsRef<'_, A::OrStats, O, A::AndChildStat> {
        let node = Self::index(id);
        let span = self.child_span(id);
        let range = span.start_usize()..span.end_usize();
        AndStatsRef {
            parent: *self.parent.get(id.to_usize()),
            op: *self.op.get(id.to_usize()),
            commutative: *self.commutative.get(id.to_usize()),
            value: self.value.get(node),
            child_or_stats: &self.child_or_stats.as_slice()[range.clone()],
            child_counts: &self.child_counts.as_slice().expect("VecP is contiguous")[range.clone()],
            child_visits: &self.child_visits.as_slice().expect("VecP is contiguous")[range],
            round_robin: self.round_robin.get(node),
            transport_rows: self.transport_rows.get(id.to_usize()),
            transport_cols: self.transport_cols.get(id.to_usize()),
            transport_cell_map: self.transport_cell_map.get(id.to_usize()),
        }
    }

    fn set_value(&mut self, id: A::AndStats, value: f64) {
        self.value.set(Self::index(id), value);
    }

    fn set_child_count(&mut self, child: A::AndChildStat, value: u32) {
        self.child_counts.set(Self::index(child), value);
    }

    fn bump_child_visit(&mut self, child: A::AndChildStat) {
        let child = Self::index(child);
        self.child_visits
            .set(child, self.child_visits.get(child) + 1);
    }

    fn bump_round_robin(&mut self, id: A::AndStats) {
        let node = Self::index(id);
        self.round_robin.set(node, self.round_robin.get(node) + 1);
    }

    fn mark(&mut self) -> AndStatsToken {
        AndStatsToken {
            parent: self.parent.mark(ShrinkPolicy::Never),
            op: self.op.mark(ShrinkPolicy::Never),
            commutative: self.commutative.mark(ShrinkPolicy::Never),
            child_spans: self.child_spans.mark(ShrinkPolicy::Never),
            child_or_stats: self.child_or_stats.mark(ShrinkPolicy::Never),
            value: self.value.mark(ShrinkPolicy::Never),
            child_counts: self.child_counts.mark(ShrinkPolicy::Never),
            child_visits: self.child_visits.mark(ShrinkPolicy::Never),
            round_robin: self.round_robin.mark(ShrinkPolicy::Never),
            transport_rows: self.transport_rows.mark(ShrinkPolicy::Never),
            transport_cols: self.transport_cols.mark(ShrinkPolicy::Never),
            transport_cell_map: self.transport_cell_map.mark(ShrinkPolicy::Never),
        }
    }

    fn is_valid_token(&self, token: &AndStatsToken) -> bool {
        self.parent.is_valid_token(&token.parent)
            && self.op.is_valid_token(&token.op)
            && self.commutative.is_valid_token(&token.commutative)
            && self.child_spans.is_valid_token(&token.child_spans)
            && self.child_or_stats.is_valid_token(&token.child_or_stats)
            && self.value.is_valid_token(&token.value)
            && self.child_counts.is_valid_token(&token.child_counts)
            && self.child_visits.is_valid_token(&token.child_visits)
            && self.round_robin.is_valid_token(&token.round_robin)
            && self.transport_rows.is_valid_token(&token.transport_rows)
            && self.transport_cols.is_valid_token(&token.transport_cols)
            && self
                .transport_cell_map
                .is_valid_token(&token.transport_cell_map)
    }

    fn restore(&mut self, token: AndStatsToken) {
        assert!(self.is_valid_token(&token), "AndStatsArena: invalid token");
        self.transport_cell_map.restore(token.transport_cell_map);
        self.transport_cols.restore(token.transport_cols);
        self.transport_rows.restore(token.transport_rows);
        self.round_robin.restore(token.round_robin);
        self.child_visits.restore(token.child_visits);
        self.child_counts.restore(token.child_counts);
        self.value.restore(token.value);
        self.child_or_stats.restore(token.child_or_stats);
        self.child_spans.restore(token.child_spans);
        self.commutative.restore(token.commutative);
        self.op.restore(token.op);
        self.parent.restore(token.parent);
    }
}

/// MCGS state composed entirely from standard semi-persistent containers.
pub(crate) struct McgsState<A: AuIds = AuIds31, O: DenseId = crate::id::OpId> {
    or_stats: OrStatsArena<A, O>,
    and_stats: AndStatsArena<A, O>,
    or_stats_map: Map<A::Or, A::OrStats>,
}

/// Token for restoring `McgsState`. It bundles only arena and map tokens.
#[derive(Clone, Copy, Debug)]
pub(crate) struct McgsToken {
    or_stats: OrStatsToken,
    and_stats: AndStatsToken,
    or_stats_map: MapToken,
}

impl<A: AuIds, O: DenseId> McgsState<A, O> {
    pub(crate) fn new() -> Self {
        Self {
            or_stats: OrStatsArena::new(),
            and_stats: AndStatsArena::new(),
            or_stats_map: Map::new(),
        }
    }

    pub(crate) fn mark(&mut self) -> McgsToken {
        McgsToken {
            or_stats: self.or_stats.mark(),
            and_stats: self.and_stats.mark(),
            or_stats_map: self.or_stats_map.mark(ShrinkPolicy::Never),
        }
    }

    pub(crate) fn is_valid_token(&self, token: &McgsToken) -> bool {
        self.or_stats.is_valid_token(&token.or_stats)
            && self.and_stats.is_valid_token(&token.and_stats)
            && self.or_stats_map.is_valid_token(&token.or_stats_map)
    }

    pub(crate) fn restore(&mut self, token: McgsToken) {
        assert!(
            self.is_valid_token(&token),
            "McgsState: token is invalid (foreign or abandoned)"
        );
        self.or_stats_map.restore(token.or_stats_map);
        self.and_stats.restore(token.and_stats);
        self.or_stats.restore(token.or_stats);
    }

    #[inline]
    fn or_stat(&self, id: A::OrStats) -> OrStatsRef<'_, A::AndStats> {
        self.or_stats.get(id)
    }

    #[inline]
    fn and_stat(&self, id: A::AndStats) -> AndStatsRef<'_, A::OrStats, O, A::AndChildStat> {
        self.and_stats.get(id)
    }

    #[inline]
    fn or_id(&self, id: A::OrStats) -> A::Or {
        self.or_stats.or_id(id)
    }

    fn push_or_stat(
        &mut self,
        or_id: A::Or,
        data: OrStatsData<A::AndStats>,
        descriptors: Vec<TransportActionDesc<O, A::Class>>,
    ) -> A::OrStats {
        let id = self.or_stats.push(or_id, data, descriptors);
        self.or_stats_map.insert(or_id, id);
        id
    }

    fn push_and_stat(&mut self, data: AndStatsData<A::OrStats, O>) -> A::AndStats {
        self.and_stats.push(data)
    }

    fn set_or_initial_value(&mut self, id: A::OrStats, value: f64) {
        self.or_stats.set_initial_value(id, value);
    }

    fn set_or_value(&mut self, id: A::OrStats, value: f64) {
        self.or_stats.set_value(id, value);
    }

    fn bump_or_edge_visit(&mut self, id: A::OrStats, action: usize) {
        self.or_stats.bump_edge_visit(id, action);
    }

    fn set_or_edge_and(&mut self, id: A::OrStats, action: usize, value: Option<A::AndStats>) {
        self.or_stats.set_edge_and(id, action, value);
    }

    fn set_and_value(&mut self, id: A::AndStats, value: f64) {
        self.and_stats.set_value(id, value);
    }

    fn set_and_child_count(&mut self, child: A::AndChildStat, value: u32) {
        self.and_stats.set_child_count(child, value);
    }

    fn bump_and_child_visit(&mut self, child: A::AndChildStat) {
        self.and_stats.bump_child_visit(child);
    }

    fn bump_and_round_robin(&mut self, id: A::AndStats) {
        self.and_stats.bump_round_robin(id);
    }
}

/// Run MCGS from a root class pair, returning the best anti-unifier found.
///
/// Errors with `AuError::NoFiniteRepresentative` if either root (or any class
/// reachable from one) has no admissible finite member (§4.1).
pub fn run_mcgs<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l_root: ClassOf<Cfg>,
    r_root: ClassOf<Cfg>,
    config: &McgsConfig,
) -> Result<
    (
        <Cfg::Au as AuIds>::Term,
        TermPool<Cfg::O, Cfg::V, Cfg::Au>,
        super::session::Completion,
    ),
    super::AuError,
>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut space: SearchSpace<Cfg::Au> = SearchSpace::new(config.cycle_mode);
    let mut pool = TermPool::new();
    // MCGS skips AC/ACI matrix materialization; those operators use transport
    // AND-nodes instead (zero matrix enumeration, same as exact).
    let mut action_cache: ActionCache<Cfg::O, Cfg::Au> =
        ActionCache::without_ac_actions(usize::MAX);
    let mut results: BestResults<Cfg::Au> = BestResults::new();
    let mut state: McgsState<Cfg::Au, Cfg::O> = McgsState::new();
    let (best, completion) = run_mcgs_in(
        snap,
        &mut space,
        &mut pool,
        &mut action_cache,
        &mut results,
        &mut state,
        l_root,
        r_root,
        config,
    )?;
    Ok((best, pool, completion))
}

/// Session-based MCGS: runs on caller-owned layers so a `SearchSession` can
/// mark/restore the entire search state (space, pool, results, cache, stats)
/// across invocations.
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_mcgs_in<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    action_cache: &mut ActionCache<Cfg::O, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    l_root: ClassOf<Cfg>,
    r_root: ClassOf<Cfg>,
    config: &McgsConfig,
) -> Result<(<Cfg::Au as AuIds>::Term, super::session::Completion), super::AuError>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    snap.validate_finite_from(l_root)?;
    snap.validate_finite_from(r_root)?;

    let empty_ctx = space.contexts.empty();
    let l_best = snap.best_size(l_root);
    let r_best = snap.best_size(r_root);
    let (root_or, _) =
        space.get_or_insert_or_node(l_root, r_root, empty_ctx, empty_ctx, l_best, r_best);

    // Eagerly publish the shared terminal generalize action as a projection-valid
    // incumbent. The mandatory structural rollout below may immediately improve it.
    let seed = evaluate_generalize_action(snap, pool, l_root, r_root);
    results.ensure_capacity(root_or);
    results.offer(root_or, seed, pool.quality(seed));

    let root_idx = ensure_or_stats(snap, space, action_cache, results, state, root_or);

    if !state.or_stat(root_idx).terminal {
        // First estimate U(root) from the initial rollout; its term is also a
        // valid result and is offered (§3.3.2).
        let rollout = initial_rollout(snap, space, pool, action_cache, root_or);
        results.offer(root_or, rollout, pool.quality(rollout));
        let sz = pool.size(rollout) as f64;
        state.set_or_initial_value(root_idx, sz);
        state.set_or_value(root_idx, sz);

        for _ in 0..config.playouts {
            playout(
                snap,
                space,
                pool,
                action_cache,
                results,
                state,
                root_idx,
                config,
            );
        }
    }

    let completion = if is_structurally_complete(state, root_idx) {
        // Close the completed DAG: path-only backpropagation may have left
        // some incoming parents without the final child improvements. One
        // children-first pass recomputes every value and recomposes every
        // AND-node, making the published root result the true optimum.
        close_completed_dag(snap, pool, results, state, root_idx);
        super::session::Completion::Exact
    } else {
        super::session::Completion::BudgetExhausted {
            playouts_used: config.playouts,
        }
    };
    let best = results.best_term(root_or).unwrap_or(seed);
    Ok((best, completion))
}

/// Children-first postorder of the OR-stats DAG reachable from `root_idx`
/// through expanded AND-nodes. Cycle-safe (back edges are not revisited).
fn or_postorder<A: AuIds, O: DenseId>(
    state: &McgsState<A, O>,
    root_idx: A::OrStats,
) -> Vec<A::OrStats> {
    let mut postorder: Vec<A::OrStats> = Vec::new();
    let mut mark: Vec<u8> = vec![0; state.or_stats.len()]; // 0 unseen, 1 active, 2 done
    let mut stack: Vec<(A::OrStats, usize)> = vec![(root_idx, 0)]; // (or id, child cursor)
    while let Some(&mut (or_idx, ref mut cursor)) = stack.last_mut() {
        if mark[or_idx.to_usize()] == 2 {
            stack.pop();
            continue;
        }
        mark[or_idx.to_usize()] = 1;
        let children: Vec<A::OrStats> = state
            .or_stat(or_idx)
            .edge_and
            .iter()
            .flatten()
            .flat_map(|&a| state.and_stat(a).child_or_stats.iter().copied())
            .collect();
        if *cursor < children.len() {
            let child = children[*cursor];
            *cursor += 1;
            if mark[child.to_usize()] == 0 {
                stack.push((child, 0));
            }
        } else {
            mark[or_idx.to_usize()] = 2;
            postorder.push(or_idx);
            stack.pop();
        }
    }
    postorder
}

/// Children-first closure over the completed DAG reachable from `root_idx`:
/// recompute every AND value, recompose and offer every AND result, then
/// recompute every OR value. Path-only backpropagation can leave incoming
/// parents of a shared child stale; this single deterministic pass propagates
/// the final child values and results through every parent. Cycle-free by
/// construction (structural completion rejects active cycles before this runs).
fn close_completed_dag<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    root_idx: <Cfg::Au as AuIds>::OrStats,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    for &or_idx in &or_postorder(state, root_idx) {
        let edges: Vec<<Cfg::Au as AuIds>::AndStats> = state
            .or_stat(or_idx)
            .edge_and
            .iter()
            .flatten()
            .copied()
            .collect();
        for and_idx in edges {
            recompute_and_value(state, and_idx);
            compose_and_offer(snap, pool, results, state, and_idx);
        }
        recompute_or_value(state, or_idx);
    }
}

/// Value-only closure (no composition): same postorder recomputation as
/// `close_completed_dag` restricted to Q values. Used by tests that construct
/// synthetic stats without a snapshot.
#[cfg(test)]
fn close_values<A: AuIds, O: DenseId>(state: &mut McgsState<A, O>, root_idx: A::OrStats) {
    for &or_idx in &or_postorder(state, root_idx) {
        let edges: Vec<A::AndStats> = state
            .or_stat(or_idx)
            .edge_and
            .iter()
            .flatten()
            .copied()
            .collect();
        for and_idx in edges {
            recompute_and_value(state, and_idx);
        }
        recompute_or_value(state, or_idx);
    }
}

/// Structural completion certificate: an OR node is complete when it is terminal
/// or every legal action has been expanded and each expanded AND-node is complete.
/// An AND-node is complete when every child OR-node is complete.
///
/// Iterative (explicit frame stack) with the tri-state visited protocol of the
/// recursive definition: 0 = unseen, 1 = active (on the current path; a re-entry
/// is a cycle and conservatively rejects), 2 = memoized complete. The first
/// `false` anywhere (unrealized edge, or active-cycle hit) short-circuits the
/// whole certificate, exactly like the recursive `all(..)` chains.
fn is_structurally_complete<A: AuIds, O: DenseId>(
    state: &McgsState<A, O>,
    or_idx: A::OrStats,
) -> bool {
    let mut visited: Vec<u8> = vec![0; state.or_stats.len()];
    // Frame: an OR node whose flattened child OR list (every expanded
    // AND-node's children, in edge then child order) is being verified.
    let mut stack: Vec<(A::OrStats, Vec<A::OrStats>, usize)> = Vec::new();
    let mut pending = Some(or_idx);
    loop {
        if let Some(current) = pending.take() {
            match visited[current.to_usize()] {
                2 => {}            // memoized: already verified complete
                1 => return false, // active: cycle, conservatively reject
                _ => {
                    visited[current.to_usize()] = 1; // mark active
                    let stats = state.or_stat(current);
                    if stats.terminal {
                        visited[current.to_usize()] = 2;
                    } else {
                        // Every legal action must have been expanded.
                        if stats.edge_and.iter().any(|e| e.is_none()) {
                            return false;
                        }
                        // Every expanded AND-node's children must be complete.
                        let children: Vec<A::OrStats> = stats
                            .edge_and
                            .iter()
                            .flatten()
                            .flat_map(|&a| state.and_stat(a).child_or_stats.iter().copied())
                            .collect();
                        stack.push((current, children, 0));
                    }
                }
            }
        }
        loop {
            let Some((_, children, cursor)) = stack.last_mut() else {
                return true;
            };
            if *cursor < children.len() {
                let child = children[*cursor];
                *cursor += 1;
                pending = Some(child);
                break;
            }
            let (done, _, _) = stack.pop().expect("completion stack cannot be empty");
            visited[done.to_usize()] = 2; // memoize
        }
    }
}

/// One feasible AC/ACI transport action at an OR node: a representation pair
/// with its cycle-blocked cell mask. Only pairs admitting a feasible flow
/// (zero-cost transport with blocked cells Forbidden) become actions; a pair
/// with legal cells can still be Hall-infeasible (a blocked row with positive
/// supply), and such pairs must not consume an action slot.
struct TransportActionDesc<O, C> {
    op: O,
    left: ac_repr::Monomial<C>,
    right: ac_repr::Monomial<C>,
    /// Flat row-major r*c mask: true = cell is not cycle-blocked.
    legal_cells: Vec<bool>,
}

/// Enumerate the feasible transport actions for `(l, r)` at `or_id`. Single
/// source of truth for action counting, expansion indexing, and rollout.
fn transport_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &SearchSpace<Cfg::Au>,
    or_id: <Cfg::Au as AuIds>::Or,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
) -> Vec<TransportActionDesc<Cfg::O, ClassOf<Cfg>>>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut out = Vec::new();
    for op in ac_repr::common_ac_ops(snap, l, r) {
        for (lm, rm) in ac_repr::representation_pairs(snap, l, r, op) {
            let n_cols = rm.len();
            let mut legal_cells = vec![false; lm.len() * n_cols];
            let mut cost = vec![vec![Cell::Forbidden; n_cols]; lm.len()];
            for (i, (lc, _)) in lm.iter().enumerate() {
                for (j, (rc, _)) in rm.iter().enumerate() {
                    if !space.is_cycle_blocked(or_id, *lc, *rc) {
                        legal_cells[i * n_cols + j] = true;
                        cost[i][j] = Cell::Cost(0, 0);
                    }
                }
            }
            let feasible = solve_transport(&TransportProblem {
                row_supply: lm.iter().map(|(_, k)| *k).collect(),
                col_demand: rm.iter().map(|(_, k)| *k).collect(),
                cost,
            })
            .is_some();
            if feasible {
                out.push(TransportActionDesc {
                    op,
                    left: lm,
                    right: rm,
                    legal_cells,
                });
            }
        }
    }
    out
}

/// Look up or create the statistics struct for an OR node. Fresh structs know
/// their action count (cycle-filtered), terminal flag, and normalization sizes;
/// values start at the node's stored best-result size (terminal) or infinity
/// (awaiting a rollout estimate).
fn ensure_or_stats<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    action_cache: &mut ActionCache<Cfg::O, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    or_id: <Cfg::Au as AuIds>::Or,
) -> <Cfg::Au as AuIds>::OrStats
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if let Some(log_idx) = state.or_stats_map.id_of(&or_id) {
        return *state.or_stats_map.get(log_idx);
    }

    let l = *space.or_arena.left.get(or_id.to_usize());
    let r = *space.or_arena.right.get(or_id.to_usize());
    let l_best = *space.or_arena.left_best_size.get(or_id.to_usize()) as f64;
    let r_best = *space.or_arena.right_best_size.get(or_id.to_usize()) as f64;

    let (num_actions, descs) = if l == r {
        (0, Vec::new())
    } else {
        generate_actions(snap, action_cache, l, r);
        let actions = action_cache.get(l, r).unwrap();
        let mut count = 0;
        for action in actions {
            let blocked = action
                .pairs
                .iter()
                .any(|p| space.is_cycle_blocked(or_id, p.left, p.right));
            if !blocked {
                count += 1;
            }
        }
        // One edge per feasible AC/ACI transport action (flow-verified).
        // Descriptors are computed once here and cached on the stats entry;
        // expansion reads the cache instead of re-solving feasibility.
        let descs = transport_actions(snap, space, or_id, l, r);
        count += descs.len();
        (count, descs)
    };

    let terminal = l == r || num_actions == 0 || results.is_exact(or_id);
    // Terminal nodes take their stored best result as their permanent value.
    let value = if terminal {
        results.best_size(or_id) as f64
    } else {
        f64::INFINITY
    };

    state.push_or_stat(
        or_id,
        OrStatsData {
            initial_value: value,
            value,
            min_size: l_best.min(r_best),
            max_size: l_best.max(r_best),
            terminal,
            edge_visits: vec![0; num_actions],
            edge_and: vec![None; num_actions],
        },
        descs,
    )
}

/// One playout (§3.3): descend by UCT at OR nodes and the configured AND
/// selector (§3.3.5), expand the first
/// unrealized action met, rollout fresh children, then backpropagate along the
/// traversed path (children before parents), recomputing values idempotently
/// and offering composed results.
#[allow(clippy::too_many_arguments)]
fn playout<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    action_cache: &mut ActionCache<Cfg::O, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    root_idx: <Cfg::Au as AuIds>::OrStats,
    config: &McgsConfig,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    // The traversed path: AND stats ids, root-side first.
    let mut path: Vec<<Cfg::Au as AuIds>::AndStats> = Vec::new();
    let mut current = root_idx;

    loop {
        if state.or_stat(current).terminal {
            break;
        }

        // First unrealized action, in ascending action order (UCT expansion §3.3.4).
        let unrealized = state
            .or_stat(current)
            .edge_and
            .iter()
            .position(|e| e.is_none());

        if let Some(action_idx) = unrealized {
            // Edge visit is counted before the realization check, so the new
            // edge is born with visit count 1 (§3.3.4).
            state.bump_or_edge_visit(current, action_idx);
            let and_idx = expand_action(
                snap,
                space,
                pool,
                action_cache,
                results,
                state,
                current,
                action_idx,
            );
            state.set_or_edge_and(current, action_idx, Some(and_idx));
            path.push(and_idx);

            // Rollout: first estimate for fresh children (§3.3.2).
            for pos in 0..state.and_stat(and_idx).child_or_stats.len() {
                let child_idx = state.and_stat(and_idx).child_or_stats[pos];
                if state.or_stat(child_idx).value.is_infinite() {
                    let child_or = state.or_id(child_idx);
                    let rollout = initial_rollout(snap, space, pool, action_cache, child_or);
                    results.ensure_capacity(child_or);
                    results.offer(child_or, rollout, pool.quality(rollout));
                    let sz = pool.size(rollout) as f64;
                    state.set_or_initial_value(child_idx, sz);
                    state.set_or_value(child_idx, sz);
                }
            }
            break;
        }

        // Fully expanded: score realized actions by UCT (§3.3.4), first max wins.
        let action_idx = select_uct(state, current, config);
        state.bump_or_edge_visit(current, action_idx);
        let and_idx = state.or_stat(current).edge_and[action_idx].unwrap();
        path.push(and_idx);

        // AND allocation: configured selector (§3.3.5), with its own edge
        // visit. The round-robin counter is part of the overlay state and is
        // maintained regardless of the selector in use.
        let pos = select_and_child(state, and_idx, config);
        let child = state.and_stats.child_id(and_idx, pos);
        state.bump_and_round_robin(and_idx);
        state.bump_and_child_visit(child);
        current = state.and_stats.child_or(child);
    }

    // Backpropagation (§3.3.3): deepest AND first, then rootward. Each AND
    // recomputes Q from its children, composes their best results into a
    // candidate, and offers it to its parent OR; the parent recomputes Q.
    for &and_idx in path.iter().rev() {
        recompute_and_value(state, and_idx);
        compose_and_offer(snap, pool, results, state, and_idx);
        let parent = state.and_stat(and_idx).parent;
        recompute_or_value(state, parent);
    }
}

/// UCT score (§3.3.4):
/// `score(a) = reward(Q(and_a)) + C * sqrt(sum_N) / (1 + N(n,a))`
/// evaluated in ascending action order; the first maximum wins.
///
/// All actions are normalized against the parent OR node's own (min_size, max_size)
/// (§2.5.1 property A); per-action bases can invert the size preference.
fn select_uct<A: AuIds, O: DenseId>(
    state: &McgsState<A, O>,
    or_idx: A::OrStats,
    config: &McgsConfig,
) -> usize {
    let stats = state.or_stat(or_idx);
    let total: u64 = stats.edge_visits.iter().sum();
    let sqrt_total = (total as f64).sqrt();

    let mut best_score = f64::NEG_INFINITY;
    let mut best_action = 0;

    for (a, edge) in stats.edge_and.iter().enumerate() {
        let and_idx = edge.expect("select_uct requires a fully expanded node");
        let and = state.and_stat(and_idx);
        let r = super::reward::reward(and.value, stats.min_size, stats.max_size, config.x_target);
        let exploration =
            config.exploration_constant * sqrt_total / (1.0 + stats.edge_visits[a] as f64);
        let score = r + exploration;
        if score > best_score {
            best_score = score;
            best_action = a;
        }
    }
    best_action
}

/// AND-node effort allocation (§3.3.5): pick the child position that receives
/// the next unit of refinement effort, per the configured selector:
///
/// ```text
/// round_robin:  i = counter mod arity;  counter += 1
/// uct_and:      argmax_i (1 − normalize(Q(child_i))) + C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))
/// lct_and:      argmin_i (1 − normalize(Q(child_i))) − C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))
/// ```
///
/// Each child's Q is normalized against that child OR node's own
/// `(min_size, max_size)` basis (§2.5.1 property A: per-node basis). Scores
/// are evaluated in ascending child order with strict improvement, so ties
/// resolve to the smallest (scored) child index.
///
/// **Terminal-skip gate (delivered refinement, see
/// doc/future/au-associative-operators.md §5).** The value-guided selectors
/// skip children whose OR node is terminal. A terminal child can never change
/// the completion certificate and its Q is exact and immutable, so visiting
/// it refines nothing. The bare formulas do NOT starve such children
/// naturally: on a deep spine the nonterminal child's reward converges to
/// `1 − λ/best_size`, a near-tie with the terminal sibling's reward of 1, and
/// the exploration term then forces near-equal allocation (the bonus-balance
/// steady state is N_terminal ≈ N_spine), reproducing round-robin's 2^-depth
/// flux decay — pinned by `lct_and_without_terminal_skip_splits_flux_on_near_ties`.
/// Skipping terminals is admissible under §2.5.1 F because fairness exists to
/// converge child estimates, and a terminal child's estimate is already exact.
/// When every child is terminal the choice is inert (descent stops at any
/// terminal child and backpropagation is path-based); the smallest index is
/// returned.
fn select_and_child<A: AuIds, O: DenseId>(
    state: &McgsState<A, O>,
    and_idx: A::AndStats,
    config: &McgsConfig,
) -> usize {
    match config.and_selector {
        AndSelector::RoundRobin => {
            let and = state.and_stat(and_idx);
            let arity = and.child_or_stats.len();
            debug_assert!(arity > 0, "AND selection requires at least one child");
            (and.round_robin as usize) % arity
        }
        AndSelector::UctAnd => select_and_child_value_guided(state, and_idx, config, 1.0, true),
        AndSelector::LctAnd => select_and_child_value_guided(state, and_idx, config, -1.0, true),
    }
}

/// Value-guided scoring core shared by `uct_and` (`sign = +1`, argmax) and
/// `lct_and` (`sign = −1`, argmin as argmax of the negated reward). The
/// exploration bonus is added in both cases:
/// `sign · reward(child) + C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))`.
/// `skip_terminal` is the terminal-skip gate documented on
/// [`select_and_child`]; production always passes `true`, tests exercise
/// `false` to pin why the gate is required.
fn select_and_child_value_guided<A: AuIds, O: DenseId>(
    state: &McgsState<A, O>,
    and_idx: A::AndStats,
    config: &McgsConfig,
    sign: f64,
    skip_terminal: bool,
) -> usize {
    let and = state.and_stat(and_idx);
    debug_assert!(
        !and.child_or_stats.is_empty(),
        "AND selection requires at least one child"
    );
    let total: u64 = and.child_visits.iter().sum();
    let sqrt_total = (total as f64).sqrt();

    let mut best_score = f64::NEG_INFINITY;
    let mut best_child = None;
    for (i, &child_idx) in and.child_or_stats.iter().enumerate() {
        let child = state.or_stat(child_idx);
        if skip_terminal && child.terminal {
            continue;
        }
        let r = super::reward::reward(child.value, child.min_size, child.max_size, config.x_target);
        let exploration =
            config.exploration_constant * sqrt_total / (1.0 + and.child_visits[i] as f64);
        let score = sign * r + exploration;
        if score > best_score {
            best_score = score;
            best_child = Some(i);
        }
    }
    // Every child terminal: the choice is inert (see the gate documentation).
    best_child.unwrap_or(0)
}

/// AND value equation (§3.3): for fixed-action AND-nodes,
/// `Q(n) = 1 + Σ_i count_i · Q(child_i)`. For transport-AND-nodes,
/// `Q(n) = 1 + min_X Σ_ij x_ij · Q(cell_ij)` where X is the transport argmin.
fn recompute_and_value<A: AuIds, O: DenseId>(state: &mut McgsState<A, O>, and_idx: A::AndStats) {
    let is_transport = !state.and_stat(and_idx).transport_rows.is_empty();
    if is_transport {
        recompute_transport_and_value(state, and_idx);
    } else {
        let and = state.and_stat(and_idx);
        let mut q = 1.0;
        for (i, &child) in and.child_or_stats.iter().enumerate() {
            q += and.child_counts[i] as f64 * state.or_stat(child).value;
        }
        state.set_and_value(and_idx, q);
    }
}

/// Transport-AND value recomputation: solve min-cost flow over current cell Qs,
/// update child_counts to the argmin flow, and set Q accordingly.
fn recompute_transport_and_value<A: AuIds, O: DenseId>(
    state: &mut McgsState<A, O>,
    and_idx: A::AndStats,
) {
    let rows = state.and_stat(and_idx).transport_rows.to_vec();
    let cols = state.and_stat(and_idx).transport_cols.to_vec();
    let n_rows = rows.len();
    let n_cols = cols.len();

    // Build the float cost matrix from current child Q values via the typed cell map.
    // Native f64 costs: no scalarization or rounding, the exact Q argmin over
    // the represented values is preserved. Non-finite Qs are Forbidden.
    let cell_map = state.and_stat(and_idx).transport_cell_map.to_vec();
    let mut cost: Vec<Vec<Option<f64>>> = vec![vec![None; n_cols]; n_rows];
    for flat in 0..(n_rows * n_cols) {
        if let Some(child) = cell_map[flat] {
            let q = state.or_stat(state.and_stats.child_or(child)).value;
            if q.is_finite() {
                cost[flat / n_cols][flat % n_cols] = Some(q);
            }
        }
    }

    let problem = TransportProblemF64 {
        row_supply: rows,
        col_demand: cols,
        cost,
    };

    match solve_transport_f64(&problem) {
        Some(solution) => {
            // Zero out child counts, then fill them from the selected flow.
            for position in 0..state.and_stat(and_idx).child_counts.len() {
                if state.and_stat(and_idx).child_counts[position] != 0 {
                    let child = state.and_stats.child_id(and_idx, position);
                    state.set_and_child_count(child, 0);
                }
            }
            let mut q = 1.0;
            for flat in 0..(n_rows * n_cols) {
                let i = flat / n_cols;
                let j = flat % n_cols;
                let x = solution.flow[i][j];
                if x > 0
                    && let Some(child) = cell_map[flat]
                {
                    state.set_and_child_count(child, x);
                    q += x as f64 * state.or_stat(state.and_stats.child_or(child)).value;
                }
            }
            state.set_and_value(and_idx, q);
        }
        None => {
            state.set_and_value(and_idx, f64::INFINITY);
        }
    }
}

/// OR value equation (§2.6, idempotent):
/// `Q(n) = (U(n) + Σ_a N(n,a) · Q(and_a)) / (1 + Σ_a N(n,a))`.
fn recompute_or_value<A: AuIds, O: DenseId>(state: &mut McgsState<A, O>, or_idx: A::OrStats) {
    let stats = &state.or_stat(or_idx);
    if stats.terminal {
        return;
    }
    let mut sum = stats.initial_value;
    let mut total: u64 = 0;
    for (a, edge) in stats.edge_and.iter().enumerate() {
        if let Some(and_idx) = *edge {
            let n = stats.edge_visits[a];
            sum += n as f64 * state.and_stat(and_idx).value;
            total += n;
        }
    }
    let v = sum / (1.0 + total as f64);
    state.set_or_value(or_idx, v);
}

/// Compose the AND node's children's stored best results into a candidate term
/// and offer it to the parent OR node (§3.3: "every update also offers the
/// children's stored best results"). For transport-AND-nodes, a separate
/// transport solve over the lexicographic best-result qualities determines the
/// composition flow (distinct from the value-flow Q estimates).
fn compose_and_offer<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    state: &McgsState<Cfg::Au, Cfg::O>,
    and_idx: <Cfg::Au as AuIds>::AndStats,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let and = state.and_stat(and_idx);
    let is_transport = !and.transport_rows.is_empty();

    let children: Vec<(<Cfg::Au as AuIds>::Term, u32)> = if is_transport {
        // Solve transport over lexicographic best-result qualities for composition.
        let n_rows = and.transport_rows.len();
        let n_cols = and.transport_cols.len();
        let cell_map = &and.transport_cell_map;
        let mut cost = vec![vec![Cell::Forbidden; n_cols]; n_rows];
        let mut terms: Vec<Option<<Cfg::Au as AuIds>::Term>> = vec![None; n_rows * n_cols];
        for flat in 0..(n_rows * n_cols) {
            if let Some(child) = cell_map[flat] {
                let child_or = state.or_id(state.and_stats.child_or(child));
                if let Some(t) = results.best_term(child_or) {
                    let (s, v) = pool.quality(t);
                    let i = flat / n_cols;
                    let j = flat % n_cols;
                    cost[i][j] = Cell::Cost(s, v);
                    terms[flat] = Some(t);
                }
            }
        }
        let problem = TransportProblem {
            row_supply: and.transport_rows.to_vec(),
            col_demand: and.transport_cols.to_vec(),
            cost,
        };
        let Some(solution) = solve_transport(&problem) else {
            return;
        };
        let mut out = Vec::new();
        for (idx, term) in terms.iter().enumerate() {
            let i = idx / n_cols;
            let j = idx % n_cols;
            let x = solution.flow[i][j];
            if x > 0 {
                if let Some(t) = term {
                    out.push((*t, x));
                } else {
                    return;
                }
            }
        }
        out
    } else {
        // Fixed-action composition: use stored child_counts.
        let mut out = Vec::with_capacity(and.child_or_stats.len());
        for (i, &child_idx) in and.child_or_stats.iter().enumerate() {
            let child_or = state.or_id(child_idx);
            match results.best_term(child_or) {
                Some(t) => out.push((t, and.child_counts[i])),
                None => return,
            }
        }
        out
    };

    let op = and.op;
    let candidate = pool.intern_action_result(TermOp::EGraph(op), &children, and.commutative);
    let parent_or = state.or_id(and.parent);
    let _ = snap;
    results.offer(parent_or, candidate, pool.quality(candidate));
}

/// Realize one edge: allocate the AND statistics struct and all child OR nodes.
/// `action_idx` indexes first over non-AC cached actions, then over AC/ACI
/// representation pairs (transport-AND-nodes).
#[allow(clippy::too_many_arguments)]
fn expand_action<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    action_cache: &mut ActionCache<Cfg::O, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    or_idx: <Cfg::Au as AuIds>::OrStats,
    action_idx: usize,
) -> <Cfg::Au as AuIds>::AndStats
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let or_id = state.or_id(or_idx);
    let l = *space.or_arena.left.get(or_id.to_usize());
    let r = *space.or_arena.right.get(or_id.to_usize());
    let ctx_l = *space.or_arena.left_ctx.get(or_id.to_usize());
    let ctx_r = *space.or_arena.right_ctx.get(or_id.to_usize());

    generate_actions(snap, action_cache, l, r);
    let actions = action_cache.get(l, r).unwrap().to_vec();

    // Count non-AC surviving actions.
    let non_ac_count = actions
        .iter()
        .filter(|a| {
            !a.pairs
                .iter()
                .any(|p| space.is_cycle_blocked(or_id, p.left, p.right))
        })
        .count();

    if action_idx < non_ac_count {
        // Non-AC action: fixed-weight AND-node.
        let action = actions
            .iter()
            .filter(|a| {
                !a.pairs
                    .iter()
                    .any(|p| space.is_cycle_blocked(or_id, p.left, p.right))
            })
            .nth(action_idx)
            .unwrap();

        let mut child_or_stats = Vec::with_capacity(action.pairs.len());
        let mut child_counts = Vec::with_capacity(action.pairs.len());
        for pair in &action.pairs {
            let child_ctx_l = space
                .derive_child_context(ctx_l, l, |c| snap.reachability().is_reachable(pair.left, c));
            let child_ctx_r = space.derive_child_context(ctx_r, r, |c| {
                snap.reachability().is_reachable(pair.right, c)
            });
            let (child_or, _) = space.get_or_insert_or_node(
                pair.left,
                pair.right,
                child_ctx_l,
                child_ctx_r,
                snap.best_size(pair.left),
                snap.best_size(pair.right),
            );
            let child_seed = evaluate_generalize_action(snap, pool, pair.left, pair.right);
            results.ensure_capacity(child_or);
            results.offer(child_or, child_seed, pool.quality(child_seed));
            let child_idx = ensure_or_stats(snap, space, action_cache, results, state, child_or);
            child_or_stats.push(child_idx);
            child_counts.push(pair.count);
        }
        let arity = child_or_stats.len();
        state.push_and_stat(AndStatsData {
            parent: or_idx,
            op: action.op,
            commutative: snap.op_is_commutative(action.op),
            value: f64::INFINITY,
            child_or_stats,
            child_counts,
            child_visits: vec![0; arity],
            round_robin: 0,
            transport_rows: Vec::new(),
            transport_cols: Vec::new(),
            transport_cell_map: Vec::new(),
        })
    } else {
        // AC/ACI transport-AND-node: one per feasible transport action.
        // Descriptors come from the per-OR cache built at stats creation.
        let transport_idx = action_idx - non_ac_count;
        let desc = &state.or_stats.transport_descs(or_idx)[transport_idx];
        let (op, lm, rm) = (desc.op, desc.left.clone(), desc.right.clone());
        let legal_cells = desc.legal_cells.clone();
        let (lm, rm) = (&lm, &rm);
        let n_rows = lm.len();
        let n_cols = rm.len();

        // Create children for legal cells; blocked cells map to None and are
        // Forbidden in the transport combiner.
        let mut cell_map: Vec<Option<usize>> = Vec::with_capacity(n_rows * n_cols);
        let mut filtered_children: Vec<<Cfg::Au as AuIds>::OrStats> = Vec::new();
        for (i, (lc, _)) in lm.iter().enumerate() {
            for (j, (rc, _)) in rm.iter().enumerate() {
                if !legal_cells[i * n_cols + j] {
                    cell_map.push(None);
                    continue;
                }
                let child_ctx_l = space
                    .derive_child_context(ctx_l, l, |c| snap.reachability().is_reachable(*lc, c));
                let child_ctx_r = space
                    .derive_child_context(ctx_r, r, |c| snap.reachability().is_reachable(*rc, c));
                let (child_or, _) = space.get_or_insert_or_node(
                    *lc,
                    *rc,
                    child_ctx_l,
                    child_ctx_r,
                    snap.best_size(*lc),
                    snap.best_size(*rc),
                );
                let child_seed = evaluate_generalize_action(snap, pool, *lc, *rc);
                results.ensure_capacity(child_or);
                results.offer(child_or, child_seed, pool.quality(child_seed));
                let child_idx =
                    ensure_or_stats(snap, space, action_cache, results, state, child_or);
                cell_map.push(Some(filtered_children.len()));
                filtered_children.push(child_idx);
            }
        }

        let arity = filtered_children.len();
        state.push_and_stat(AndStatsData {
            parent: or_idx,
            op,
            commutative: true,
            value: f64::INFINITY,
            child_or_stats: filtered_children,
            child_counts: vec![0; arity],
            child_visits: vec![0; arity],
            round_robin: 0,
            transport_rows: lm.iter().map(|(_, k)| *k).collect(),
            transport_cols: rm.iter().map(|(_, k)| *k).collect(),
            transport_cell_map: cell_map,
        })
    }
}

/// Deterministic, bounded initialization choice. Static estimates inspect every
/// surviving action, but recursive rollout follows only the selected action (and,
/// for transport, only the cells carrying its selected static flow).
enum InitialRolloutChoice {
    Generalize,
    Structural(usize),
    Transport {
        descriptor: usize,
        flow: Vec<Vec<u32>>,
    },
}

/// Exact quality of the terminal generalize action without interning its term.
fn static_generalize_quality<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
) -> (u32, u32)
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if l == r {
        (snap.best_size(l), 0)
    } else {
        let size = snap
            .best_size(l)
            .checked_add(snap.best_size(r))
            .expect("generalize estimate exceeds u32 term-size capacity");
        (size, size)
    }
}

#[inline]
fn wide_quality((size, variant_mass): (u32, u32)) -> (u128, u128) {
    (u128::from(size), u128::from(variant_mass))
}

/// Action-aware initialization (§A.4): compare the eager generalize action with
/// a deterministic concrete upper-bound estimate for every cycle-surviving
/// structural and transport action. Then recursively follow only the selected
/// action. This is complete at the operator-choice level without becoming an
/// exhaustive exact recursion over every action subtree.
///
/// Iterative frame machine (explicit stack): each frame holds the selection
/// outcome for its node — a structural action's pair list or a transport
/// action's positive-flow cells, in the recursive evaluation order
/// (left-to-right pairs / row-major cells) — plus a child cursor and the
/// collected child terms. Child OR nodes are created (contexts derived,
/// `get_or_insert_or_node`) at descent time, exactly when the recursion would,
/// so search-space side effects and term-pool interning order are identical.
/// Generalize selections and `l == r` terminals complete without a frame.
fn initial_rollout<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    action_cache: &mut ActionCache<Cfg::O, Cfg::Au>,
    or_id: <Cfg::Au as AuIds>::Or,
) -> <Cfg::Au as AuIds>::Term
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    struct Frame<Cfg: EGraphConfig> {
        l: ClassOf<Cfg>,
        r: ClassOf<Cfg>,
        ctx_l: <Cfg::Au as AuIds>::Context,
        ctx_r: <Cfg::Au as AuIds>::Context,
        op: Cfg::O,
        /// Transport frames compose commutatively and fall back to the
        /// generalize action when no cell carries flow.
        transport: bool,
        /// Child pairs in evaluation order: `(left, right, count)`.
        items: Vec<(ClassOf<Cfg>, ClassOf<Cfg>, u32)>,
        cursor: usize,
        child_terms: Vec<(<Cfg::Au as AuIds>::Term, u32)>,
    }

    let mut stack: Vec<Frame<Cfg>> = Vec::new();
    let mut pending = or_id;
    loop {
        // ── Enter: evaluate the selection for `pending` ──
        let current = pending;
        let l = *space.or_arena.left.get(current.to_usize());
        let r = *space.or_arena.right.get(current.to_usize());

        let mut done: Option<<Cfg::Au as AuIds>::Term> = None;
        if l == r {
            done = Some(build_best_term(snap, pool, l));
        } else {
            generate_actions(snap, action_cache, l, r);
            let actions = action_cache.get(l, r).unwrap().to_vec();
            let transport = transport_actions(snap, space, current, l, r);
            let ctx_l = *space.or_arena.left_ctx.get(current.to_usize());
            let ctx_r = *space.or_arena.right_ctx.get(current.to_usize());

            // Eager generalization is an explicit action and wins ties, so the
            // initializer can never return a result worse than this valid incumbent.
            let mut choice = InitialRolloutChoice::Generalize;
            let mut best_estimate = wide_quality(static_generalize_quality(snap, l, r));

            for (action_idx, action) in actions.iter().enumerate() {
                if action
                    .pairs
                    .iter()
                    .any(|p| space.is_cycle_blocked(current, p.left, p.right))
                {
                    continue;
                }

                let mut estimate = (1u128, 0u128);
                for pair in &action.pairs {
                    let child =
                        wide_quality(static_generalize_quality(snap, pair.left, pair.right));
                    estimate.0 = estimate
                        .0
                        .checked_add(child.0 * u128::from(pair.count))
                        .expect("structural rollout size estimate overflow");
                    estimate.1 = estimate
                        .1
                        .checked_add(child.1 * u128::from(pair.count))
                        .expect("structural rollout variant estimate overflow");
                }
                if estimate < best_estimate {
                    best_estimate = estimate;
                    choice = InitialRolloutChoice::Structural(action_idx);
                }
            }

            for (descriptor, desc) in transport.iter().enumerate() {
                let n_cols = desc.right.len();
                let mut cost = vec![vec![Cell::Forbidden; n_cols]; desc.left.len()];
                for (i, (lc, _)) in desc.left.iter().enumerate() {
                    for (j, (rc, _)) in desc.right.iter().enumerate() {
                        if desc.legal_cells[i * n_cols + j] {
                            let (size, variant_mass) = static_generalize_quality(snap, *lc, *rc);
                            cost[i][j] = Cell::Cost(size, variant_mass);
                        }
                    }
                }
                let Some(solution) = solve_transport(&TransportProblem {
                    row_supply: desc.left.iter().map(|(_, count)| *count).collect(),
                    col_demand: desc.right.iter().map(|(_, count)| *count).collect(),
                    cost,
                }) else {
                    continue;
                };
                let estimate = (
                    solution
                        .total
                        .0
                        .checked_add(1)
                        .expect("transport rollout size estimate overflow"),
                    solution.total.1,
                );
                if estimate < best_estimate {
                    best_estimate = estimate;
                    choice = InitialRolloutChoice::Transport {
                        descriptor,
                        flow: solution.flow,
                    };
                }
            }

            match choice {
                InitialRolloutChoice::Generalize => {
                    done = Some(evaluate_generalize_action(snap, pool, l, r));
                }
                InitialRolloutChoice::Structural(action_idx) => {
                    let action = &actions[action_idx];
                    let items: Vec<(ClassOf<Cfg>, ClassOf<Cfg>, u32)> = action
                        .pairs
                        .iter()
                        .map(|pair| (pair.left, pair.right, pair.count))
                        .collect();
                    let capacity = items.len();
                    stack.push(Frame {
                        l,
                        r,
                        ctx_l,
                        ctx_r,
                        op: action.op,
                        transport: false,
                        items,
                        cursor: 0,
                        child_terms: Vec::with_capacity(capacity),
                    });
                }
                InitialRolloutChoice::Transport { descriptor, flow } => {
                    let desc = transport
                        .into_iter()
                        .nth(descriptor)
                        .expect("selected transport descriptor disappeared");
                    let n_cols = desc.right.len();
                    // Positive-flow cells in row-major order: the recursive
                    // evaluation order of the selected static flow.
                    let mut items: Vec<(ClassOf<Cfg>, ClassOf<Cfg>, u32)> = Vec::new();
                    for (i, (lc, _)) in desc.left.iter().enumerate() {
                        for (j, (rc, _)) in desc.right.iter().enumerate() {
                            let count = flow[i][j];
                            if count == 0 {
                                continue;
                            }
                            debug_assert!(desc.legal_cells[i * n_cols + j]);
                            items.push((*lc, *rc, count));
                        }
                    }
                    stack.push(Frame {
                        l,
                        r,
                        ctx_l,
                        ctx_r,
                        op: desc.op,
                        transport: true,
                        items,
                        cursor: 0,
                        child_terms: Vec::new(),
                    });
                }
            }
        }

        // ── Advance: deliver completed terms upward, descend or compose ──
        loop {
            if let Some(term) = done.take() {
                let Some(parent) = stack.last_mut() else {
                    return term;
                };
                let (_, _, count) = parent.items[parent.cursor];
                parent.child_terms.push((term, count));
                parent.cursor += 1;
            }
            let top = stack
                .last_mut()
                .expect("initial rollout stack cannot be empty");
            if top.cursor < top.items.len() {
                // Create the child OR node now, exactly when the recursion would.
                let (cl, cr, _) = top.items[top.cursor];
                let (pl, pr, pctx_l, pctx_r) = (top.l, top.r, top.ctx_l, top.ctx_r);
                let child_ctx_l = space
                    .derive_child_context(pctx_l, pl, |c| snap.reachability().is_reachable(cl, c));
                let child_ctx_r = space
                    .derive_child_context(pctx_r, pr, |c| snap.reachability().is_reachable(cr, c));
                let (child_or, _) = space.get_or_insert_or_node(
                    cl,
                    cr,
                    child_ctx_l,
                    child_ctx_r,
                    snap.best_size(cl),
                    snap.best_size(cr),
                );
                pending = child_or;
                break; // descend
            }
            let frame = stack.pop().expect("initial rollout stack cannot be empty");
            done = Some(if frame.transport {
                if frame.child_terms.is_empty() {
                    evaluate_generalize_action(snap, pool, frame.l, frame.r)
                } else {
                    pool.intern_action_result(TermOp::EGraph(frame.op), &frame.child_terms, true)
                }
            } else {
                pool.intern_action_result(
                    TermOp::EGraph(frame.op),
                    &frame.child_terms,
                    snap.op_is_commutative(frame.op),
                )
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::au::exact::eager_with_memo;
    use crate::au::space::OrId;
    use crate::au::{AndChildStatId, AndStatsId, OrEdgeStatId, OrStatsId};
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

    crate::containers::define_id7! { struct TinyId / TinyStoredId, "tiny"; }
    crate::containers::define_id7! { struct TinyOrStats / TinyStoredOrStats, "tos"; }
    crate::containers::define_id7! { struct TinyAndStats / TinyStoredAndStats, "tas"; }
    crate::containers::define_id7! { struct TinyOrEdge / TinyStoredOrEdge, "toe"; }
    crate::containers::define_id7! { struct TinyAndChild / TinyStoredAndChild, "tac"; }

    struct TinyAu;
    impl AuIds for TinyAu {
        type Index = u8;
        type Class = TinyId;
        type Scc = TinyId;
        type Or = TinyId;
        type Action = TinyId;
        type Context = TinyId;
        type Term = TinyId;
        type OrStats = TinyOrStats;
        type AndStats = TinyAndStats;
        type SnapshotMember = TinyId;
        type ContextElem = TinyId;
        type TermChild = TinyId;
        type ReachBlock = TinyId;
        type OrEdgeStat = TinyOrEdge;
        type AndChildStat = TinyAndChild;
    }

    fn tiny_or_data(edges: usize) -> OrStatsData<TinyAndStats> {
        OrStatsData {
            initial_value: 1.0,
            value: 1.0,
            min_size: 1.0,
            max_size: 1.0,
            terminal: edges == 0,
            edge_visits: vec![0; edges],
            edge_and: vec![None; edges],
        }
    }

    fn tiny_and_data(
        children: usize,
        transport_cell_map: Vec<Option<usize>>,
    ) -> AndStatsData<TinyOrStats, TinyId> {
        AndStatsData {
            parent: TinyOrStats::from_usize(0),
            op: TinyId::from_usize(0),
            commutative: false,
            value: 1.0,
            child_or_stats: vec![TinyOrStats::from_usize(0); children],
            child_counts: vec![1; children],
            child_visits: vec![0; children],
            round_robin: 0,
            transport_rows: Vec::new(),
            transport_cols: Vec::new(),
            transport_cell_map,
        }
    }

    fn tiny_or_lengths(arena: &OrStatsArena<TinyAu, TinyId>) -> [usize; 10] {
        [
            arena.or_ids.len(),
            arena.min_size.len(),
            arena.max_size.len(),
            arena.terminal.len(),
            arena.edge_spans.len(),
            arena.initial_value.len().as_usize(),
            arena.value.len().as_usize(),
            arena.edge_visits.len().as_usize(),
            arena.edge_and.len().as_usize(),
            arena.transport_descs.len(),
        ]
    }

    fn tiny_and_lengths(arena: &AndStatsArena<TinyAu, TinyId>) -> [usize; 12] {
        [
            arena.parent.len(),
            arena.op.len(),
            arena.commutative.len(),
            arena.child_spans.len(),
            arena.child_or_stats.len(),
            arena.value.len().as_usize(),
            arena.child_counts.len().as_usize(),
            arena.child_visits.len().as_usize(),
            arena.round_robin.len().as_usize(),
            arena.transport_rows.len(),
            arena.transport_cols.len(),
            arena.transport_cell_map.len(),
        ]
    }

    #[test]
    fn or_stats_capacity_panics_leave_all_pools_aligned() {
        let mut edge_full: OrStatsArena<TinyAu, TinyId> = OrStatsArena::new();
        edge_full.push(TinyId::from_usize(0), tiny_or_data(128), Vec::new());
        let before = tiny_or_lengths(&edge_full);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            edge_full.push(TinyId::from_usize(1), tiny_or_data(1), Vec::new());
        }));
        assert!(outcome.is_err());
        assert_eq!(tiny_or_lengths(&edge_full), before);

        let mut node_full: OrStatsArena<TinyAu, TinyId> = OrStatsArena::new();
        for i in 0..128 {
            node_full.push(TinyId::from_usize(i), tiny_or_data(0), Vec::new());
        }
        let before = tiny_or_lengths(&node_full);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            node_full.push(TinyId::from_usize(0), tiny_or_data(0), Vec::new());
        }));
        assert!(outcome.is_err());
        assert_eq!(tiny_or_lengths(&node_full), before);
    }

    #[test]
    fn and_stats_preflight_panics_leave_all_pools_aligned() {
        let mut child_full: AndStatsArena<TinyAu, TinyId> = AndStatsArena::new();
        child_full.push(tiny_and_data(128, vec![Some(127)]));
        let before = tiny_and_lengths(&child_full);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            child_full.push(tiny_and_data(1, vec![Some(0)]));
        }));
        assert!(outcome.is_err());
        assert_eq!(tiny_and_lengths(&child_full), before);

        let mut invalid_map: AndStatsArena<TinyAu, TinyId> = AndStatsArena::new();
        let before = tiny_and_lengths(&invalid_map);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            invalid_map.push(tiny_and_data(1, vec![Some(1)]));
        }));
        assert!(outcome.is_err());
        assert_eq!(tiny_and_lengths(&invalid_map), before);
    }

    fn os(i: usize) -> OrStatsId {
        OrStatsId::from_usize(i)
    }
    fn asid(i: usize) -> AndStatsId {
        AndStatsId::from_usize(i)
    }
    fn cs(i: usize) -> AndChildStatId {
        AndChildStatId::from_usize(i)
    }
    fn push_or(state: &mut McgsState, data: OrStatsData<AndStatsId>) -> OrStatsId {
        let or_id = OrId::from_usize(state.or_stats.len());
        state.push_or_stat(or_id, data, Vec::new())
    }
    fn push_and(
        state: &mut McgsState,
        data: AndStatsData<OrStatsId, crate::id::OpId>,
    ) -> AndStatsId {
        state.push_and_stat(data)
    }

    /// On a small instance, MCGS run to exhaustion equals the exact solver's size.
    #[test]
    fn mcgs_matches_exact_small() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let f_op = eg.register_op2("f", int, int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let fab = eg.add(f_op, &[a, b]);
        let fac = eg.add(f_op, &[a, c]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(fab).unwrap();
        let rc = snap.class_of(fac).unwrap();

        let (exact_term, exact_pool) =
            eager_with_memo(&snap, lc, rc, CycleMode::AncestorOnly).unwrap();
        let exact_size = exact_pool.size(exact_term);

        let config = McgsConfig {
            playouts: 500,
            cycle_mode: CycleMode::AncestorOnly,
            ..Default::default()
        };
        let (mcgs_term, mcgs_pool, completion) = run_mcgs(&snap, lc, rc, &config).unwrap();
        assert_eq!(mcgs_pool.size(mcgs_term), exact_size);
        // This tiny graph should be fully certified within 500 playouts.
        assert_eq!(completion, super::super::session::Completion::Exact);
    }

    /// The §3.4.4 greedy counterexample: the greedy diagonal costs 10, the
    /// crossed matching costs 9. The initial rollout finds 10; only result
    /// composition through backpropagation can reach 9. This is the regression
    /// gate for "MCGS cannot improve beyond its initial rollout".
    #[test]
    fn mcgs_beats_initial_rollout() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let v1_op = eg.register_op0("v1", int);
        let v2_op = eg.register_op0("v2", int);
        let f_op = eg.register_op2("f", int, int, int);
        let g_op = eg.register_op2("g", int, int, int);
        let op_op = eg.register_mset("op", int, int);

        let v1 = eg.add(v1_op, &[]);
        let v2 = eg.add(v2_op, &[]);
        let x1 = eg.add(f_op, &[v1, v1]);
        let x2 = eg.add(g_op, &[v1, v1]);
        eg.merge(x1, x2); // X = {f(v1,v1), g(v1,v1)}
        let y = eg.add(f_op, &[v1, v2]); // Y = {f(v1,v2)}
        let z = eg.add(g_op, &[v1, v2]); // Z = {g(v1,v2)}
        let left = eg.add(op_op, &[x1, y]);
        let right = eg.add(op_op, &[x1, z]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(left).unwrap();
        let rc = snap.class_of(right).unwrap();

        let (exact_term, exact_pool) =
            eager_with_memo(&snap, lc, rc, CycleMode::AncestorOnly).unwrap();
        let exact_size = exact_pool.size(exact_term);
        assert_eq!(exact_size, 9, "exact optimum is the crossed matching");

        let config = McgsConfig {
            playouts: 1000,
            cycle_mode: CycleMode::AncestorOnly,
            ..Default::default()
        };
        let (mcgs_term, mcgs_pool, _) = run_mcgs(&snap, lc, rc, &config).unwrap();
        assert_eq!(
            mcgs_pool.size(mcgs_term),
            exact_size,
            "MCGS must improve past its initial rollout (size 10) to the optimum (9)"
        );
    }

    /// MCGS produces a valid result even on trivial (identical) classes.
    #[test]
    fn mcgs_identical_classes() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let a = eg.add(a_op, &[]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let ac = snap.class_of(a).unwrap();

        let config = McgsConfig {
            playouts: 10,
            ..Default::default()
        };
        let (term, pool, _) = run_mcgs(&snap, ac, ac, &config).unwrap();
        assert_eq!(pool.size(term), 1);
    }

    /// MCGS terminates on cyclic e-graphs.
    #[test]
    fn mcgs_cyclic_terminates() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let f_op = eg.register_op1("f", int, int);

        let a = eg.add(a_op, &[]);
        let fa = eg.add(f_op, &[a]);
        let b = eg.add(b_op, &[]);
        eg.merge(a, fa);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let ac = snap.class_of(a).unwrap();
        let bc = snap.class_of(b).unwrap();

        let config = McgsConfig {
            playouts: 100,
            ..Default::default()
        };
        let (term, pool, _) = run_mcgs(&snap, ac, bc, &config).unwrap();
        assert!(pool.size(term) < 100);
    }

    /// Transport value recomputation must minimize the actual floating-point
    /// child Q estimates. Truncating every Q to u32 makes all four costs tie in
    /// this instance, selects the diagonal, and reports 1 + 1.9 + 1.9 = 4.8;
    /// the true crossed optimum is 1 + 1.1 + 1.1 = 3.2.
    #[test]
    fn transport_and_value_uses_fractional_q_ordering() {
        fn child_stats(value: f64) -> OrStatsData<crate::au::AndStatsId> {
            OrStatsData {
                initial_value: value,
                value,
                min_size: 1.0,
                max_size: 2.0,
                terminal: true,
                edge_visits: Vec::new(),
                edge_and: Vec::new(),
            }
        }

        let mut state: McgsState = McgsState::new();
        // Row-major Q matrix: diagonal 1.9 + 1.9, crossed 1.1 + 1.1.
        for value in [1.9, 1.1, 1.1, 1.9] {
            push_or(&mut state, child_stats(value));
        }
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                op: crate::id::OpId::from_usize(0),
                commutative: true,
                value: f64::INFINITY,
                child_or_stats: vec![os(0), os(1), os(2), os(3)],
                child_counts: vec![0; 4],
                child_visits: vec![0; 4],
                round_robin: 0,
                transport_rows: vec![1, 1],
                transport_cols: vec![1, 1],
                transport_cell_map: vec![Some(0), Some(1), Some(2), Some(3)],
            },
        );

        recompute_transport_and_value(&mut state, asid(0));
        let and = state.and_stat(asid(0));
        assert!(
            (and.value - 3.2).abs() < 1e-12,
            "transport must select the crossed fractional-Q optimum; got {}",
            and.value
        );
        assert_eq!(and.child_counts, &[0, 1, 1, 0]);
        let child_span: crate::au::Span<AndChildStatId> = state.and_stats.child_span(asid(0));
        assert_eq!(child_span, crate::au::Span::new(0, 4));
        assert_eq!(
            and.transport_cell_map,
            &[Some(cs(0)), Some(cs(1)), Some(cs(2)), Some(cs(3))]
        );
    }

    #[test]
    fn structural_completion_rejects_unresolved_cycle() {
        let mut state: McgsState = McgsState::new();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 3.0,
                value: 3.0,
                min_size: 1.0,
                max_size: 1.0,
                terminal: false,
                edge_visits: vec![1],
                edge_and: vec![Some(asid(0))],
            },
        );
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: 3.0,
                child_or_stats: vec![os(0)],
                child_counts: vec![1],
                child_visits: vec![1],
                round_robin: 1,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );

        assert!(
            !is_structurally_complete(&state, os(0)),
            "an unresolved cycle is not a finite structural optimality certificate"
        );
    }

    #[test]
    fn mcgs_restore_clears_dangling_edges() {
        let mut state: McgsState = McgsState::new();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 3.0,
                value: 3.0,
                min_size: 1.0,
                max_size: 2.0,
                terminal: false,
                edge_visits: vec![0],
                edge_and: vec![None],
            },
        );
        let token = state.mark();

        // Simulate expansion: create an AND-node and link it.
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: 3.0,
                child_or_stats: Vec::new(),
                child_counts: Vec::new(),
                child_visits: Vec::new(),
                round_robin: 0,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );
        state.set_or_edge_and(os(0), 0, Some(asid(0)));
        state.bump_or_edge_visit(os(0), 0);

        state.restore(token);
        assert_eq!(state.and_stats.len(), 0);
        let edges: crate::au::Span<OrEdgeStatId> = state.or_stats.edge_span(os(0));
        assert_eq!(edges, crate::au::Span::new(0, 1));
        assert_eq!(state.or_stat(os(0)).edge_and, &[None]);
        assert_eq!(state.or_stat(os(0)).edge_visits, &[0]);
    }

    /// Shared DAG: f(a,a) vs f(b,b) shares the child subproblem AU(a,b).
    /// With tri-state visited, the completion check should still certify Exact
    /// (the second visit finds the memoized result, not a cycle).
    #[test]
    fn shared_dag_completion_is_exact() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let sort = eg.intern_sort("S");
        let a_op = eg.register_op0("a", sort);
        let b_op = eg.register_op0("b", sort);
        let f_op = eg.register_op2("f", sort, sort, sort);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let faa = eg.add(f_op, &[a, a]);
        let fbb = eg.add(f_op, &[b, b]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(faa).unwrap();
        let rc = snap.class_of(fbb).unwrap();

        let config = McgsConfig {
            playouts: 200,
            ..Default::default()
        };
        let (_, _, completion) = run_mcgs(&snap, lc, rc, &config).unwrap();
        assert_eq!(
            completion,
            super::super::session::Completion::Exact,
            "shared DAG should certify Exact (200 playouts on a 3-node graph)"
        );
    }

    #[test]
    fn transport_and_value_preserves_sub_mill_ordering() {
        fn child_stats(value: f64) -> OrStatsData<crate::au::AndStatsId> {
            OrStatsData {
                initial_value: value,
                value,
                min_size: 1.0,
                max_size: 2.0,
                terminal: true,
                edge_visits: Vec::new(),
                edge_and: Vec::new(),
            }
        }

        let mut state: McgsState = McgsState::new();
        for value in [1.0004, 1.0001, 1.0001, 1.0004] {
            push_or(&mut state, child_stats(value));
        }
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                op: crate::id::OpId::from_usize(0),
                commutative: true,
                value: f64::INFINITY,
                child_or_stats: vec![os(0), os(1), os(2), os(3)],
                child_counts: vec![0; 4],
                child_visits: vec![0; 4],
                round_robin: 0,
                transport_rows: vec![1, 1],
                transport_cols: vec![1, 1],
                transport_cell_map: vec![Some(0), Some(1), Some(2), Some(3)],
            },
        );

        recompute_transport_and_value(&mut state, asid(0));
        let and = state.and_stat(asid(0));
        assert!(
            (and.value - 3.0002).abs() < 1e-12,
            "transport must preserve the crossed sub-mill optimum; got {}",
            and.value
        );
        assert_eq!(and.child_counts, &[0, 1, 1, 0]);
    }

    #[test]
    fn mcgs_restore_undoes_all_surviving_statistics() {
        let mut state: McgsState = McgsState::new();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 3.0,
                value: 3.0,
                min_size: 1.0,
                max_size: 2.0,
                terminal: false,
                edge_visits: vec![1],
                edge_and: vec![Some(asid(0))],
            },
        );
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: 3.0,
                child_or_stats: vec![os(0)],
                child_counts: vec![1],
                child_visits: vec![1],
                round_robin: 1,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );
        let token = state.mark();

        state.set_or_initial_value(os(0), 2.0);
        state.set_or_value(os(0), 2.0);
        state.bump_or_edge_visit(os(0), 0);
        state.set_or_edge_and(os(0), 0, None);
        state.set_and_value(asid(0), 2.0);
        state.set_and_child_count(cs(0), 7);
        state.bump_and_child_visit(cs(0));
        state.bump_and_round_robin(asid(0));

        state.restore(token);
        let or = state.or_stat(os(0));
        assert_eq!(state.or_id(os(0)), OrId::from_usize(0));
        assert_eq!(or.initial_value, 3.0);
        assert_eq!(or.value, 3.0);
        assert_eq!(or.min_size, 1.0);
        assert_eq!(or.max_size, 2.0);
        assert!(!or.terminal);
        assert_eq!(or.edge_visits, &[1]);
        assert_eq!(or.edge_and, &[Some(asid(0))]);
        let and = state.and_stat(asid(0));
        assert_eq!(and.parent, os(0));
        assert_eq!(and.op, crate::id::OpId::from_usize(0));
        assert!(!and.commutative);
        assert_eq!(and.value, 3.0);
        assert_eq!(and.child_or_stats, &[os(0)]);
        assert_eq!(and.child_counts, &[1]);
        assert_eq!(state.and_stats.child_visits(asid(0)), &[1]);
        assert_eq!(and.round_robin, 1);
        assert!(and.transport_rows.is_empty());
        assert!(and.transport_cols.is_empty());
        assert!(and.transport_cell_map.is_empty());
    }

    #[test]
    fn completion_closes_values_through_every_shared_parent() {
        fn or_stats(
            value: f64,
            terminal: bool,
            edge: Option<usize>,
        ) -> OrStatsData<crate::au::AndStatsId> {
            OrStatsData {
                initial_value: value,
                value,
                min_size: 1.0,
                max_size: 20.0,
                terminal,
                edge_visits: edge.map_or_else(Vec::new, |_| vec![1]),
                edge_and: edge.map_or_else(Vec::new, |idx| vec![Some(asid(idx))]),
            }
        }
        fn and_stats(
            parent: usize,
            value: f64,
            children: Vec<usize>,
        ) -> AndStatsData<crate::au::OrStatsId, crate::id::OpId> {
            let arity = children.len();
            AndStatsData {
                parent: os(parent),
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value,
                child_or_stats: children.into_iter().map(os).collect(),
                child_counts: vec![1; arity],
                child_visits: vec![1; arity],
                round_robin: 1,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            }
        }

        // root -> {left, right}; left -> shared <- right; shared -> leaf.
        // A path through `left` updates shared and root, but path-only
        // backpropagation leaves the incoming `right` parent stale.
        let mut state: McgsState = McgsState::new();
        for data in [
            or_stats(20.0, false, Some(0)),
            or_stats(10.0, false, Some(1)),
            or_stats(10.0, false, Some(2)),
            or_stats(10.0, false, Some(3)),
            or_stats(1.0, true, None),
        ] {
            push_or(&mut state, data);
        }
        for data in [
            and_stats(0, 21.0, vec![1, 2]),
            and_stats(1, 11.0, vec![3]),
            and_stats(2, 11.0, vec![3]),
            and_stats(3, 2.0, vec![4]),
        ] {
            push_and(&mut state, data);
        }

        // Simulate backpropagation only along root -> left -> shared -> leaf.
        recompute_and_value(&mut state, asid(3));
        recompute_or_value(&mut state, os(3));
        recompute_and_value(&mut state, asid(1));
        recompute_or_value(&mut state, os(1));
        recompute_and_value(&mut state, asid(0));
        recompute_or_value(&mut state, os(0));
        assert!(is_structurally_complete(&state, os(0)));

        // The children-first closure pass (run before certifying Exact)
        // propagates the final child values through EVERY incoming parent.
        close_values(&mut state, os(0));
        let closed_root = state.or_stat(os(0)).value;

        // Reference: manually push through the other incoming parent too;
        // no further improvement should be possible after the closure.
        recompute_and_value(&mut state, asid(2));
        recompute_or_value(&mut state, os(2));
        recompute_and_value(&mut state, asid(0));
        recompute_or_value(&mut state, os(0));
        assert_eq!(
            closed_root,
            state.or_stat(os(0)).value,
            "Exact certification must close values/results through every incoming parent"
        );
    }

    #[test]
    fn mcgs_visit_counters_cover_the_supported_playout_budget() {
        let stats: OrStatsData<AndStatsId> = OrStatsData {
            initial_value: 1.0,
            value: 1.0,
            min_size: 1.0,
            max_size: 1.0,
            terminal: false,
            edge_visits: vec![0],
            edge_and: vec![None],
        };
        assert_eq!(
            core::mem::size_of_val(&stats.edge_visits[0]),
            core::mem::size_of::<u64>(),
            "visit counters must represent every supported u64 playout budget"
        );
    }

    #[test]
    fn mcgs_rejects_foreign_token_before_mutation() {
        let mut source: McgsState = McgsState::new();
        let foreign = source.mark();

        let mut target: McgsState = McgsState::new();
        push_or(
            &mut target,
            OrStatsData {
                initial_value: 4.0,
                value: 4.0,
                min_size: 1.0,
                max_size: 2.0,
                terminal: true,
                edge_visits: Vec::new(),
                edge_and: Vec::new(),
            },
        );
        assert!(!target.is_valid_token(&foreign));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            target.restore(foreign);
        }));
        assert!(outcome.is_err());
        assert_eq!(target.or_stats.len(), 1);
        assert_eq!(target.or_stat(os(0)).value, 4.0);
    }

    #[test]
    fn mcgs_invalidates_abandoned_future_token() {
        let mut state: McgsState = McgsState::new();
        let outer = state.mark();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 1.0,
                value: 1.0,
                min_size: 1.0,
                max_size: 1.0,
                terminal: true,
                edge_visits: Vec::new(),
                edge_and: Vec::new(),
            },
        );
        let abandoned = state.mark();
        state.set_or_value(os(0), 2.0);
        state.restore(outer);
        assert!(!state.is_valid_token(&abandoned));
    }

    /// Synthetic 2-child AND fixture for AND-selector tests: both children
    /// are nonterminal. Child 0 is strong (Q at its basis, reward near 1);
    /// child 1 is weak (large Q against a small basis, reward near 0, the
    /// high-uncertainty child). The AND node at index 0 has both as children.
    fn two_child_and_fixture() -> McgsState {
        let mut state: McgsState = McgsState::new();
        // Child 0: nonterminal, strong estimate (reward near 1).
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 2.1,
                value: 2.1,
                min_size: 2.0,
                max_size: 2.0,
                terminal: false,
                edge_visits: vec![0],
                edge_and: vec![None],
            },
        );
        // Child 1: nonterminal, weak estimate (reward near 0).
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 50.0,
                value: 50.0,
                min_size: 1.0,
                max_size: 2.0,
                terminal: false,
                edge_visits: vec![0],
                edge_and: vec![None],
            },
        );
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: f64::INFINITY,
                child_or_stats: vec![os(0), os(1)],
                child_counts: vec![1, 1],
                child_visits: vec![0, 0],
                round_robin: 0,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );
        state
    }

    /// Drive `select_and_child` for `n` rounds, maintaining both counters the
    /// way `playout` does, and return the per-child visit totals.
    fn drive_and_selector(state: &mut McgsState, selector: AndSelector, n: usize) -> Vec<u64> {
        let config = McgsConfig {
            and_selector: selector,
            ..Default::default()
        };
        for _ in 0..n {
            let pos = select_and_child(state, asid(0), &config);
            let child = state.and_stats.child_id(asid(0), pos);
            state.bump_and_round_robin(asid(0));
            state.bump_and_child_visit(child);
        }
        state.and_stats.child_visits(asid(0)).to_vec()
    }

    /// LctAnd routes visits toward the less-visited / higher-uncertainty
    /// child: the weak nonterminal (reward near 0) receives the dominant
    /// share of flux, while its strong sibling (reward near 1) keeps only its
    /// O(√N) exploration visits (§2.5.1 E/F: the diverging exploration term
    /// still revisits it — with C = √2 that is ≈ C·√N visits, ~28 of 400).
    #[test]
    fn lct_and_routes_visits_to_the_uncertain_child() {
        let mut state = two_child_and_fixture();
        let visits = drive_and_selector(&mut state, AndSelector::LctAnd, 400);
        assert!(
            visits[1] >= 350,
            "LctAnd must route the dominant share of effort to the weak child; got {visits:?}"
        );
        assert!(
            (1..=50).contains(&visits[0]),
            "the strong child must keep only its O(sqrt N) exploration visits; got {visits:?}"
        );
    }

    /// UctAnd refines the most promising child: the strong child (reward
    /// near 1) wins over the weak sibling, with the exploration term still
    /// paying O(√N) visits to the weak child.
    #[test]
    fn uct_and_routes_visits_to_the_promising_child() {
        let mut state = two_child_and_fixture();
        let visits = drive_and_selector(&mut state, AndSelector::UctAnd, 400);
        assert!(
            visits[0] >= 350,
            "UctAnd must route the dominant share of effort to the strong child; got {visits:?}"
        );
        assert!(
            (1..=50).contains(&visits[1]),
            "the neglected child must keep only its O(sqrt N) exploration visits; got {visits:?}"
        );
    }

    /// Necessity proof for the terminal-skip gate: on a near-tie — a terminal
    /// child (reward exactly 1) beside a nonterminal whose converged reward is
    /// close to 1, the deep-spine steady state — the bare lct_and formula
    /// splits flux roughly evenly (bonus-balance equalizes visits), which is
    /// exactly the round-robin 2^-depth decay the value-guided selector must
    /// fix. With the gate, the nonterminal child receives every visit.
    #[test]
    fn lct_and_without_terminal_skip_splits_flux_on_near_ties() {
        fn near_tie_fixture() -> McgsState {
            let mut state: McgsState = McgsState::new();
            // Child 0: terminal (l = r), reward exactly 1.
            push_or(
                &mut state,
                OrStatsData {
                    initial_value: 1.0,
                    value: 1.0,
                    min_size: 1.0,
                    max_size: 1.0,
                    terminal: true,
                    edge_visits: Vec::new(),
                    edge_and: Vec::new(),
                },
            );
            // Child 1: nonterminal spine child whose Q has converged to just
            // past its basis: reward = 1 - ncr is close to (but below) 1.
            push_or(
                &mut state,
                OrStatsData {
                    initial_value: 40.2,
                    value: 40.2,
                    min_size: 40.0,
                    max_size: 40.0,
                    terminal: false,
                    edge_visits: vec![0],
                    edge_and: vec![None],
                },
            );
            push_and(
                &mut state,
                AndStatsData {
                    parent: os(0),
                    op: crate::id::OpId::from_usize(0),
                    commutative: false,
                    value: f64::INFINITY,
                    child_or_stats: vec![os(0), os(1)],
                    child_counts: vec![1, 1],
                    child_visits: vec![0, 0],
                    round_robin: 0,
                    transport_rows: Vec::new(),
                    transport_cols: Vec::new(),
                    transport_cell_map: Vec::new(),
                },
            );
            state
        }

        let config = McgsConfig::default();
        assert_eq!(config.and_selector, AndSelector::LctAnd);

        // Ungated formula: near-equal split (the defect).
        let mut state = near_tie_fixture();
        for _ in 0..400 {
            let pos = select_and_child_value_guided(&state, asid(0), &config, -1.0, false);
            let child = state.and_stats.child_id(asid(0), pos);
            state.bump_and_round_robin(asid(0));
            state.bump_and_child_visit(child);
        }
        let ungated = state.and_stats.child_visits(asid(0)).to_vec();
        assert!(
            ungated[0] >= 150 && ungated[1] >= 150,
            "without the gate, near-ties must show the flux split that motivates it; \
             got {ungated:?} (if this fails, the gate may no longer be necessary — \
             re-evaluate it before weakening this pin)"
        );

        // Production selector (gated): the terminal child is skipped entirely.
        let mut state = near_tie_fixture();
        let visits = drive_and_selector(&mut state, AndSelector::LctAnd, 400);
        assert_eq!(
            visits,
            vec![0, 400],
            "with the gate, the nonterminal child receives every visit"
        );
    }

    /// When every child of an AND node is terminal the value-guided selectors
    /// return the smallest index (the choice is inert: descent stops at any
    /// terminal child).
    #[test]
    fn value_guided_selector_is_inert_when_all_children_are_terminal() {
        let mut state: McgsState = McgsState::new();
        for value in [1.0, 2.0] {
            push_or(
                &mut state,
                OrStatsData {
                    initial_value: value,
                    value,
                    min_size: 1.0,
                    max_size: 1.0,
                    terminal: true,
                    edge_visits: Vec::new(),
                    edge_and: Vec::new(),
                },
            );
        }
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: f64::INFINITY,
                child_or_stats: vec![os(0), os(1)],
                child_counts: vec![1, 1],
                child_visits: vec![0, 0],
                round_robin: 0,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );
        for selector in [AndSelector::LctAnd, AndSelector::UctAnd] {
            let config = McgsConfig {
                and_selector: selector,
                ..Default::default()
            };
            assert_eq!(select_and_child(&state, asid(0), &config), 0);
        }
    }

    /// RoundRobin rotates strictly, splitting visits equally regardless of
    /// values, and advances the shared round-robin counter.
    #[test]
    fn round_robin_rotates_regardless_of_values() {
        let mut state = two_child_and_fixture();
        let config = McgsConfig {
            and_selector: AndSelector::RoundRobin,
            ..Default::default()
        };
        // Strict alternation 0, 1, 0, 1, ...
        for k in 0..10 {
            let pos = select_and_child(&state, asid(0), &config);
            assert_eq!(pos, k % 2, "round-robin must rotate in order");
            let child = state.and_stats.child_id(asid(0), pos);
            state.bump_and_round_robin(asid(0));
            state.bump_and_child_visit(child);
        }
        assert_eq!(state.and_stats.child_visits(asid(0)), &[5, 5]);
        assert_eq!(state.and_stat(asid(0)).round_robin, 10);
    }

    /// The round-robin counter is overlay state and advances under every
    /// selector (playout bumps it unconditionally), so switching selectors
    /// mid-session cannot desynchronize pinned overlay expectations.
    #[test]
    fn round_robin_counter_advances_under_value_guided_selectors() {
        for selector in [AndSelector::LctAnd, AndSelector::UctAnd] {
            let mut state = two_child_and_fixture();
            drive_and_selector(&mut state, selector, 7);
            assert_eq!(
                state.and_stat(asid(0)).round_robin,
                7,
                "{selector:?}: the round-robin counter must be maintained regardless of selector"
            );
        }
    }

    /// AND-selector ties resolve to the smallest child index: two identical
    /// children give identical scores, and the first strict maximum wins.
    #[test]
    fn and_selector_ties_resolve_to_smallest_index() {
        let mut state: McgsState = McgsState::new();
        for _ in 0..2 {
            push_or(
                &mut state,
                OrStatsData {
                    initial_value: 5.0,
                    value: 5.0,
                    min_size: 1.0,
                    max_size: 2.0,
                    terminal: false,
                    edge_visits: vec![0],
                    edge_and: vec![None],
                },
            );
        }
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: f64::INFINITY,
                child_or_stats: vec![os(0), os(1)],
                child_counts: vec![1, 1],
                child_visits: vec![0, 0],
                round_robin: 0,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );
        for selector in [AndSelector::LctAnd, AndSelector::UctAnd] {
            let config = McgsConfig {
                and_selector: selector,
                ..Default::default()
            };
            assert_eq!(
                select_and_child(&state, asid(0), &config),
                0,
                "{selector:?}: ties must resolve to the smallest child index"
            );
        }
    }

    /// End-to-end oracle equality under every AND selector: on a small
    /// instance each selector certifies Exact and matches the exact solver.
    #[test]
    fn mcgs_matches_exact_under_every_and_selector() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let f_op = eg.register_op2("f", int, int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let fab = eg.add(f_op, &[a, b]);
        let fac = eg.add(f_op, &[a, c]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(fab).unwrap();
        let rc = snap.class_of(fac).unwrap();

        let (exact_term, exact_pool) =
            eager_with_memo(&snap, lc, rc, CycleMode::AncestorOnly).unwrap();
        let exact_size = exact_pool.size(exact_term);

        for selector in [
            AndSelector::RoundRobin,
            AndSelector::UctAnd,
            AndSelector::LctAnd,
        ] {
            let config = McgsConfig {
                playouts: 500,
                cycle_mode: CycleMode::AncestorOnly,
                and_selector: selector,
                ..Default::default()
            };
            let (mcgs_term, mcgs_pool, completion) = run_mcgs(&snap, lc, rc, &config).unwrap();
            assert_eq!(
                mcgs_pool.size(mcgs_term),
                exact_size,
                "{selector:?}: MCGS must match the exact optimum"
            );
            assert_eq!(
                completion,
                super::super::session::Completion::Exact,
                "{selector:?}: this tiny graph must certify within 500 playouts"
            );
        }
    }

    #[test]
    fn mcgs_unmarked_mutations_do_not_accumulate_history() {
        let mut state: McgsState = McgsState::new();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 1.0,
                value: 1.0,
                min_size: 1.0,
                max_size: 1.0,
                terminal: false,
                edge_visits: Vec::new(),
                edge_and: Vec::new(),
            },
        );

        for value in 2..=1_001 {
            state.set_or_value(os(0), value as f64);
        }
        assert_eq!(
            state.or_stats.value.diff_log_len(),
            0,
            "without a live mark, VecP must not accumulate restore history"
        );
    }
}
