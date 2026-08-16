// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! E-matching execution engine: DFS stack machine over a `QueryPlan`.
//!
//! Walks the plan's steps, materializing index lookups into leapfrog joins,
//! extracting children from matched nodes, and yielding binding environments.

use crate::ast::{CmpOp, LitValVarId, MsetVarId, MultVarId, SeqVarId, SetVarId, VarId};
use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::IndexLike;
use crate::egraph::EGraph;
use crate::index::{IndexMode, IndexStore, SortedVecCursor, VariantIndex};
use crate::leapfrog::{CursorVec, Difference, LeapfrogJoin, SortedCursor};
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;
use crate::resolve::{PatVar, RMult};
use crate::schedule::{IndexLookup, QueryPlan, Step};
use std::sync::atomic::{AtomicUsize, Ordering};

// ---------------------------------------------------------------------------
// Match-work instrumentation
// ---------------------------------------------------------------------------
//
// A thread-local counter of "matching steps": one increment per `run_step`
// entry, i.e. per partial-match extension the DFS explores. This is the
// faithful measure of e-matching work — it reflects how many candidate
// bindings the join machinery walks, which is exactly what semi-naive (and
// driver-narrowing lookups like `ByContains`) aim to reduce.
//
// The hot path does not touch the thread-local at all. `run_step` increments a
// plain `u64` on the `MatchPool` it already carries by `&mut`, and
// `run_query_into` folds that into the thread-local once per query, if counting
// is enabled. A thread-local read is an out-of-line call to `_tlv_get_addr` on
// Apple targets and the compiler hoists it out of nothing, so the earlier
// "one bool load per step" claim understated it: doing the read per step cost
// 1.2% of the run on `comparison/math-microbenchmark.rules.egg`.
//
// Counting stays gated at runtime by a thread-local flag, off by default, so a
// normal (release) run can be profiled by flipping the flag — e.g. the
// `--count-match-steps` CLI flag — with no test-mode rebuild.
//
// Use `set_match_step_counting(true)` to enable, `reset_match_steps()` before a
// measured region, and `match_steps()` after to read the delta.

use std::cell::Cell;

thread_local! {
    static MATCH_STEPS: Cell<u64> = const { Cell::new(0) };
    static COUNTING: Cell<bool> = const { Cell::new(false) };
}

/// Enable or disable match-step counting at runtime. Off by default. Turn it on
/// to profile a run (the `--count-match-steps` CLI flag, or a measuring test)
/// without rebuilding in test mode.
pub fn set_match_step_counting(on: bool) {
    COUNTING.with(|c| c.set(on));
}

/// Whether match-step counting is currently enabled on this thread.
pub fn match_step_counting_enabled() -> bool {
    COUNTING.with(|c| c.get())
}

/// Reset the match-step counter to zero.
pub fn reset_match_steps() {
    MATCH_STEPS.with(|c| c.set(0));
}

/// Read the match-step counter (number of `run_step` entries counted while
/// counting was enabled, since the last reset).
pub fn match_steps() -> u64 {
    MATCH_STEPS.with(|c| c.get())
}

/// Fold a query's step tally into the thread-local counter, if counting is on.
#[inline]
fn add_match_steps(n: u64) {
    if COUNTING.with(|c| c.get()) {
        MATCH_STEPS.with(|c| c.set(c.get() + n));
    }
}

// ---------------------------------------------------------------------------
// Rest-pool spans
// ---------------------------------------------------------------------------

/// A `(start, len)` span into one of the flattened rest pools, in the config's index
/// word.
///
/// `Cfg::Index`, not `u32` and not `usize`. Not `u32`, because a 63-bit config's pools
/// address far past four billion entries and a fixed word would cap them there — the same
/// hard-coded ceiling this pass exists to remove. Not `usize`, because these spans are
/// *stored*: `Match` keeps one per seq/set/mset variable and `MatchSet` keeps one per
/// (match, variable), so at a 31-bit config the pair is 8 bytes rather than 16, and the
/// stride-packed span vectors — the largest arrays in a `MatchSet` after the pools
/// themselves — halve.
type PoolSpan<Cfg> = (<Cfg as EGraphConfig>::Index, <Cfg as EGraphConfig>::Index);

/// The empty span, for an unbound rest variable.
#[inline]
fn empty_span<Cfg: EGraphConfig>() -> PoolSpan<Cfg> {
    let zero = <Cfg::Index as IndexLike>::min();
    (zero, zero)
}

/// `(start, len)` for the region `start..end` of a pool, converted into the config's
/// index word, or a panic naming the pool if the region is not addressable there.
///
/// Checked on the **end** position, which is the quantity that bounds the pair: `start`
/// and `end - start` are both at most `end`, so one check covers all three, and the span
/// can then be read back as `s + l` in the index word without a second check at every
/// read. Checking the two fields separately instead would wave through exactly the case
/// that matters — a start and a length that each fit while their sum does not.
///
/// This is a hard failure rather than a saturating clamp because a truncated span is
/// unrecoverable and silent: it aliases one variable's rest data onto another's, and
/// e-matching would then report confident, wrong matches. The message names the pool and
/// the ceiling so the remedy (a wider `EGraphConfig::Index`) is actionable.
#[inline]
fn pool_span<Cfg: EGraphConfig>(start: usize, end: usize, pool: &'static str) -> PoolSpan<Cfg> {
    debug_assert!(
        start <= end,
        "{pool}: span end {end} precedes start {start}"
    );
    if <Cfg::Index as IndexLike>::try_from_usize(end).is_none() {
        panic!(
            "{pool} grew to {end} entries, past the {} addressable by EGraphConfig::Index; \
             configure a wider index word",
            <Cfg::Index as IndexLike>::max().as_usize(),
        );
    }
    // Both fit, given `end` does: `start <= end` and `end - start <= end`.
    let ix = |n: usize| {
        <Cfg::Index as IndexLike>::try_from_usize(n).expect("bounded by the checked end position")
    };
    (ix(start), ix(end - start))
}

/// The `start..start + len` range of a stored span, back in `usize` for slicing.
///
/// Widening, so it cannot truncate, and the sum cannot overflow `usize`: both fields came
/// from positions in a live `Vec`, whose length is a `usize`.
#[inline]
fn span_range<Cfg: EGraphConfig>(span: PoolSpan<Cfg>) -> core::ops::Range<usize> {
    let start = span.0.as_usize();
    start..start + span.1.as_usize()
}

// ---------------------------------------------------------------------------
// Binding environment
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub struct Match<Cfg: EGraphConfig> {
    /// E-node bindings indexed by VarId.
    pub nodes: Vec<Option<Cfg::G>>,
    /// Multiplicity bindings indexed by MultVarId.
    pub mults: Vec<Cfg::M>,
    /// Literal value bindings indexed by LitValVarId.
    pub lit_vals: Vec<Cfg::V>,
    /// Sequence rest pool — all seq slices packed contiguously.
    pub seq_pool: Vec<Cfg::G>,
    /// Span (start, len) into seq_pool, indexed by SeqVarId.
    pub seq_spans: Vec<PoolSpan<Cfg>>,
    /// Set rest pool — all set slices packed contiguously.
    pub set_pool: Vec<Cfg::G>,
    /// Span (start, len) into set_pool, indexed by SetVarId.
    pub set_spans: Vec<PoolSpan<Cfg>>,
    /// Multiset rest pool — packed AC children (id + mult).
    pub mset_pool: Vec<Cfg::C>,
    /// Span (start, len) into mset_pool, indexed by MsetVarId.
    pub mset_spans: Vec<PoolSpan<Cfg>>,
}

impl<Cfg: EGraphConfig> Clone for Match<Cfg> {
    fn clone(&self) -> Self {
        Self {
            nodes: self.nodes.clone(),
            mults: self.mults.clone(),
            lit_vals: self.lit_vals.clone(),
            seq_pool: self.seq_pool.clone(),
            seq_spans: self.seq_spans.clone(),
            set_pool: self.set_pool.clone(),
            set_spans: self.set_spans.clone(),
            mset_pool: self.mset_pool.clone(),
            mset_spans: self.mset_spans.clone(),
        }
    }

    /// Overwrite in place, keeping every existing allocation.
    ///
    /// Spelled out rather than left to the default `*self = source.clone()`,
    /// which drops nine buffers and allocates nine more. `Vec::clone_from`
    /// reuses the destination's capacity when it suffices, so a recycled match
    /// costs nine `memcpy`s and no allocator traffic. This is what makes
    /// [`MatchPool`] worth having; see `doc/perf-results/E2-match-recycling.md`.
    fn clone_from(&mut self, source: &Self) {
        self.nodes.clone_from(&source.nodes);
        self.mults.clone_from(&source.mults);
        self.lit_vals.clone_from(&source.lit_vals);
        self.seq_pool.clone_from(&source.seq_pool);
        self.seq_spans.clone_from(&source.seq_spans);
        self.set_pool.clone_from(&source.set_pool);
        self.set_spans.clone_from(&source.set_spans);
        self.mset_pool.clone_from(&source.mset_pool);
        self.mset_spans.clone_from(&source.mset_spans);
    }
}

impl<Cfg: EGraphConfig> Match<Cfg> {
    pub fn new(shape: &crate::resolve::MatchShape) -> Self {
        Self {
            nodes: vec![None; shape.num_vars()],
            mults: vec![Cfg::M::ZERO; shape.num_mult_vars()],
            lit_vals: vec![Cfg::V::default(); shape.num_lit_val_vars()],
            seq_pool: Vec::new(),
            seq_spans: vec![empty_span::<Cfg>(); shape.num_seq_vars()],
            set_pool: Vec::new(),
            set_spans: vec![empty_span::<Cfg>(); shape.num_set_vars()],
            mset_pool: Vec::new(),
            mset_spans: vec![empty_span::<Cfg>(); shape.num_mset_vars()],
        }
    }
    // Node bindings
    pub fn get(&self, v: VarId) -> Cfg::G {
        self.nodes[v.idx()].unwrap()
    }
    pub fn set(&mut self, v: VarId, val: Cfg::G) {
        self.nodes[v.idx()] = Some(val);
    }
    pub fn clear(&mut self, v: VarId) {
        self.nodes[v.idx()] = None;
    }
    /// Read the raw binding (bound value or `None`). For save/restore of a slot that may
    /// already be bound (the bound-node re-join in `leapfrog_join`).
    pub fn get_opt(&self, v: VarId) -> Option<Cfg::G> {
        self.nodes[v.idx()]
    }
    /// Restore a raw binding saved by `get_opt`.
    pub fn set_opt(&mut self, v: VarId, val: Option<Cfg::G>) {
        self.nodes[v.idx()] = val;
    }
    /// Resolve a PatVar: local from env, global from GlobalCtx.
    pub fn resolve_pv<S: Copy>(
        &self,
        pv: PatVar,
        globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    ) -> Cfg::G {
        match pv {
            PatVar::Local(vid) => self.get(vid),
            PatVar::Global(gid) => globals.binding(gid),
        }
    }
    // Mult bindings
    pub fn get_mult(&self, v: MultVarId) -> Cfg::M {
        self.mults[v.idx()]
    }
    pub fn set_mult(&mut self, v: MultVarId, val: Cfg::M) {
        self.mults[v.idx()] = val;
    }
    // Lit val bindings
    pub fn get_lit_val(&self, v: LitValVarId) -> Cfg::V {
        self.lit_vals[v.idx()]
    }
    pub fn set_lit_val(&mut self, v: LitValVarId, val: Cfg::V) {
        self.lit_vals[v.idx()] = val;
    }
    // Seq rest
    pub fn seq_slice(&self, v: SeqVarId) -> &[Cfg::G] {
        &self.seq_pool[span_range::<Cfg>(self.seq_spans[v.idx()])]
    }
    pub fn push_seq(&mut self, v: SeqVarId, data: &[Cfg::G]) {
        let start = self.seq_pool.len();
        self.seq_pool.extend_from_slice(data);
        self.seq_spans[v.idx()] = pool_span::<Cfg>(start, self.seq_pool.len(), "Match::seq_pool");
    }
    pub fn pop_seq(&mut self, v: SeqVarId) {
        let (s, _) = self.seq_spans[v.idx()];
        self.seq_pool.truncate(s.as_usize());
        self.seq_spans[v.idx()] = empty_span::<Cfg>();
    }
    // Set rest
    pub fn set_slice(&self, v: SetVarId) -> &[Cfg::G] {
        &self.set_pool[span_range::<Cfg>(self.set_spans[v.idx()])]
    }
    pub fn push_set(&mut self, v: SetVarId, data: &[Cfg::G]) {
        let start = self.set_pool.len();
        self.set_pool.extend_from_slice(data);
        self.set_spans[v.idx()] = pool_span::<Cfg>(start, self.set_pool.len(), "Match::set_pool");
    }
    pub fn pop_set(&mut self, v: SetVarId) {
        let (s, _) = self.set_spans[v.idx()];
        self.set_pool.truncate(s.as_usize());
        self.set_spans[v.idx()] = empty_span::<Cfg>();
    }
    // Mset rest
    pub fn mset_slice(&self, v: MsetVarId) -> &[Cfg::C] {
        &self.mset_pool[span_range::<Cfg>(self.mset_spans[v.idx()])]
    }
    pub fn push_mset(&mut self, v: MsetVarId, data: &[Cfg::C]) {
        let start = self.mset_pool.len();
        self.mset_pool.extend_from_slice(data);
        self.mset_spans[v.idx()] =
            pool_span::<Cfg>(start, self.mset_pool.len(), "Match::mset_pool");
    }
    pub fn pop_mset(&mut self, v: MsetVarId) {
        let (s, _) = self.mset_spans[v.idx()];
        self.mset_pool.truncate(s.as_usize());
        self.mset_spans[v.idx()] = empty_span::<Cfg>();
    }

    /// Bind `v` to the still-available residual entries, writing them
    /// straight onto the pool tail (E15). `push_mset` with a caller-built
    /// slice re-bought a temporary per binding at every leaf of the AC
    /// assignment search - 221k bindings per allocprobe run, three growth
    /// allocations each; the pool was the destination all along.
    pub fn push_mset_residual(&mut self, v: MsetVarId, residual: &[(Cfg::G, Cfg::M)]) {
        let start = self.mset_pool.len();
        let zero = Cfg::M::ZERO;
        self.mset_pool.extend(
            residual
                .iter()
                .filter(|&&(_, m)| m > zero)
                .map(|&(g, m)| Cfg::mset_child_with_mult(g, m)),
        );
        self.mset_spans[v.idx()] =
            pool_span::<Cfg>(start, self.mset_pool.len(), "Match::mset_pool");
    }

    /// The ACI twin: bind `v` to the residual ids not consumed by the
    /// element assignment (same write-through mechanism).
    pub fn push_set_residual(
        &mut self,
        v: SetVarId,
        residual: &[Cfg::G],
        used: &crate::containers::bitset::BitSet,
    ) {
        let start = self.set_pool.len();
        self.set_pool.extend(
            residual
                .iter()
                .enumerate()
                .filter(|&(i, _)| !used.test(i))
                .map(|(_, &g)| g),
        );
        self.set_spans[v.idx()] = pool_span::<Cfg>(start, self.set_pool.len(), "Match::set_pool");
    }
}

// ---------------------------------------------------------------------------
// MatchPool — recycled match storage across queries
// ---------------------------------------------------------------------------

/// A reusable buffer of matches.
///
/// `run_query` emits one `Match` per solution, and each `Match` owns nine
/// `Vec`s. Freshly allocating them per match cost about nine allocations per
/// emitted match, and freeing them at the end of the round cost as many again —
/// on the `plain7` workload that is the single largest source of allocator
/// traffic in saturation.
///
/// A pool keeps the matches from the previous query alive and overwrites them:
/// `len` is the number currently valid, `slots` is however many were ever
/// allocated. Pushing into a slot that already exists is `Match::clone_from`,
/// which reuses that slot's nine buffers. Because a saturation round runs many
/// queries whose match counts are similar, the pool reaches its high-water mark
/// in the first round and allocates almost nothing afterwards.
///
/// Correctness note: [`Self::matches_mut`] hands out only `&mut [Match]` of
/// length `len`, so a stale slot beyond `len` is unreachable — its contents are
/// overwritten before ever being read.
/// Correctness note 2: the two scratch free-lists ([`Self::take_id_buf`] and
/// friends) are deliberately *not* touched by [`Self::clear`]. They hold no
/// query state — every borrower fills them from scratch before reading, since
/// `seq_children`/`set_children`/`mset_children` all begin with `buf.clear()` —
/// so surviving a `clear` is the whole point of them.
pub struct MatchPool<Cfg: EGraphConfig> {
    /// Flat stride-packed storage (E17): the per-slot form allocated ~5 vecs
    /// per fresh slot up to the query's high-water — 76k slots and ~380k
    /// allocations on ac10/naive — where the flat arrays grow amortized.
    set: MatchSet<Cfg>,
    /// Retired child-id buffers, lent to the `ExpandA`/`DecomposeACI` steps.
    id_bufs: Vec<Vec<Cfg::G>>,
    /// Retired `(id, multiplicity)` buffers, lent to the `DecomposeAC` step.
    mset_bufs: Vec<Vec<(Cfg::G, Cfg::M)>>,
    /// Partial-match extensions the current query has explored — one per
    /// `run_step` entry. Reset by `run_query_into` and folded into the
    /// thread-local match-step counter when the query finishes; see the
    /// match-work instrumentation notes at the top of this file.
    steps: u64,
    /// [`op_filter_policy`] as of this query's start. Carried on the pool
    /// because it is the only per-query state `run_join` already receives; see
    /// [`OP_FILTER_POLICY`] for why it is not read per join.
    op_filter_policy: OpFilterPolicy,
}

impl<Cfg: EGraphConfig> Default for MatchPool<Cfg> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Cfg: EGraphConfig> MatchPool<Cfg> {
    pub fn new() -> Self {
        Self {
            set: MatchSet::empty(),
            id_bufs: Vec::new(),
            mset_bufs: Vec::new(),
            steps: 0,
            op_filter_policy: OpFilterPolicy::Adaptive,
        }
    }

    /// Adopt a query's shape, dropping stored matches and keeping every flat
    /// allocation warm.
    pub fn reshape(&mut self, shape: &crate::resolve::MatchShape) {
        self.set.reshape(shape);
    }

    /// One stored match, by row.
    #[inline]
    pub fn row_mut(&mut self, j: usize) -> MatchRow<'_, Cfg> {
        MatchRow {
            set: &mut self.set,
            j,
        }
    }

    /// Reconstruct row `j` as an owned `Match` (tests and diagnostics; this
    /// allocates and the hot paths never call it).
    pub fn clone_match(&self, j: usize) -> Match<Cfg> {
        let s = &self.set;
        let mut m = Match {
            nodes: (0..s.node_stride)
                .map(|i| Some(s.nodes[j * s.node_stride + i]))
                .collect(),
            mults: s.mults[j * s.mult_stride..(j + 1) * s.mult_stride].to_vec(),
            lit_vals: s.lit_vals[j * s.lit_stride..(j + 1) * s.lit_stride].to_vec(),
            seq_pool: Vec::new(),
            seq_spans: vec![empty_span::<Cfg>(); s.seq_stride],
            set_pool: Vec::new(),
            set_spans: vec![empty_span::<Cfg>(); s.set_stride],
            mset_pool: Vec::new(),
            mset_spans: vec![empty_span::<Cfg>(); s.mset_stride],
        };
        for i in 0..s.seq_stride {
            let span = s.seq_spans[j * s.seq_stride + i];
            let start = m.seq_pool.len();
            m.seq_pool
                .extend_from_slice(&s.seq_pool[span_range::<Cfg>(span)]);
            m.seq_spans[i] = pool_span::<Cfg>(start, m.seq_pool.len(), "clone_match:seq");
        }
        for i in 0..s.set_stride {
            let span = s.set_spans[j * s.set_stride + i];
            let start = m.set_pool.len();
            m.set_pool
                .extend_from_slice(&s.set_pool[span_range::<Cfg>(span)]);
            m.set_spans[i] = pool_span::<Cfg>(start, m.set_pool.len(), "clone_match:set");
        }
        for i in 0..s.mset_stride {
            let span = s.mset_spans[j * s.mset_stride + i];
            let start = m.mset_pool.len();
            m.mset_pool
                .extend_from_slice(&s.mset_pool[span_range::<Cfg>(span)]);
            m.mset_spans[i] = pool_span::<Cfg>(start, m.mset_pool.len(), "clone_match:mset");
        }
        m
    }

    /// Borrow a child-id buffer, by move.
    ///
    /// By move rather than by reference because the borrower passes `&mut self`
    /// down the same call it uses the buffer in, so a `&mut` into the pool could
    /// not coexist with it. The caller must return it via [`Self::give_id_buf`];
    /// failing to is a leak of one allocation, not a correctness bug.
    #[inline]
    fn take_id_buf(&mut self) -> Vec<Cfg::G> {
        self.id_bufs.pop().unwrap_or_default()
    }

    #[inline]
    fn give_id_buf(&mut self, buf: Vec<Cfg::G>) {
        self.id_bufs.push(buf);
    }

    #[inline]
    fn take_mset_buf(&mut self) -> Vec<(Cfg::G, Cfg::M)> {
        self.mset_bufs.pop().unwrap_or_default()
    }

    #[inline]
    fn give_mset_buf(&mut self, buf: Vec<(Cfg::G, Cfg::M)>) {
        self.mset_bufs.push(buf);
    }

    /// Drop the previous query's results without releasing their storage.
    #[inline]
    pub fn clear(&mut self) {
        self.set.clear();
    }

    /// Append a copy of `env` into the flat store.
    #[inline]
    pub fn push(&mut self, env: &Match<Cfg>) {
        self.set.push(env);
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.set.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }
}

// ---------------------------------------------------------------------------
// MatchSet — flat SoA storage for multiple matches
// ---------------------------------------------------------------------------

/// Flat, stride-packed storage for all matches of a query.
///
/// Each variable kind occupies a single `Vec` with `stride` entries per match.
/// Stride = number of variables of that kind (from `MatchShape`).
/// Rest data lives in shared append-only pools; per-match spans are strided.
pub struct MatchSet<Cfg: EGraphConfig> {
    pub count: usize,
    node_stride: usize,
    mult_stride: usize,
    lit_stride: usize,
    seq_stride: usize,
    set_stride: usize,
    mset_stride: usize,
    nodes: Vec<Cfg::G>,
    mults: Vec<Cfg::M>,
    lit_vals: Vec<Cfg::V>,
    seq_spans: Vec<PoolSpan<Cfg>>,
    set_spans: Vec<PoolSpan<Cfg>>,
    mset_spans: Vec<PoolSpan<Cfg>>,
    seq_pool: Vec<Cfg::G>,
    set_pool: Vec<Cfg::G>,
    mset_pool: Vec<Cfg::C>,
}

impl<Cfg: EGraphConfig> MatchSet<Cfg> {
    pub fn new(shape: &crate::resolve::MatchShape) -> Self {
        Self {
            count: 0,
            node_stride: shape.num_vars(),
            mult_stride: shape.num_mult_vars(),
            lit_stride: shape.num_lit_val_vars(),
            seq_stride: shape.num_seq_vars(),
            set_stride: shape.num_set_vars(),
            mset_stride: shape.num_mset_vars(),
            nodes: Vec::new(),
            mults: Vec::new(),
            lit_vals: Vec::new(),
            seq_spans: Vec::new(),
            set_spans: Vec::new(),
            mset_spans: Vec::new(),
            seq_pool: Vec::new(),
            set_pool: Vec::new(),
            mset_pool: Vec::new(),
        }
    }

    /// A shapeless set (every stride zero); given a real shape by
    /// [`Self::reshape`] before first use. What lets one warm store serve
    /// queries of different shapes across a whole saturation.
    pub fn empty() -> Self {
        Self {
            count: 0,
            node_stride: 0,
            mult_stride: 0,
            lit_stride: 0,
            seq_stride: 0,
            set_stride: 0,
            mset_stride: 0,
            nodes: Vec::new(),
            mults: Vec::new(),
            lit_vals: Vec::new(),
            seq_spans: Vec::new(),
            set_spans: Vec::new(),
            mset_spans: Vec::new(),
            seq_pool: Vec::new(),
            set_pool: Vec::new(),
            mset_pool: Vec::new(),
        }
    }

    /// Adopt a query's shape: set the strides and drop stored matches, keeping
    /// every flat allocation (the warm-reuse discipline across queries).
    pub fn reshape(&mut self, shape: &crate::resolve::MatchShape) {
        self.node_stride = shape.num_vars();
        self.mult_stride = shape.num_mult_vars();
        self.lit_stride = shape.num_lit_val_vars();
        self.seq_stride = shape.num_seq_vars();
        self.set_stride = shape.num_set_vars();
        self.mset_stride = shape.num_mset_vars();
        self.count = 0;
        self.nodes.clear();
        self.mults.clear();
        self.lit_vals.clear();
        self.seq_spans.clear();
        self.set_spans.clear();
        self.mset_spans.clear();
        self.seq_pool.clear();
        self.set_pool.clear();
        self.mset_pool.clear();
    }

    /// Append one match.
    pub fn push(&mut self, m: &Match<Cfg>) {
        // `extend` over a sized iterator, not a `push` per variable: the
        // capacity check moves out of the loop, and this runs once per match.
        self.nodes
            .extend(m.nodes[..self.node_stride].iter().map(|v| v.unwrap()));
        if !m.mults.is_empty() {
            self.mults.extend_from_slice(&m.mults);
        }
        if !m.lit_vals.is_empty() {
            self.lit_vals.extend_from_slice(&m.lit_vals);
        }
        for &span in &m.seq_spans {
            let start = self.seq_pool.len();
            self.seq_pool
                .extend_from_slice(&m.seq_pool[span_range::<Cfg>(span)]);
            self.seq_spans.push(pool_span::<Cfg>(
                start,
                self.seq_pool.len(),
                "MatchSet::seq_pool",
            ));
        }
        for &span in &m.set_spans {
            let start = self.set_pool.len();
            self.set_pool
                .extend_from_slice(&m.set_pool[span_range::<Cfg>(span)]);
            self.set_spans.push(pool_span::<Cfg>(
                start,
                self.set_pool.len(),
                "MatchSet::set_pool",
            ));
        }
        for &span in &m.mset_spans {
            let start = self.mset_pool.len();
            self.mset_pool
                .extend_from_slice(&m.mset_pool[span_range::<Cfg>(span)]);
            self.mset_spans.push(pool_span::<Cfg>(
                start,
                self.mset_pool.len(),
                "MatchSet::mset_pool",
            ));
        }
        self.count += 1;
    }

    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    pub fn len(&self) -> usize {
        self.count
    }

    pub fn get_node(&self, v: VarId, j: usize) -> Cfg::G {
        self.nodes[j * self.node_stride + v.idx()]
    }
    pub fn get_mult(&self, v: MultVarId, j: usize) -> Cfg::M {
        self.mults[j * self.mult_stride + v.idx()]
    }
    pub fn get_lit_val(&self, v: LitValVarId, j: usize) -> Cfg::V {
        self.lit_vals[j * self.lit_stride + v.idx()]
    }
    pub fn set_node(&mut self, v: VarId, j: usize, val: Cfg::G) {
        self.nodes[j * self.node_stride + v.idx()] = val;
    }
    pub fn set_mult(&mut self, v: MultVarId, j: usize, val: Cfg::M) {
        self.mults[j * self.mult_stride + v.idx()] = val;
    }
    pub fn seq_slice(&self, v: SeqVarId, j: usize) -> &[Cfg::G] {
        let span = self.seq_spans[j * self.seq_stride + v.idx()];
        &self.seq_pool[span_range::<Cfg>(span)]
    }
    pub fn set_slice(&self, v: SetVarId, j: usize) -> &[Cfg::G] {
        let span = self.set_spans[j * self.set_stride + v.idx()];
        &self.set_pool[span_range::<Cfg>(span)]
    }
    pub fn mset_slice(&self, v: MsetVarId, j: usize) -> &[Cfg::C] {
        let span = self.mset_spans[j * self.mset_stride + v.idx()];
        &self.mset_pool[span_range::<Cfg>(span)]
    }

    /// Drop the stored matches without releasing storage (the `MatchPool`
    /// warm-reuse discipline, for consumers that keep a `MatchSet` across
    /// queries).
    pub fn clear(&mut self) {
        self.count = 0;
        self.nodes.clear();
        self.mults.clear();
        self.lit_vals.clear();
        self.seq_spans.clear();
        self.set_spans.clear();
        self.mset_spans.clear();
        self.seq_pool.clear();
        self.set_pool.clear();
        self.mset_pool.clear();
    }
}

// ---------------------------------------------------------------------------
// MatchView — one access surface over an owned Match and a MatchSet row
// ---------------------------------------------------------------------------

/// The binding-access surface `apply` consumes: reads of every variable kind
/// plus the two scalar writes RHS comprehensions perform. Implemented by the
/// in-progress `Match` and by [`MatchRow`], so the apply loop is agnostic to
/// whether matches live in per-slot vectors or the flat store.
pub trait MatchView<Cfg: EGraphConfig> {
    fn get(&self, v: VarId) -> Cfg::G;
    fn get_mult(&self, v: MultVarId) -> Cfg::M;
    fn get_lit_val(&self, v: LitValVarId) -> Cfg::V;
    fn seq_slice(&self, v: SeqVarId) -> &[Cfg::G];
    fn set_slice(&self, v: SetVarId) -> &[Cfg::G];
    fn mset_slice(&self, v: MsetVarId) -> &[Cfg::C];
    fn set(&mut self, v: VarId, val: Cfg::G);
    fn set_mult(&mut self, v: MultVarId, val: Cfg::M);
    /// Unbind `v` after a comprehension. On the owned `Match` this restores
    /// the panic-on-read guard; the flat store holds no unbound state, so a
    /// row leaves the stale value in place — equivalent for every compiled
    /// action sequence, which sets a comprehension variable before each read.
    fn clear(&mut self, v: VarId);
}

impl<Cfg: EGraphConfig> MatchView<Cfg> for Match<Cfg> {
    fn get(&self, v: VarId) -> Cfg::G {
        Match::get(self, v)
    }
    fn get_mult(&self, v: MultVarId) -> Cfg::M {
        Match::get_mult(self, v)
    }
    fn get_lit_val(&self, v: LitValVarId) -> Cfg::V {
        Match::get_lit_val(self, v)
    }
    fn seq_slice(&self, v: SeqVarId) -> &[Cfg::G] {
        Match::seq_slice(self, v)
    }
    fn set_slice(&self, v: SetVarId) -> &[Cfg::G] {
        Match::set_slice(self, v)
    }
    fn mset_slice(&self, v: MsetVarId) -> &[Cfg::C] {
        Match::mset_slice(self, v)
    }
    fn set(&mut self, v: VarId, val: Cfg::G) {
        Match::set(self, v, val)
    }
    fn set_mult(&mut self, v: MultVarId, val: Cfg::M) {
        Match::set_mult(self, v, val)
    }
    fn clear(&mut self, v: VarId) {
        Match::clear(self, v)
    }
}

/// One match of a [`MatchSet`], by row index.
pub struct MatchRow<'a, Cfg: EGraphConfig> {
    set: &'a mut MatchSet<Cfg>,
    j: usize,
}

impl<'a, Cfg: EGraphConfig> MatchView<Cfg> for MatchRow<'a, Cfg> {
    fn get(&self, v: VarId) -> Cfg::G {
        self.set.get_node(v, self.j)
    }
    fn get_mult(&self, v: MultVarId) -> Cfg::M {
        self.set.get_mult(v, self.j)
    }
    fn get_lit_val(&self, v: LitValVarId) -> Cfg::V {
        self.set.get_lit_val(v, self.j)
    }
    fn seq_slice(&self, v: SeqVarId) -> &[Cfg::G] {
        self.set.seq_slice(v, self.j)
    }
    fn set_slice(&self, v: SetVarId) -> &[Cfg::G] {
        self.set.set_slice(v, self.j)
    }
    fn mset_slice(&self, v: MsetVarId) -> &[Cfg::C] {
        self.set.mset_slice(v, self.j)
    }
    fn set(&mut self, v: VarId, val: Cfg::G) {
        self.set.set_node(v, self.j, val);
    }
    fn set_mult(&mut self, v: MultVarId, val: Cfg::M) {
        self.set.set_mult(v, self.j, val);
    }
    fn clear(&mut self, _v: VarId) {}
}

// ---------------------------------------------------------------------------
// Cloned iterator adapter
// ---------------------------------------------------------------------------

/// Adapter that wraps `MatchIterator` and yields owned `Match<Cfg>` clones.
pub struct ClonedMatchIter<'a, Cfg: EGraphConfig, L: LitVal, S: Copy, const T: bool, const P: bool>
{
    inner: MatchIterator<'a, Cfg, L, S, T, P>,
}

impl<'a, Cfg, L, S: Copy, const T: bool, const P: bool> Iterator
    for ClonedMatchIter<'a, Cfg, L, S, T, P>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    type Item = Match<Cfg>;
    fn next(&mut self) -> Option<Match<Cfg>> {
        if self.inner.next_match() {
            Some(self.inner.env().clone())
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------------------
// Match iterator
// ---------------------------------------------------------------------------

/// Collects all matches of `plan` against `eg`/`index` into a fresh `Vec`.
///
/// Convenience wrapper over [`run_query_into`] for callers that run one query
/// and do not care about allocation — tests, the REPL, `EGraph::run_query`. The
/// saturation drivers use `run_query_into` with a persistent [`MatchPool`].
pub fn run_query<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    plan: &QueryPlan<Cfg::O, Cfg::Index, L>,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> Vec<Match<Cfg>>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut pool = MatchPool::new();
    run_query_into(plan, eg, index, globals, &mut pool);
    (0..pool.len()).map(|j| pool.clone_match(j)).collect()
}

/// The round's class representative for `id` — the one the index snapshot was
/// built with, not the e-graph's live one.
///
/// Matching is specified against the e-graph as of the round's index build
/// (chapter 09). The e-graph keeps changing inside a round: every rule's
/// actions merge classes and add nodes before the next rule matches, while the
/// index buckets stay keyed by the reprs of the build. Canonicalizing with the
/// live union-find and then probing a bucket keyed at build time therefore
/// reads a bucket belonging to a different class — `ByRepr` and `ByChildPos`
/// go wrong in opposite directions on the same merge — and `CheckChildEq`
/// accepts pairs that the snapshot kept apart. Which of those a query performs
/// is decided by the join order, so the match set became a function of the
/// plan (measured at 2.9% on `comparison/math-microbenchmark.rules.egg`).
/// Every canonicalization in the matcher goes through here instead.
///
/// The fallback covers ids the snapshot does not know: a delta store defers to
/// its full index (which is where the mapping is kept), and a global may be
/// bound to a node minted after the build. Bindings never need it — each one
/// descends from a snapshot bucket.
#[inline]
fn canon<Cfg, L, const TRACK: bool, const PROOFS: bool>(
    index: &VariantIndex<'_, Cfg>,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    id: Cfg::G,
) -> Cfg::G
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    match index.full.round_repr(id) {
        Some(r) => r,
        None => eg.find_const(id),
    }
}

/// Collect all matches of `plan` into `pool`, reusing its storage.
///
/// The pool is cleared first, so a caller may hand the same pool to every query
/// in a round; see [`MatchPool`] for why that is where the win is.
pub fn run_query_into<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    plan: &QueryPlan<Cfg::O, Cfg::Index, L>,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    pool.reshape(&plan.shape);
    pool.steps = 0;
    pool.op_filter_policy = op_filter_policy();
    let mut env = Match::new(&plan.shape);
    let exec = Exec::<Cfg, L, S>::static_plan(&plan.steps);
    run_step(&exec, 0, eg, index, globals, &mut env, pool);
    add_match_steps(pool.steps);
}

/// Collect all matches of `rq` into `pool`, choosing the atom order at plan time
/// (`plan`) or per binding, according to [`runtime_scheduling`].
///
/// `plan` is `rq` scheduled by [`schedule_with_stats`](crate::schedule::schedule_with_stats).
/// It is what runs with the flag off, and it is also the fallback for a query
/// too wide for the runtime scheduler's masks (see [`ADAPTIVE_MAX_WIDTH`]), so a
/// caller passes both and gets the same match set either way.
pub fn run_query_scheduled_into<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    rq: &crate::resolve::ResolvedQuery<Cfg::O, S, L>,
    plan: &QueryPlan<Cfg::O, Cfg::Index, L>,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if !runtime_scheduling() || !Adaptive::<Cfg, L, S>::fits(rq) {
        run_query_into(plan, eg, index, globals, pool);
        return;
    }
    pool.reshape(&rq.shape);
    pool.steps = 0;
    pool.op_filter_policy = op_filter_policy();
    let mut env = Match::new(&rq.shape);
    let adaptive = Adaptive::new(rq);
    let exec = Exec::adaptive(&adaptive);
    run_step(&exec, 0, eg, index, globals, &mut env, pool);
    add_match_steps(pool.steps);
}

/// [`run_query_scheduled_into`] into a fresh `Vec`; the counterpart of
/// [`run_query`] for callers that want the flag respected.
pub fn run_query_scheduled<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    rq: &crate::resolve::ResolvedQuery<Cfg::O, S, L>,
    plan: &QueryPlan<Cfg::O, Cfg::Index, L>,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> Vec<Match<Cfg>>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut pool = MatchPool::new();
    run_query_scheduled_into(rq, plan, eg, index, globals, &mut pool);
    (0..pool.len()).map(|j| pool.clone_match(j)).collect()
}

// ---------------------------------------------------------------------------
// Runtime atom scheduling
// ---------------------------------------------------------------------------

thread_local! {
    /// Whether the matcher picks the next atom per binding instead of once per
    /// query. Off by default: the plan-time order stays the shipped one.
    ///
    /// Thread-local rather than process-wide like [`OP_FILTER_POLICY`], because
    /// it is read once per query rather than once per join — so the argument
    /// that made that one an atomic does not apply here — and because the
    /// differential tests run one match set with the flag on against another
    /// with it off, which a process-wide flag would make order-dependent under
    /// the test harness's thread pool.
    static RUNTIME_SCHEDULING: Cell<bool> = const { Cell::new(false) };
}

/// Turn runtime (per-binding) atom scheduling on or off for subsequent queries
/// run through [`run_query_scheduled_into`]. Per thread, read at query start.
pub fn set_runtime_scheduling(on: bool) {
    RUNTIME_SCHEDULING.with(|c| c.set(on));
}

/// Whether runtime atom scheduling is in force on this thread.
pub fn runtime_scheduling() -> bool {
    RUNTIME_SCHEDULING.with(|c| c.get())
}

/// Atoms and node variables a runtime-scheduled query may have.
///
/// The scheduler state that the static scheduler keeps in two `Vec<bool>` —
/// which atoms are used, which variables are bound — is a pair of `u64` masks
/// here, because it is carried per stack frame and keys the lowering memo. A
/// wider query falls back to its static plan, which is a performance decision
/// and not a correctness one: no rule in the corpus has more than a handful of
/// atoms.
pub const ADAPTIVE_MAX_WIDTH: usize = 64;

/// Memo key for the eager block, in the slot that otherwise holds an atom index.
const EAGER: u32 = u32::MAX;

/// One lowered block of steps, with the scheduler state it leaves behind.
///
/// `steps` is shared rather than owned because the same block is re-entered once
/// per partial match that reaches the same decision point, and re-lowering it
/// there was the whole cost this memo exists to avoid; an `Rc` clone is a
/// refcount bump and the borrow lives on the executing frame's stack.
struct Segment<Cfg: EGraphConfig, L: LitVal> {
    steps: std::rc::Rc<[Step<Cfg::O, Cfg::Index, L>]>,
    bound: u64,
    used: u64,
}

impl<Cfg: EGraphConfig, L: LitVal> Clone for Segment<Cfg, L> {
    fn clone(&self) -> Self {
        Self {
            steps: self.steps.clone(),
            bound: self.bound,
            used: self.used,
        }
    }
}

/// The query a runtime-scheduled execution schedules from, plus its lowering
/// memo.
///
/// `emit_atom`'s output is a function of the atom and of which variables are
/// bound when it is emitted, so a block is memoized under
/// `(atom, bound-mask, used-mask)` and computed once per distinct mask a run
/// reaches. There are few of those — a k-atom rule reaches at most the k! atom
/// prefixes, and in practice a handful — so the memo is a linear-scanned vector
/// rather than a hash map: three-word key comparisons over a few entries beat
/// hashing one on the per-partial-match path.
struct Adaptive<'q, Cfg: EGraphConfig, L: LitVal, S: Copy> {
    atoms: &'q [crate::resolve::RAtom<Cfg::O, S, L>],
    /// Atoms phase B ranges over: every atom that is not an equality. The
    /// equalities are the eager pass's business and are never costed, exactly
    /// as in the static loop's `min_by` filter.
    costed: u64,
    num_vars: usize,
    memo: std::cell::RefCell<Vec<((u32, u64, u64), Segment<Cfg, L>)>>,
}

impl<'q, Cfg: EGraphConfig, L: LitVal, S: Copy> Adaptive<'q, Cfg, L, S> {
    /// Whether `rq` fits the mask width; see [`ADAPTIVE_MAX_WIDTH`].
    fn fits(rq: &crate::resolve::ResolvedQuery<Cfg::O, S, L>) -> bool {
        rq.atoms.len() <= ADAPTIVE_MAX_WIDTH && rq.shape.num_vars() <= ADAPTIVE_MAX_WIDTH
    }

    fn new(rq: &'q crate::resolve::ResolvedQuery<Cfg::O, S, L>) -> Self {
        let mut costed = 0u64;
        for (i, atom) in rq.atoms.iter().enumerate() {
            if !matches!(
                atom,
                crate::resolve::RAtom::Eq(..) | crate::resolve::RAtom::EqGlobal(..)
            ) {
                costed |= 1 << i;
            }
        }
        Self {
            atoms: &rq.atoms,
            costed,
            num_vars: rq.shape.num_vars(),
            memo: std::cell::RefCell::new(Vec::new()),
        }
    }

    /// The block `chosen` lowers to at `(bound, used)`: the eager fixpoint when
    /// `chosen` is [`EAGER`], otherwise that one atom's join and its reads.
    fn segment(&self, chosen: u32, bound: u64, used: u64) -> Segment<Cfg, L> {
        let key = (chosen, bound, used);
        if let Some((_, seg)) = self.memo.borrow().iter().find(|(k, _)| *k == key) {
            return seg.clone();
        }
        // `ADAPTIVE_MAX_WIDTH` bools of stack, in the two shapes the scheduler's
        // lowering takes its state in.
        let mut bound_buf = [false; ADAPTIVE_MAX_WIDTH];
        let mut used_buf = [false; ADAPTIVE_MAX_WIDTH];
        let bound_arr = &mut bound_buf[..self.num_vars];
        let used_arr = &mut used_buf[..self.atoms.len()];
        for (i, b) in bound_arr.iter_mut().enumerate() {
            *b = bound & (1 << i) != 0;
        }
        for (i, u) in used_arr.iter_mut().enumerate() {
            *u = used & (1 << i) != 0;
        }
        let mut steps = Vec::new();
        if chosen == EAGER {
            crate::schedule::lower_eager(self.atoms, used_arr, bound_arr, &mut steps);
        } else {
            let ai = chosen as usize;
            crate::schedule::emit_atom(&self.atoms[ai], ai, bound_arr, &mut steps);
            used_arr[ai] = true;
        }
        let seg = Segment {
            steps: steps.into(),
            bound: mask_of(bound_arr),
            used: mask_of(used_arr),
        };
        self.memo.borrow_mut().push((key, seg.clone()));
        seg
    }
}

fn mask_of(flags: &[bool]) -> u64 {
    flags
        .iter()
        .enumerate()
        .fold(0u64, |m, (i, &b)| if b { m | (1 << i) } else { m })
}

/// A position the matcher executes from: a slice of steps, and — under runtime
/// scheduling — what to do when it runs out.
///
/// Statically scheduled, `steps` is the whole plan and `adaptive` is `None`, so
/// this is the `&QueryPlan` the engine used to carry. Runtime-scheduled, `steps`
/// is one lowered block owned by the frame that chose it, and the masks are the
/// scheduler state at its end. The chain of frames on the stack is the order
/// chosen for the partial match under execution; a sibling binding at the same
/// depth may choose a different one.
struct Exec<'a, Cfg: EGraphConfig, L: LitVal, S: Copy> {
    steps: &'a [Step<Cfg::O, Cfg::Index, L>],
    adaptive: Option<&'a Adaptive<'a, Cfg, L, S>>,
    bound: u64,
    used: u64,
}

impl<'a, Cfg: EGraphConfig, L: LitVal, S: Copy> Exec<'a, Cfg, L, S> {
    fn static_plan(steps: &'a [Step<Cfg::O, Cfg::Index, L>]) -> Self {
        Self {
            steps,
            adaptive: None,
            bound: 0,
            used: 0,
        }
    }

    /// The empty prefix of a runtime-scheduled run: the first thing the engine
    /// does is hit the end of it, which is the first decision point.
    fn adaptive(ad: &'a Adaptive<'a, Cfg, L, S>) -> Self {
        Self {
            steps: &[],
            adaptive: Some(ad),
            bound: 0,
            used: 0,
        }
    }
}

/// Decide what runs next, at the end of a runtime-scheduled block.
///
/// The two phases of the static scheduling loop (chapter 08), one iteration per
/// call, with the environment live: the eager pass to fixpoint, then the
/// cheapest remaining atom. The order is the same as the static one because it
/// is the same code lowering the same atoms; only the choice in phase B is made
/// from the bindings in hand rather than from a per-round average.
///
/// Both phases run against the state at the end of the current block, and the
/// block below is executed before the next decision, so every variable the
/// scheduler calls bound is actually set in `env` when phase B reads it.
fn advance<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    ad: &Adaptive<'_, Cfg, L, S>,
    exec: &Exec<'_, Cfg, L, S>,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &mut Match<Cfg>,
    results: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let eager = ad.segment(EAGER, exec.bound, exec.used);
    if !eager.steps.is_empty() {
        let next = Exec {
            steps: &eager.steps,
            adaptive: Some(ad),
            bound: eager.bound,
            used: eager.used,
        };
        run_step(&next, 0, eg, index, globals, env, results);
        return;
    }

    // No atom left to schedule: every atom is used, or the ones left are
    // equalities between two unbound variables, which the static scheduler
    // leaves unenforced for the same reason (nothing else in the query binds
    // them). Either way the environment is a match.
    let Some(ai) = choose_atom(ad, exec, eg, index, globals, env) else {
        results.steps += 1;
        results.push(env);
        return;
    };
    let seg = ad.segment(ai as u32, exec.bound, exec.used);
    let next = Exec {
        steps: &seg.steps,
        adaptive: Some(ad),
        bound: seg.bound,
        used: seg.used,
    };
    run_step(&next, 0, eg, index, globals, env, results);
}

/// The unused atom whose join opens the shortest cursor under the current
/// bindings, or `None` if none is schedulable.
///
/// Phase B of the scheduling loop with the estimator replaced by a measurement.
/// The static scheduler prices an atom by its relation scaled by one measured
/// mean fan-out per bound key (`schedule::estimate_cost`); those means are
/// averages over skewed distributions, so they are right about the workload and
/// wrong about the binding (chapter 20, Fact 2). Here the atom is priced by the
/// length of the shortest bucket its join would actually open, which is the
/// leapfrog intersection's own bound on the candidates it can propose: an upper
/// bound on the work, exact for a single-lookup join, and read from the buckets
/// the join is about to open anyway.
///
/// Ties keep the lowest atom index, so the choice is a function of the bindings
/// and the atom numbering and nothing else.
fn choose_atom<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    ad: &Adaptive<'_, Cfg, L, S>,
    exec: &Exec<'_, Cfg, L, S>,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &Match<Cfg>,
) -> Option<usize>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let candidates = ad.costed & !exec.used;
    // One candidate is its own minimum. Worth the branch because it is the
    // common case — the last atom of every rule, and both remaining atoms of a
    // two-atom one — and because the alternative is a bucket resolution per
    // lookup that `run_join` is about to repeat.
    if candidates.count_ones() == 1 {
        let ai = candidates.trailing_zeros() as usize;
        #[cfg(test)]
        ATOM_CHOICE_LOG.with(|l| l.borrow_mut().push((exec.used, ai)));
        return Some(ai);
    }
    let mut best: Option<(usize, usize)> = None;
    for ai in 0..ad.atoms.len() {
        if candidates & (1 << ai) == 0 {
            continue;
        }
        let seg = ad.segment(ai as u32, exec.bound, exec.used);
        let len = cursor_len(&seg, ai, eg, index, globals, env);
        if best.is_none_or(|(b, _)| len < b) {
            best = Some((len, ai));
        }
    }
    #[cfg(test)]
    if let Some((_, ai)) = best {
        ATOM_CHOICE_LOG.with(|l| l.borrow_mut().push((exec.used, ai)));
    }
    best.map(|(_, ai)| ai)
}

#[cfg(test)]
thread_local! {
    /// One entry per phase-B decision: the atoms already scheduled, and the one
    /// chosen next. Drained by the tests that assert the choice is per binding;
    /// release has no probe on the path.
    static ATOM_CHOICE_LOG: std::cell::RefCell<Vec<(u64, usize)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Take and clear this thread's record of per-binding atom choices.
#[cfg(test)]
pub(crate) fn take_atom_choices() -> Vec<(u64, usize)> {
    ATOM_CHOICE_LOG.with(|l| std::mem::take(&mut *l.borrow_mut()))
}

/// Shortest bucket the block's join would open, in the slice this atom's
/// semi-naive mode reads.
///
/// One `len` per lookup on buckets `run_join` is about to resolve again, which
/// is the same pair of reads the operator-restriction policy already makes per
/// binding (see [`demote_by_op`]). `FullMinusDelta` reads the full side, an
/// upper bound on `full ∖ delta`, for the reason given in `run_join`: a tighter
/// number would cost the overlap, which is the work being priced.
fn cursor_len<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    seg: &Segment<Cfg, L>,
    atom_id: usize,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &Match<Cfg>,
) -> usize
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    // Every atom phase B costs lowers to a `Join` first; the ones that do not
    // are the equalities, which are filtered out before this is called.
    let Some(Step::Join { lookups, .. }) = seg.steps.first() else {
        return usize::MAX;
    };
    let store = match index.mode(atom_id) {
        IndexMode::Delta => index.delta,
        IndexMode::Full | IndexMode::FullMinusDelta => index.full,
    };
    let mut best = usize::MAX;
    for l in lookups {
        let len = bucket_in(store, index, l, eg, globals, env).len();
        if len < best {
            best = len;
        }
    }
    best
}

fn run_step<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    exec: &Exec<'_, Cfg, L, S>,
    step_idx: usize,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &mut Match<Cfg>,
    results: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if step_idx >= exec.steps.len() {
        // End of the step sequence. Statically scheduled, that is the whole
        // plan and the environment is a match; runtime-scheduled, it is a
        // decision point — `advance` either finds another atom to lower or
        // reaches the same conclusion. The step tally counts one per executed
        // step and one per emitted match in both modes, so the two are
        // comparable; the choice itself is not a step.
        match exec.adaptive {
            None => {
                results.steps += 1;
                results.push(env);
            }
            Some(ad) => advance(ad, exec, eg, index, globals, env, results),
        }
        return;
    }
    results.steps += 1;

    match &exec.steps[step_idx] {
        Step::Join {
            target,
            lookups,
            atom_id,
        } => {
            run_join(
                exec, step_idx, *target, lookups, *atom_id, eg, index, globals, env, results,
            );
        }
        Step::ExtractChild {
            target,
            parent,
            pos,
        } => {
            let parent_id = env.get(*parent);
            let child = eg.child_at(parent_id, *pos);
            env.set(*target, child);
            run_step(exec, step_idx + 1, eg, index, globals, env, results);
            env.clear(*target);
        }
        Step::CheckChildEq {
            parent,
            pos,
            expected,
        } => {
            let parent_id = env.get(*parent);
            let child = eg.child_at(parent_id, *pos);
            let exp = env.resolve_pv(*expected, globals);
            if canon(index, eg, child) == canon(index, eg, exp) {
                run_step(exec, step_idx + 1, eg, index, globals, env, results);
            }
        }
        Step::CheckEq { a, b } => {
            if canon(index, eg, env.get(*a)) == canon(index, eg, env.get(*b)) {
                run_step(exec, step_idx + 1, eg, index, globals, env, results);
            }
        }
        Step::CheckEqGlobal { local, global } => {
            if canon(index, eg, env.get(*local)) == canon(index, eg, globals.binding(*global)) {
                run_step(exec, step_idx + 1, eg, index, globals, env, results);
            }
        }
        Step::CopyBinding { target, other } => {
            let val = canon(index, eg, env.get(*other));
            env.set(*target, val);
            run_step(exec, step_idx + 1, eg, index, globals, env, results);
            env.clear(*target);
        }
        Step::ExpandA {
            node,
            children,
            pre,
            suf,
        } => {
            let node_id = env.get(*node);
            // Recycled through the pool: this step runs once per candidate node, so a
            // fresh `Vec` here was one allocation per match step (E14).
            let mut buf = results.take_id_buf();
            eg.seq_children(node_id, &mut buf);
            run_expand_a(
                exec, step_idx, children, *pre, *suf, &buf, eg, index, globals, env, results,
            );
            results.give_id_buf(buf);
        }
        Step::DecomposeAC {
            node,
            elems,
            rest,
            idempotent: _,
        } => {
            let node_id = env.get(*node);
            let mut residual = results.take_mset_buf();
            eg.mset_children(node_id, &mut residual);
            for entry in &mut residual {
                entry.0 = canon(index, eg, entry.0);
            }
            run_decompose_ac(
                exec,
                step_idx,
                elems,
                *rest,
                &mut residual,
                eg,
                index,
                globals,
                env,
                results,
            );
            results.give_mset_buf(residual);
        }
        Step::DecomposeACI { node, elems, rest } => {
            let node_id = env.get(*node);
            let mut residual = results.take_id_buf();
            eg.set_children(node_id, &mut residual);
            for entry in &mut residual {
                *entry = canon(index, eg, *entry);
            }
            run_decompose_aci(
                exec, step_idx, elems, *rest, &residual, eg, index, globals, env, results,
            );
            results.give_id_buf(residual);
        }
        Step::ExtractLitVal { node, val } => {
            let node_id = env.get(*node);
            if let Some(lit_val_id) = eg.get_lit_val_id(node_id) {
                env.set_lit_val(*val, lit_val_id);
                run_step(exec, step_idx + 1, eg, index, globals, env, results);
            }
        }
        Step::CheckLit { node, value } => {
            let node_id = env.get(*node);
            if eg.get_lit_val(node_id) == Some(value) {
                run_step(exec, step_idx + 1, eg, index, globals, env, results);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// ExpandA — sequence (A) node decomposition
// ---------------------------------------------------------------------------

fn run_expand_a<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    exec: &Exec<'_, Cfg, L, S>,
    step_idx: usize,
    children: &[PatVar],
    pre: Option<SeqVarId>,
    suf: Option<SeqVarId>,
    seq: &[Cfg::G],
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &mut Match<Cfg>,
    results: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let nfixed = children.len();
    match (pre, suf) {
        (None, None) => {
            if seq.len() != nfixed {
                return;
            }
            bind_fixed_and_continue(
                exec, step_idx, children, seq, 0, eg, index, globals, env, results,
            );
        }
        (Some(p), None) => {
            if seq.len() < nfixed {
                return;
            }
            let split = seq.len() - nfixed;
            env.push_seq(p, &seq[..split]);
            bind_fixed_and_continue(
                exec, step_idx, children, seq, split, eg, index, globals, env, results,
            );
            env.pop_seq(p);
        }
        (None, Some(s)) => {
            if seq.len() < nfixed {
                return;
            }
            env.push_seq(s, &seq[nfixed..]);
            bind_fixed_and_continue(
                exec, step_idx, children, seq, 0, eg, index, globals, env, results,
            );
            env.pop_seq(s);
        }
        (Some(p), Some(s)) => {
            if seq.len() < nfixed {
                return;
            }
            let slack = seq.len() - nfixed;
            for offset in 0..=slack {
                env.push_seq(p, &seq[..offset]);
                env.push_seq(s, &seq[offset + nfixed..]);
                bind_fixed_and_continue(
                    exec, step_idx, children, seq, offset, eg, index, globals, env, results,
                );
                for &cv in children {
                    if let PatVar::Local(v) = cv {
                        env.clear(v)
                    };
                }
                env.pop_seq(s);
                env.pop_seq(p);
            }
        }
    }
}

fn bind_fixed_and_continue<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    exec: &Exec<'_, Cfg, L, S>,
    step_idx: usize,
    children: &[PatVar],
    seq: &[Cfg::G],
    offset: usize,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &mut Match<Cfg>,
    results: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    for (i, &cv) in children.iter().enumerate() {
        let val = seq[offset + i];
        match cv {
            PatVar::Global(gid) => {
                if canon(index, eg, globals.binding(gid)) != canon(index, eg, val) {
                    return;
                }
            }
            PatVar::Local(vid) => {
                if let Some(existing) = env.nodes[vid.idx()] {
                    if canon(index, eg, existing) != canon(index, eg, val) {
                        return;
                    }
                } else {
                    env.set(vid, val);
                }
            }
        }
    }
    run_step(exec, step_idx + 1, eg, index, globals, env, results);
    for &cv in children {
        if let PatVar::Local(v) = cv {
            env.clear(v)
        };
    }
}

// ---------------------------------------------------------------------------
// DecomposeAC — multiset (AC/ACI) node decomposition
// ---------------------------------------------------------------------------

/// Check whether `avail` satisfies a multiplicity requirement.
/// Exact(n): avail must equal n exactly.
/// Var with constraint: avail must be >= 1, satisfy the constraint,
/// and if the mult variable is already bound (non-zero), avail must
/// equal the bound value (non-linear variable consistency).
fn mult_matches(mult: &RMult, avail: u64, bound_mult: Option<u64>) -> bool {
    match mult {
        // Compared at the surface width. Narrowing `*n` to the configured
        // multiplicity width instead would make a literal above that width
        // alias onto a small multiplicity (`x:4294967297` matching 1); a
        // literal the configuration cannot represent simply never matches.
        RMult::Exact(n) => avail == *n,
        RMult::Var { constraint, .. } => {
            if avail < 1 {
                return false;
            }
            // Non-linear: if already bound, must match
            if let Some(prev) = bound_mult
                && prev > 0
                && avail != prev
            {
                return false;
            }
            match constraint {
                None => true,
                Some((op, val)) => {
                    let v = *val;
                    match op {
                        CmpOp::Ge => avail >= v,
                        CmpOp::Gt => avail > v,
                        CmpOp::Le => avail <= v,
                        CmpOp::Lt => avail < v,
                        CmpOp::Eq => avail == v,
                        CmpOp::Ne => avail != v,
                    }
                }
            }
        }
    }
}

/// Get the currently bound multiplicity for a mult variable, if any.
/// Returns Some(val) where val > 0 if already bound, None otherwise.
fn bound_mult_val<Cfg: EGraphConfig>(mult: &RMult, env: &Match<Cfg>) -> Option<u64> {
    match mult {
        RMult::Exact(_) => None,
        RMult::Var { var, .. } => {
            let v = env.get_mult(*var).to_u64();
            if v > 0 { Some(v) } else { None }
        }
    }
}
fn run_decompose_ac<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    exec: &Exec<'_, Cfg, L, S>,
    step_idx: usize,
    elems: &[(PatVar, RMult)],
    rest: Option<MsetVarId>,
    residual: &mut [(Cfg::G, Cfg::M)],
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &mut Match<Cfg>,
    results: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    decompose_ac_elem(
        exec, step_idx, elems, 0, rest, residual, eg, index, globals, env, results,
    );
}

fn decompose_ac_elem<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    exec: &Exec<'_, Cfg, L, S>,
    step_idx: usize,
    elems: &[(PatVar, RMult)],
    ei: usize,
    rest: Option<MsetVarId>,
    residual: &mut [(Cfg::G, Cfg::M)],
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &mut Match<Cfg>,
    results: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let zero = Cfg::M::ZERO;
    if ei >= elems.len() {
        if let Some(rv) = rest {
            env.push_mset_residual(rv, residual);
            run_step(exec, step_idx + 1, eg, index, globals, env, results);
            env.pop_mset(rv);
        } else if residual.iter().all(|&(_, m)| m == zero) {
            run_step(exec, step_idx + 1, eg, index, globals, env, results);
        }
        return;
    }

    let (var, mult) = &elems[ei];

    let bound_repr = match *var {
        PatVar::Global(gid) => Some(canon(index, eg, globals.binding(gid))),
        PatVar::Local(vid) => env.nodes[vid.idx()].map(|v| canon(index, eg, v)),
    };

    if let Some(repr) = bound_repr {
        if let Some(pos) = residual.iter().position(|&(r, m)| {
            r == repr && mult_matches(mult, m.to_u64(), bound_mult_val(mult, env))
        }) {
            let actual = residual[pos].1;
            let was_unbound = match mult {
                RMult::Var { var: mv, .. } => env.get_mult(*mv) == Cfg::M::ZERO,
                _ => false,
            };
            let take: Cfg::M = match mult {
                // `mult_matches` compared this entry against the literal at the
                // surface width, so an `Exact` match means the literal equals
                // `actual`; reuse it rather than narrowing the literal back
                // down, which is where the truncation used to happen.
                RMult::Exact(_) => actual,
                RMult::Var { var: mv, .. } => {
                    env.set_mult(*mv, actual);
                    actual
                }
            };
            let prev = residual[pos].1;
            residual[pos].1 = prev.saturating_sub(take);
            decompose_ac_elem(
                exec,
                step_idx,
                elems,
                ei + 1,
                rest,
                residual,
                eg,
                index,
                globals,
                env,
                results,
            );
            residual[pos].1 = prev;
            if was_unbound && let RMult::Var { var: mv, .. } = mult {
                env.set_mult(*mv, Cfg::M::ZERO);
            }
        }
        return;
    }

    let n = residual.len();
    for ri in 0..n {
        let (repr, avail) = residual[ri];
        if !mult_matches(mult, avail.to_u64(), bound_mult_val(mult, env)) {
            continue;
        }
        let PatVar::Local(vid) = *var else {
            unreachable!()
        };
        env.set(vid, repr);
        let was_unbound = match mult {
            RMult::Var { var: mv, .. } => env.get_mult(*mv) == Cfg::M::ZERO,
            _ => false,
        };
        let take: Cfg::M = match mult {
            // See the bound-repr path above: an `Exact` match means the literal
            // equals `avail` at the surface width.
            RMult::Exact(_) => avail,
            RMult::Var { var: mv, .. } => {
                env.set_mult(*mv, avail);
                avail
            }
        };
        let prev = residual[ri].1;
        residual[ri].1 = prev.saturating_sub(take);
        decompose_ac_elem(
            exec,
            step_idx,
            elems,
            ei + 1,
            rest,
            residual,
            eg,
            index,
            globals,
            env,
            results,
        );
        residual[ri].1 = prev;
        env.clear(vid);
        if was_unbound && let RMult::Var { var: mv, .. } = mult {
            env.set_mult(*mv, Cfg::M::ZERO);
        }
    }
}

// ---------------------------------------------------------------------------
// DecomposeACI — set node decomposition
// ---------------------------------------------------------------------------

fn run_decompose_aci<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    exec: &Exec<'_, Cfg, L, S>,
    step_idx: usize,
    elems: &[PatVar],
    rest: Option<SetVarId>,
    residual: &[Cfg::G],
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &mut Match<Cfg>,
    results: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut used = crate::containers::bitset::BitSet::new(residual.len());
    decompose_aci_elem(
        exec, step_idx, elems, 0, rest, residual, &mut used, eg, index, globals, env, results,
    );
}

fn decompose_aci_elem<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    exec: &Exec<'_, Cfg, L, S>,
    step_idx: usize,
    elems: &[PatVar],
    ei: usize,
    rest: Option<SetVarId>,
    residual: &[Cfg::G],
    used: &mut crate::containers::bitset::BitSet,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &mut Match<Cfg>,
    results: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if ei >= elems.len() {
        if let Some(rv) = rest {
            env.push_set_residual(rv, residual, used);
            run_step(exec, step_idx + 1, eg, index, globals, env, results);
            env.pop_set(rv);
        } else if (0..residual.len()).all(|i| used.test(i)) {
            run_step(exec, step_idx + 1, eg, index, globals, env, results);
        }
        return;
    }

    let var = elems[ei];
    let bound_repr = match var {
        PatVar::Global(gid) => Some(canon(index, eg, globals.binding(gid))),
        PatVar::Local(vid) => env.nodes[vid.idx()].map(|v| canon(index, eg, v)),
    };

    if let Some(repr) = bound_repr {
        if let Some(pos) = residual
            .iter()
            .enumerate()
            .position(|(i, &r)| !used.test(i) && r == repr)
        {
            used.set(pos);
            decompose_aci_elem(
                exec,
                step_idx,
                elems,
                ei + 1,
                rest,
                residual,
                used,
                eg,
                index,
                globals,
                env,
                results,
            );
            used.clear(pos);
        }
        return;
    }

    let PatVar::Local(vid) = var else {
        unreachable!()
    };
    for ri in 0..residual.len() {
        if used.test(ri) {
            continue;
        }
        env.set(vid, residual[ri]);
        used.set(ri);
        decompose_aci_elem(
            exec,
            step_idx,
            elems,
            ei + 1,
            rest,
            residual,
            used,
            eg,
            index,
            globals,
            env,
            results,
        );
        used.clear(ri);
        env.clear(vid);
    }
}

// ---------------------------------------------------------------------------
// Join — leapfrog intersection of index lookups
// ---------------------------------------------------------------------------

/// Relation size per candidate above which a join applies its operator
/// restriction as a per-candidate test rather than as a leapfrog operand, and
/// the ceiling that threshold stops climbing at.
///
/// The two mechanisms are priced by two lengths the join reads before it opens
/// anything: `m`, the smallest of the atom's other buckets, which bounds the
/// candidates the ring will propose, and `n = |by_op[op]|`. The test costs `m`
/// random loads into the round's `op` table. The operand costs a fixed start-up,
/// a sort of the ring plus a gallop of the `by_op` cursor to the bucket's first
/// key, plus one iteration per element of the smaller side, `min(m, n)`. The
/// rule is
///
/// ```text
/// filter  iff  n >= min(512 * m, 131_072)  and  m <= 2 * n
/// ```
///
/// **Where the ceiling comes from.** `tests/ematch_op_filter.rs::sweep` builds
/// `hubs` child classes with `m` parents each spread over eight operators,
/// `hubs * m` held at 262 144, against an `f0` relation of `n` with an empty
/// intersection, so no match construction is in either column. Median wall per
/// query, release, Apple M4 Pro; entries are `leapfrog / filter`, so below 1
/// means the operand won.
///
/// | m | n = 2 621 | 16 384 | 53 710 | 131 072 | 262 144 |
/// |---|---|---|---|---|---|
/// | 8 | 0.75 | 0.96 | 1.34 | 1.67 | 1.98 |
/// | 16 | 0.52 | 0.73 | 1.05 | 1.43 | 1.71 |
/// | 64 | 0.20 | 0.35 | 0.61 | 1.12 | 1.57 |
/// | 4 096 | 0.04 | 0.13 | 0.43 | 0.99 | 1.52 |
/// | 262 144 | 0.03 | 0.13 | 0.44 | 0.99 | 1.49 |
///
/// The test's cost per candidate is flat at 8.8 ns across the whole table: a
/// random load into a table of `4 * node_count` bytes, which no parameter here
/// changes. The filter column is therefore the same 2.3 ms of work everywhere and
/// only the operand moves. An iteration costs 0.5-2 ns against a relation that
/// fits in cache and 13-17 ns against one that does not, and the operand pays
/// for `min(m, n)` of them rather than `m`. Both effects favour the operand as
/// `n` falls, and past `n = 131 072` neither rescues it at any bucket size: that
/// is the ceiling. The same shape at the intersection densities the bucket sizes
/// admit, `n` set to the hub-parent population scaled by the density, says the
/// same thing and adds the extreme this policy exists for:
///
/// | m | n = 262 144 (dense) | n = 2 621 (1%) | n = 26 (0.01%) |
/// |---|---|---|---|
/// | 16 | 1.08 | 0.51 | 0.46 |
/// | 256 | 1.07 | 0.12 | 0.04 |
/// | 4 096 | 1.04 | 0.09 | 0.003 |
/// | 65 536 | 1.05 | 0.09 | 0.002 |
/// | 262 144 | 1.06 | 0.08 | 0.002 |
///
/// The bottom-right cell is 2.32 ms against 4 µs: a hub class with a quarter of
/// a million parents and a 26-node operator relation, which the unconditional
/// demotion this replaced ran 600x slower than it had to.
///
/// **Where the slope comes from, and where the two measurements disagree.** The
/// sweep says the threshold climbs with `m`, because a small bucket cannot
/// amortize the operand's start-up and so crosses over at a smaller `n`, and
/// fitting the rows above gives about 4 096 per candidate. `comparison/math-microbenchmark`
/// says otherwise. Its joins run with `m` between 2 and 128 against relations of
/// 8 k to 131 k, exactly the disputed window, and the whole-benchmark wall
/// against the slope constant is
///
/// | per candidate | 0 | 64 | 128 | 256 | 512 | 1 024 | 4 096 |
/// |---|---|---|---|---|---|---|---|
/// | rules encoding | 562.0 | 565.4 | 559.1 | 568.7 | 565.1 | 582.1 | 636.3 |
///
/// against 562.0 ms for the unconditional demotion, medians of nine interleaved
/// runs. Anything at or below 512 is inside the run-to-run spread; 4 096, the
/// value the sweep fits, costs 13%.
///
/// The sweep is the optimistic instrument in that window and the workload is the
/// realistic one. A sweep query probes one `by_op` vector 16 384 times with
/// nothing else touching memory in between, so the operand's seeks run against a
/// cache-resident relation; real matching interleaves several relations, the
/// `op` table, the child pool and match construction between joins, and the
/// relation is cold when the next join reaches it. That is exactly the `n`
/// range where the sweep measured 0.5-2 ns per iteration, and it is why the
/// slope is set from the workload at 512 rather than from the fit at 4 096. The
/// price is paid in the sweep's `m = 16` to `m = 64` rows just above the
/// threshold, where the rule takes the test and the operand was up to 2.0x
/// better; the extremes both instruments agree on are fenced by
/// `tests/ematch_op_filter.rs::adaptive_policy_is_within_1_2x_of_the_better_mechanism`.
const OP_FILTER_RELATION_PER_CANDIDATE: usize = 512;

/// Ceiling on the fitted threshold; see [`OP_FILTER_RELATION_PER_CANDIDATE`].
pub const OP_FILTER_MIN_RELATION: usize = 131_072;

/// How much a leapfrog iteration costs against one `op` table load, rounded up
/// from the 8.8 ns and 13-17 ns the sweep measured for the two.
///
/// Only binds when the bucket is more than twice the relation, which is past the
/// largest bucket the sweep covers: there `min(m, n) = n` makes the operand's
/// work independent of how far the bucket grows while the test's stays linear in
/// it, so the ceiling above would otherwise keep choosing the test forever.
const OP_FILTER_SEEK_COST: usize = 2;

/// Which mechanism a join uses for its `ByOp` restriction.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum OpFilterPolicy {
    /// Decide per binding from the two bucket lengths. The shipped policy; see
    /// [`OP_FILTER_MIN_RELATION`].
    Adaptive,
    /// Always demote `ByOp` to a per-candidate operator test.
    AlwaysFilter,
    /// Always keep `ByOp` in the leapfrog ring.
    AlwaysLeapfrog,
}

/// The live policy. A `static` rather than a constant so a measurement harness
/// can pin either mechanism without a rebuild; read once per query into
/// [`MatchPool`], never per join, because an atomic load inside `run_join` would
/// sit on the per-partial-match path for the benefit of a knob nothing turns.
static OP_FILTER_POLICY: AtomicUsize = AtomicUsize::new(0);

/// Pin the operator-restriction policy for subsequent queries. Process-wide, and
/// read at query start.
pub fn set_op_filter_policy(p: OpFilterPolicy) {
    OP_FILTER_POLICY.store(
        match p {
            OpFilterPolicy::Adaptive => 0,
            OpFilterPolicy::AlwaysFilter => 1,
            OpFilterPolicy::AlwaysLeapfrog => 2,
        },
        Ordering::Relaxed,
    );
}

/// The operator-restriction policy in force.
pub fn op_filter_policy() -> OpFilterPolicy {
    match OP_FILTER_POLICY.load(Ordering::Relaxed) {
        1 => OpFilterPolicy::AlwaysFilter,
        2 => OpFilterPolicy::AlwaysLeapfrog,
        _ => OpFilterPolicy::Adaptive,
    }
}

/// Which mechanism a join applied its `ByOp` restriction with. Recorded per
/// join execution in test builds only; release has no probe on the path.
#[cfg(test)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum OpRestriction {
    /// `ByOp` stayed in the leapfrog ring as an intersection operand.
    Leapfrog,
    /// `ByOp` was demoted to a per-candidate `op[id]` test.
    Filter,
}

#[cfg(test)]
thread_local! {
    /// One entry per join execution that had a `ByOp` restriction to place.
    /// Drained by the policy tests; see `op_restriction_log`.
    static OP_RESTRICTION_LOG: std::cell::RefCell<Vec<OpRestriction>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Take and clear this thread's record of per-join restriction decisions.
#[cfg(test)]
pub(crate) fn take_op_restriction_log() -> Vec<OpRestriction> {
    OP_RESTRICTION_LOG.with(|l| std::mem::take(&mut *l.borrow_mut()))
}

/// Decide how this join places its `ByOp` restriction: `true` to demote it to a
/// per-candidate operator test, `false` to keep it as a leapfrog operand.
///
/// `m` is the smallest of the atom's other buckets, `usize::MAX` when it has
/// none; `n` is `|by_op[op]|`, or `None` when the join has no `ByOp` to place,
/// which is a single-lookup `ByOp` scan: it has to stay a cursor because it is
/// the only thing enumerating anything. Two compares and a shift on values already
/// in registers; see [`OP_FILTER_RELATION_PER_CANDIDATE`] for where they come
/// from.
#[inline]
fn demote_by_op(m: usize, n: Option<usize>, policy: OpFilterPolicy) -> bool {
    let Some(n) = n else { return false };
    let demote = match policy {
        OpFilterPolicy::AlwaysFilter => true,
        OpFilterPolicy::AlwaysLeapfrog => false,
        OpFilterPolicy::Adaptive => {
            n >= OP_FILTER_MIN_RELATION.min(m.saturating_mul(OP_FILTER_RELATION_PER_CANDIDATE))
                && m <= n.saturating_mul(OP_FILTER_SEEK_COST)
        }
    };
    #[cfg(test)]
    OP_RESTRICTION_LOG.with(|l| {
        l.borrow_mut().push(if demote {
            OpRestriction::Filter
        } else {
            OpRestriction::Leapfrog
        })
    });
    demote
}

/// Turn a resolved bucket into a cursor; an absent key resolves to the empty
/// slice, hence to an empty cursor.
#[inline]
fn cursor_of<G: crate::containers::DenseId>(b: &[G]) -> SortedVecCursor<'_, G> {
    SortedVecCursor::new(b)
}

fn run_join<Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    exec: &Exec<'_, Cfg, L, S>,
    step_idx: usize,
    target: VarId,
    lookups: &[IndexLookup<Cfg::O, Cfg::Index>],
    atom_id: usize,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &mut Match<Cfg>,
    results: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if lookups.is_empty() {
        // No constraints — preserve original behavior (no match emitted).
        return;
    }
    // Every `Step::Join` the scheduler emits carries exactly one `ByOp`: it is
    // the first lookup at all eight emission sites in `schedule.rs`, and none of
    // them appends a second. The demotion below relies on that: it takes one
    // `ByOp` out of the ring and covers it with the per-candidate test, so a
    // second one would silently stay a cursor while the first became a filter,
    // which is a different split, still sound but unpriced.
    debug_assert_eq!(
        lookups
            .iter()
            .filter(|l| matches!(l, IndexLookup::ByOp { .. }))
            .count(),
        1,
        "a join's lookups must carry exactly one ByOp"
    );
    // A `ByOp` lookup in a join that has a narrower lookup too can be applied
    // two ways, and which is cheaper depends on the binding, not on the atom.
    //
    // `IndexStore::build_from` files every non-subsumed node into `by_op` and
    // into its `by_repr` / `by_child_pos` / `by_contains` buckets from one id
    // stream, so for any other bucket `B` of the same store
    // `by_op[o] ∩ B = { n ∈ B : op(n) = o }`: the intersection and the test are
    // the same set. They are not the same cost. Demoting `by_op[o]` to a test
    // costs one `op[id]` load per element of `B`, whatever the intersection
    // turns out to be. Keeping it in the leapfrog ring costs one iteration per
    // element of the *smaller* of `B` and `by_op[o]`, because a seek from either
    // side clears every key of the other side below it in one step, and each is a
    // doubling gallop plus a bisection over the two vectors. So the ring wins when
    // `by_op[o]` is small, both because it does less work and because its
    // working set stays in cache, and `|B|` and `|by_op[o]|` are `len` reads on
    // buckets the join is opening anyway (see `OP_FILTER_RELATION_PER_CANDIDATE`
    // for the measured crossover and the rule fitted to it).
    //
    // The set identity holds in each of the three modes because the delta store
    // is built by the same `build_from` over the same e-graph: a node in
    // `full.B ∖ delta.B` cannot be in the delta id stream at all (if it were,
    // the same child/class/op reads that put it in `full.B` would have put it
    // in `delta.B`), so it is not in `delta.by_op[o]` either.
    let op_pos = if lookups.len() > 1 {
        lookups
            .iter()
            .position(|l| matches!(l, IndexLookup::ByOp { .. }))
    } else {
        None
    };
    let policy = results.op_filter_policy;

    // One pass per mode: resolve the `ByOp` bucket for its length, then resolve
    // and open the other lookups while tracking the smallest of them, and put
    // the `ByOp` cursor back in the ring only if the decision keeps it. The ring
    // is sorted by key at construction, so appending it last is the same join.
    //
    // The mode is fixed for the whole atom (all its lookups read the same
    // flavor); see design doc "How a Variant Executes".
    macro_rules! dispatch {
        ($store:expr, $open:expr) => {{
            let store = $store;
            let mut m = usize::MAX;
            let mut cursors = CursorVec::new();
            for (i, l) in lookups.iter().enumerate() {
                if Some(i) == op_pos {
                    continue;
                }
                let b = bucket_in(store, index, l, eg, globals, env);
                let len = b.len();
                if len < m {
                    m = len;
                }
                cursors.push($open(b, l));
            }
            let op_bucket = op_pos.map(|p| bucket_in(store, index, &lookups[p], eg, globals, env));
            let op_filter = if demote_by_op(m, op_bucket.map(|b| b.len()), policy) {
                match &lookups[op_pos.expect("a demoted join has a ByOp lookup")] {
                    IndexLookup::ByOp { op } => Some(*op),
                    _ => unreachable!("op_pos indexes a ByOp lookup"),
                }
            } else {
                if let (Some(b), Some(p)) = (op_bucket, op_pos) {
                    cursors.push($open(b, &lookups[p]));
                }
                None
            };
            leapfrog_join(
                cursors, op_filter, exec, step_idx, target, eg, index, globals, env, results,
            );
        }};
    }

    match index.mode(atom_id) {
        IndexMode::Full => dispatch!(index.full, |b, _l| cursor_of(b)),
        IndexMode::Delta => dispatch!(index.delta, |b, _l| cursor_of(b)),
        // The candidate set is `full ∖ delta`, so the full-side length is an
        // upper bound on it and the decision reads that. A tighter estimate
        // would need the delta bucket's overlap, which is the work being priced.
        IndexMode::FullMinusDelta => dispatch!(index.full, |b, l| Difference::new(
            cursor_of(b),
            cursor_in(index.delta, index, l, eg, globals, env)
        )),
    }
}

/// Resolve one lookup's key against a single index store, returning the bucket
/// it selects (the empty slice if the key names no bucket of this build).
///
/// `store` is the slice this atom's mode reads (full or delta); `index` is the
/// round's view, consulted only for the canonicalization the buckets are keyed
/// by (see [`canon`]). Kept apart from [`cursor_of`] because `run_join` reads
/// each bucket's length before it decides which buckets become cursors, and
/// resolving twice would repeat the canonicalization and the hash probe.
fn bucket_in<'a, Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    store: &'a IndexStore<Cfg>,
    index: &VariantIndex<'_, Cfg>,
    l: &IndexLookup<Cfg::O, Cfg::Index>,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &Match<Cfg>,
) -> &'a [Cfg::G]
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    match l {
        IndexLookup::ByOp { op } => store.nodes_by_op(*op),
        IndexLookup::ByChildPos { child, pos } => {
            let r = canon(index, eg, env.resolve_pv(*child, globals));
            store.nodes_by_child_pos(r, *pos)
        }
        IndexLookup::ByRepr { repr } => {
            let r = canon(index, eg, env.get(*repr));
            store.nodes_by_repr(r)
        }
        IndexLookup::ByContains { child } => {
            let r = canon(index, eg, env.resolve_pv(*child, globals));
            store.nodes_by_contains(r)
        }
    }
}

/// [`bucket_in`] followed by [`cursor_of`], for the one caller that needs no
/// length: the delta side of a `FullMinusDelta` cursor, which is subtracted
/// rather than enumerated.
fn cursor_in<'a, Cfg, L, S: Copy, const TRACK: bool, const PROOFS: bool>(
    store: &'a IndexStore<Cfg>,
    index: &VariantIndex<'_, Cfg>,
    l: &IndexLookup<Cfg::O, Cfg::Index>,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &Match<Cfg>,
) -> SortedVecCursor<'a, Cfg::G>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    cursor_of(bucket_in(store, index, l, eg, globals, env))
}

/// Run a leapfrog intersection over `cursors` (any `SortedCursor` flavor),
/// binding `target` to each match and recursing into the next step.
///
/// `op_filter` carries the operator of a `ByOp` lookup that `run_join` left out
/// of `cursors`; a candidate whose operator differs is skipped without being
/// bound or counted as a match step (see `run_join` for why the two forms agree).
fn leapfrog_join<Cfg, L, S: Copy, C, const TRACK: bool, const PROOFS: bool>(
    cursors: CursorVec<C>,
    op_filter: Option<Cfg::O>,
    exec: &Exec<'_, Cfg, L, S>,
    step_idx: usize,
    target: VarId,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    index: &VariantIndex<'_, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &mut Match<Cfg>,
    results: &mut MatchPool<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    C: SortedCursor<Key = Cfg::G>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    // `target` may already be bound: the bound-node re-join (`ByRepr ∩ ByOp`, emitted by
    // `emit_variadic_join`/`try_schedule_bound` when a variadic atom's node was bound by an
    // upstream `ExtractChild`) has `target` already set, and an enclosing step relies on
    // that binding. Save it and restore on exit, so this join's per-key `set`/`clear` does
    // not destroy a binding a sibling iteration of an upstream join still needs. (Plain
    // unbound joins have `prev == None`, so this reduces to the old set/clear.)
    let prev = env.get_opt(target);
    let mut join = LeapfrogJoin::new(cursors);
    while join.is_valid() {
        let id = join.key();
        if op_filter.is_none_or(|o| index.full.round_op(id).unwrap_or_else(|| eg.node_op(id)) == o)
        {
            env.set(target, id);
            run_step(exec, step_idx + 1, eg, index, globals, env, results);
        }
        join.next();
    }
    env.set_opt(target, prev);
}

// ---------------------------------------------------------------------------
// MatchIterator — explicit DFS stack machine (lazy, pull-based)
// ---------------------------------------------------------------------------

/// Resolve an `IndexLookup` to a bucket slice from the **full** index (the
/// pull-based engine runs naive only — see semi-naive design notes).
/// Returns the empty slice when the lookup key names no bucket (i.e. no matches).
fn resolve_lookup<'a, Cfg: EGraphConfig, L: LitVal, S: Copy, const T: bool, const P: bool>(
    l: &IndexLookup<Cfg::O, Cfg::Index>,
    eg: &EGraph<Cfg, L, T, P>,
    index: &'a VariantIndex<'a, Cfg>,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    env: &Match<Cfg>,
) -> &'a [Cfg::G]
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    match l {
        IndexLookup::ByOp { op } => index.full.nodes_by_op(*op),
        IndexLookup::ByChildPos { child, pos } => {
            let r = canon(index, eg, env.resolve_pv(*child, globals));
            index.full.nodes_by_child_pos(r, *pos)
        }
        IndexLookup::ByRepr { repr } => {
            let r = canon(index, eg, env.get(*repr));
            index.full.nodes_by_repr(r)
        }
        IndexLookup::ByContains { child } => {
            let r = canon(index, eg, env.resolve_pv(*child, globals));
            index.full.nodes_by_contains(r)
        }
    }
}

enum FrameKind<'a, Cfg: EGraphConfig> {
    Join {
        target: VarId,
        join: LeapfrogJoin<SortedVecCursor<'a, Cfg::G>>,
    },
    SlidingWindow {
        children: Vec<PatVar>,
        pre: SeqVarId,
        suf: SeqVarId,
        seq: Vec<Cfg::G>,
        offset: usize,
        slack: usize,
    },
    ACDecompose {
        elems: Vec<(PatVar, RMult)>,
        rest: Option<MsetVarId>,
        residual: Vec<(Cfg::G, Cfg::M)>,
        ri_at: Vec<usize>,
        ei: usize,
    },
    ACIDecompose {
        elems: Vec<PatVar>,
        rest: Option<SetVarId>,
        residual: Vec<Cfg::G>,
        used: crate::containers::bitset::BitSet,
        ri_at: Vec<usize>,
        ei: usize,
    },
}

struct Frame<'a, Cfg: EGraphConfig> {
    kind: FrameKind<'a, Cfg>,
    step_idx: usize,
}

pub struct MatchIterator<'a, Cfg: EGraphConfig, L: LitVal, S: Copy, const T: bool, const P: bool> {
    plan: &'a QueryPlan<Cfg::O, Cfg::Index, L>,
    eg: &'a EGraph<Cfg, L, T, P>,
    index: &'a VariantIndex<'a, Cfg>,
    globals: &'a crate::resolve::GlobalCtx<S, Cfg::G>,
    env: Match<Cfg>,
    frames: Vec<Frame<'a, Cfg>>,
    /// Next plan step to enter (usize::MAX = must backtrack after yield).
    cursor: usize,
    done: bool,
}

impl<'a, Cfg, L, S: Copy, const T: bool, const P: bool> MatchIterator<'a, Cfg, L, S, T, P>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    pub fn new(
        plan: &'a QueryPlan<Cfg::O, Cfg::Index, L>,
        eg: &'a EGraph<Cfg, L, T, P>,
        index: &'a VariantIndex<'a, Cfg>,
        globals: &'a crate::resolve::GlobalCtx<S, Cfg::G>,
    ) -> Self {
        Self {
            plan,
            eg,
            index,
            globals,
            env: Match::new(&plan.shape),
            frames: Vec::new(),
            cursor: 0,
            done: false,
        }
    }

    pub fn env(&self) -> &Match<Cfg> {
        &self.env
    }

    /// Composable iterator that clones each match on yield.
    pub fn cloned_iter(self) -> ClonedMatchIter<'a, Cfg, L, S, T, P> {
        ClonedMatchIter { inner: self }
    }

    /// Collect all remaining matches into a `MatchSet`.
    pub fn collect_set(&mut self, shape: &crate::resolve::MatchShape) -> MatchSet<Cfg> {
        let mut set = MatchSet::new(shape);
        while self.next_match() {
            set.push(&self.env);
        }
        set
    }

    /// Advance to the next match. Returns true if found (read via `env()`).
    pub fn next_match(&mut self) -> bool {
        if self.done {
            return false;
        }

        // If we just yielded, backtrack from the end.
        if self.cursor == usize::MAX && !self.backtrack() {
            self.done = true;
            return false;
        }

        loop {
            // Complete match?
            if self.cursor >= self.plan.steps.len() {
                self.cursor = usize::MAX;
                return true;
            }

            match self.enter() {
                Enter::Advanced => continue,
                Enter::Failed => {
                    if !self.backtrack() {
                        self.done = true;
                        return false;
                    }
                }
                Enter::Pushed(true) => {
                    self.cursor += 1;
                    continue;
                }
                Enter::Pushed(false) => {
                    self.frames.pop();
                    if !self.backtrack() {
                        self.done = true;
                        return false;
                    }
                }
            }
        }
    }

    /// Try to enter `plan.steps[self.cursor]`.
    fn enter(&mut self) -> Enter {
        match &self.plan.steps[self.cursor] {
            Step::ExtractChild {
                target,
                parent,
                pos,
            } => {
                let child = self.eg.child_at(self.env.get(*parent), *pos);
                self.env.set(*target, child);
                self.cursor += 1;
                Enter::Advanced
            }
            Step::CheckChildEq {
                parent,
                pos,
                expected,
            } => {
                let child = self.eg.child_at(self.env.get(*parent), *pos);
                if canon(self.index, self.eg, child)
                    == canon(
                        self.index,
                        self.eg,
                        self.env.resolve_pv(*expected, self.globals),
                    )
                {
                    self.cursor += 1;
                    Enter::Advanced
                } else {
                    Enter::Failed
                }
            }
            Step::CheckEq { a, b } => {
                if canon(self.index, self.eg, self.env.get(*a))
                    == canon(self.index, self.eg, self.env.get(*b))
                {
                    self.cursor += 1;
                    Enter::Advanced
                } else {
                    Enter::Failed
                }
            }
            Step::CheckEqGlobal { local, global } => {
                if canon(self.index, self.eg, self.env.get(*local))
                    == canon(self.index, self.eg, self.globals.binding(*global))
                {
                    self.cursor += 1;
                    Enter::Advanced
                } else {
                    Enter::Failed
                }
            }
            Step::CopyBinding { target, other } => {
                self.env
                    .set(*target, canon(self.index, self.eg, self.env.get(*other)));
                self.cursor += 1;
                Enter::Advanced
            }
            Step::Join {
                target, lookups, ..
            } => {
                let target = *target;
                let lookups = lookups.clone();
                self.enter_join(target, &lookups)
            }
            Step::ExpandA {
                node,
                children,
                pre,
                suf,
            } => {
                let node_id = self.env.get(*node);
                let mut seq = Vec::new();
                self.eg.seq_children(node_id, &mut seq);
                let children = children.clone();
                let pre = *pre;
                let suf = *suf;
                self.enter_expand_a(&children, pre, suf, seq)
            }
            Step::DecomposeAC {
                node, elems, rest, ..
            } => {
                let node_id = self.env.get(*node);
                let mut residual = Vec::new();
                self.eg.mset_children(node_id, &mut residual);
                for e in &mut residual {
                    e.0 = canon(self.index, self.eg, e.0);
                }
                let elems = elems.clone();
                let rest = *rest;
                self.enter_ac(&elems, rest, residual)
            }
            Step::DecomposeACI { node, elems, rest } => {
                let node_id = self.env.get(*node);
                let mut residual = Vec::new();
                self.eg.set_children(node_id, &mut residual);
                for e in &mut residual {
                    *e = canon(self.index, self.eg, *e);
                }
                let elems = elems.clone();
                let rest = *rest;
                self.enter_aci(&elems, rest, residual)
            }
            Step::ExtractLitVal { node, val } => {
                let node_id = self.env.get(*node);
                if let Some(lit_val_id) = self.eg.get_lit_val_id(node_id) {
                    self.env.set_lit_val(*val, lit_val_id);
                    self.cursor += 1;
                    Enter::Advanced
                } else {
                    Enter::Failed
                }
            }
            Step::CheckLit { node, value } => {
                let node_id = self.env.get(*node);
                if self.eg.get_lit_val(node_id) == Some(value) {
                    self.cursor += 1;
                    Enter::Advanced
                } else {
                    Enter::Failed
                }
            }
        }
    }

    fn enter_join(&mut self, target: VarId, lookups: &[IndexLookup<Cfg::O, Cfg::Index>]) -> Enter {
        // Collected straight into cursors: `resolve_lookup` borrows from the
        // index's pool, which outlives the frame, so there is no intermediate
        // vector of bucket references. An empty bucket short-circuits the whole
        // join, as the absent key it stands for did before the families became
        // dense: the intersection is empty either way, and failing here keeps
        // the frame off the stack.
        let mut iters: CursorVec<SortedVecCursor<'a, Cfg::G>> = CursorVec::new();
        for l in lookups {
            let b = resolve_lookup(l, self.eg, self.index, self.globals, &self.env);
            if b.is_empty() {
                return Enter::Failed;
            }
            iters.push(SortedVecCursor::new(b));
        }
        if iters.is_empty() {
            return Enter::Failed;
        }
        let join = LeapfrogJoin::new(iters);
        let valid = join.is_valid();
        if valid {
            self.env.set(target, join.key());
        }
        self.frames.push(Frame {
            kind: FrameKind::Join { target, join },
            step_idx: self.cursor,
        });
        Enter::Pushed(valid)
    }

    fn enter_expand_a(
        &mut self,
        children: &[PatVar],
        pre: Option<SeqVarId>,
        suf: Option<SeqVarId>,
        seq: Vec<Cfg::G>,
    ) -> Enter {
        let nfixed = children.len();
        match (pre, suf) {
            (Some(p), Some(s)) => {
                if seq.len() < nfixed {
                    return Enter::Failed;
                }
                let slack = seq.len() - nfixed;
                // Bind offset 0.
                self.env.push_seq(p, &seq[..0]);
                self.env.push_seq(s, &seq[nfixed..]);
                let valid = self.bind_fixed(children, &seq, 0);
                if !valid {
                    self.env.pop_seq(s);
                    self.env.pop_seq(p);
                }
                self.frames.push(Frame {
                    kind: FrameKind::SlidingWindow {
                        children: children.to_vec(),
                        pre: p,
                        suf: s,
                        seq,
                        offset: 0,
                        slack,
                    },
                    step_idx: self.cursor,
                });
                Enter::Pushed(valid)
            }
            _ => {
                // Single-shot cases: no generator needed.
                if pre.is_none() && suf.is_none() {
                    if seq.len() != nfixed {
                        return Enter::Failed;
                    }
                    if !self.bind_fixed(children, &seq, 0) {
                        return Enter::Failed;
                    }
                    self.cursor += 1;
                    Enter::Advanced
                } else if let (Some(p), None) = (pre, suf) {
                    if seq.len() < nfixed {
                        return Enter::Failed;
                    }
                    let split = seq.len() - nfixed;
                    self.env.push_seq(p, &seq[..split]);
                    if !self.bind_fixed(children, &seq, split) {
                        self.env.pop_seq(p);
                        return Enter::Failed;
                    }
                    self.cursor += 1;
                    Enter::Advanced
                } else {
                    // (None, Some(s))
                    let s = suf.unwrap();
                    if seq.len() < nfixed {
                        return Enter::Failed;
                    }
                    self.env.push_seq(s, &seq[nfixed..]);
                    if !self.bind_fixed(children, &seq, 0) {
                        self.env.pop_seq(s);
                        return Enter::Failed;
                    }
                    self.cursor += 1;
                    Enter::Advanced
                }
            }
        }
    }

    fn enter_ac(
        &mut self,
        elems: &[(PatVar, RMult)],
        rest: Option<MsetVarId>,
        mut residual: Vec<(Cfg::G, Cfg::M)>,
    ) -> Enter {
        if elems.is_empty() {
            let zero = Cfg::M::ZERO;
            if let Some(rv) = rest {
                let rem: Vec<Cfg::C> = residual
                    .iter()
                    .filter(|&&(_, m)| m > zero)
                    .map(|&(g, m)| Cfg::mset_child_with_mult(g, m))
                    .collect();
                self.env.push_mset(rv, &rem);
                self.cursor += 1;
                return Enter::Advanced;
            } else if residual.iter().all(|&(_, m)| m == zero) {
                self.cursor += 1;
                return Enter::Advanced;
            } else {
                return Enter::Failed;
            }
        }
        let mut ri_at = vec![0usize; elems.len()];
        let valid = self.ac_find_first(elems, &mut residual, &mut ri_at, 0);
        let mut accepted = valid;
        if valid {
            if let Some(rv) = rest {
                let zero = Cfg::M::ZERO;
                let rem: Vec<Cfg::C> = residual
                    .iter()
                    .filter(|&&(_, m)| m > zero)
                    .map(|&(g, m)| Cfg::mset_child_with_mult(g, m))
                    .collect();
                self.env.push_mset(rv, &rem);
            } else {
                // Exact: all residual must be consumed.
                let zero = Cfg::M::ZERO;
                if !residual.iter().all(|&(_, m)| m == zero) {
                    accepted = false;
                }
            }
        }
        let ei = if valid { elems.len() } else { 0 };
        self.frames.push(Frame {
            kind: FrameKind::ACDecompose {
                elems: elems.to_vec(),
                rest,
                residual,
                ri_at,
                ei,
            },
            step_idx: self.cursor,
        });
        Enter::Pushed(accepted)
    }

    fn enter_aci(
        &mut self,
        elems: &[PatVar],
        rest: Option<SetVarId>,
        residual: Vec<Cfg::G>,
    ) -> Enter {
        if elems.is_empty() {
            if let Some(rv) = rest {
                self.env.push_set(rv, &residual);
                self.cursor += 1;
                return Enter::Advanced;
            } else if residual.is_empty() {
                self.cursor += 1;
                return Enter::Advanced;
            } else {
                return Enter::Failed;
            }
        }
        let mut used = crate::containers::bitset::BitSet::new(residual.len());
        let mut ri_at = vec![0usize; elems.len()];
        let valid = self.aci_find_first(elems, &residual, &mut used, &mut ri_at, 0);
        let mut accepted = valid;
        if valid {
            if let Some(rv) = rest {
                let rem: Vec<Cfg::G> = residual
                    .iter()
                    .enumerate()
                    .filter(|&(i, _)| !used.test(i))
                    .map(|(_, &g)| g)
                    .collect();
                self.env.push_set(rv, &rem);
            } else {
                // Exact: all must be used.
                if !(0..residual.len()).all(|i| used.test(i)) {
                    accepted = false;
                }
            }
        }
        let ei = if valid { elems.len() } else { 0 };
        self.frames.push(Frame {
            kind: FrameKind::ACIDecompose {
                elems: elems.to_vec(),
                rest,
                residual,
                used,
                ri_at,
                ei,
            },
            step_idx: self.cursor,
        });
        Enter::Pushed(accepted)
    }

    fn bind_fixed(&mut self, children: &[PatVar], seq: &[Cfg::G], offset: usize) -> bool {
        for (i, &cv) in children.iter().enumerate() {
            let val = seq[offset + i];
            match cv {
                PatVar::Global(gid) => {
                    if canon(self.index, self.eg, self.globals.binding(gid))
                        != canon(self.index, self.eg, val)
                    {
                        for &cv2 in &children[..i] {
                            if let PatVar::Local(v) = cv2 {
                                self.env.clear(v);
                            }
                        }
                        return false;
                    }
                }
                PatVar::Local(vid) => {
                    if let Some(existing) = self.env.nodes[vid.idx()] {
                        if canon(self.index, self.eg, existing) != canon(self.index, self.eg, val) {
                            for &cv2 in &children[..i] {
                                if let PatVar::Local(v) = cv2 {
                                    self.env.clear(v);
                                }
                            }
                            return false;
                        }
                    } else {
                        self.env.set(vid, val);
                    }
                }
            }
        }
        true
    }

    // -- Backtracking --

    fn backtrack(&mut self) -> bool {
        loop {
            let mut frame = match self.frames.pop() {
                Some(f) => f,
                None => return false,
            };
            self.cursor = frame.step_idx;

            match &mut frame.kind {
                FrameKind::Join { target, join } => {
                    self.env.clear(*target);
                    join.next();
                    if join.is_valid() {
                        self.env.set(*target, join.key());
                        self.cursor += 1;
                        self.frames.push(frame);
                        return true;
                    }
                    // exhausted, frame dropped
                }
                FrameKind::SlidingWindow {
                    children,
                    pre,
                    suf,
                    seq,
                    offset,
                    slack,
                } => {
                    for &cv in children.iter() {
                        if let PatVar::Local(v) = cv {
                            self.env.clear(v)
                        };
                    }
                    self.env.pop_seq(*suf);
                    self.env.pop_seq(*pre);
                    *offset += 1;
                    while *offset <= *slack {
                        let nfixed = children.len();
                        let o = *offset;
                        self.env.push_seq(*pre, &seq[..o]);
                        self.env.push_seq(*suf, &seq[o + nfixed..]);
                        if self.bind_fixed(children, seq, o) {
                            self.cursor += 1;
                            self.frames.push(frame);
                            return true;
                        }
                        for &cv in children.iter() {
                            if let PatVar::Local(v) = cv {
                                self.env.clear(v)
                            };
                        }
                        self.env.pop_seq(*suf);
                        self.env.pop_seq(*pre);
                        *offset += 1;
                    }
                    // exhausted
                }
                FrameKind::ACDecompose {
                    elems,
                    rest,
                    residual,
                    ri_at,
                    ei,
                } => {
                    if *ei == elems.len()
                        && let Some(rv) = *rest
                    {
                        self.env.pop_mset(rv);
                    }
                    loop {
                        if !self.ac_advance(elems, residual, ri_at, ei) {
                            break;
                        }
                        if let Some(rv) = *rest {
                            let zero = Cfg::M::ZERO;
                            let rem: Vec<Cfg::C> = residual
                                .iter()
                                .filter(|&&(_, m)| m > zero)
                                .map(|&(g, m)| Cfg::mset_child_with_mult(g, m))
                                .collect();
                            self.env.push_mset(rv, &rem);
                            self.cursor += 1;
                            self.frames.push(frame);
                            return true;
                        } else {
                            let zero = Cfg::M::ZERO;
                            if residual.iter().all(|&(_, m)| m == zero) {
                                self.cursor += 1;
                                self.frames.push(frame);
                                return true;
                            }
                            // Not exact — keep advancing.
                        }
                    }
                    // exhausted
                }
                FrameKind::ACIDecompose {
                    elems,
                    rest,
                    residual,
                    used,
                    ri_at,
                    ei,
                } => {
                    if *ei == elems.len()
                        && let Some(rv) = *rest
                    {
                        self.env.pop_set(rv);
                    }
                    loop {
                        if !self.aci_advance(elems, residual, used, ri_at, ei) {
                            break;
                        }
                        if let Some(rv) = *rest {
                            let rem: Vec<Cfg::G> = residual
                                .iter()
                                .enumerate()
                                .filter(|&(i, _)| !used.test(i))
                                .map(|(_, &g)| g)
                                .collect();
                            self.env.push_set(rv, &rem);
                            self.cursor += 1;
                            self.frames.push(frame);
                            return true;
                        } else if (0..residual.len()).all(|i| used.test(i)) {
                            self.cursor += 1;
                            self.frames.push(frame);
                            return true;
                        }
                    }
                    // exhausted
                }
            }
        }
    }

    // -- AC helpers --

    fn ac_find_first(
        &mut self,
        elems: &[(PatVar, RMult)],
        residual: &mut [(Cfg::G, Cfg::M)],
        ri_at: &mut [usize],
        from: usize,
    ) -> bool {
        let mut ei = from;
        while ei < elems.len() {
            let start = if ei == from { ri_at[ei] } else { 0 };
            match self.ac_scan(elems, residual, ei, start) {
                Some(ri) => {
                    ri_at[ei] = ri;
                    ei += 1;
                }
                None => {
                    ri_at[ei] = 0;
                    if ei == 0 {
                        return false;
                    }
                    ei -= 1;
                    self.ac_undo(elems, residual, ei, ri_at[ei]);
                    ri_at[ei] += 1;
                }
            }
        }
        true
    }

    fn ac_scan(
        &mut self,
        elems: &[(PatVar, RMult)],
        residual: &mut [(Cfg::G, Cfg::M)],
        ei: usize,
        start: usize,
    ) -> Option<usize> {
        let (var, mult) = &elems[ei];

        let bound_repr = match *var {
            PatVar::Global(gid) => Some(canon(self.index, self.eg, self.globals.binding(gid))),
            PatVar::Local(vid) => self.env.nodes[vid.idx()].map(|v| canon(self.index, self.eg, v)),
        };

        if let Some(repr) = bound_repr {
            for ri in start..residual.len() {
                if residual[ri].0 == repr
                    && mult_matches(
                        mult,
                        residual[ri].1.to_u64(),
                        bound_mult_val(mult, &self.env),
                    )
                {
                    let take: Cfg::M = match mult {
                        // Matched at the surface width, so the literal equals
                        // this entry's multiplicity; reuse it.
                        RMult::Exact(_) => residual[ri].1,
                        RMult::Var { var: mv, .. } => {
                            self.env.set_mult(*mv, residual[ri].1);
                            residual[ri].1
                        }
                    };
                    residual[ri].1 = residual[ri].1.saturating_sub(take);
                    return Some(ri);
                }
            }
            return None;
        }

        for ri in start..residual.len() {
            let (repr, avail) = residual[ri];
            if !mult_matches(mult, avail.to_u64(), bound_mult_val(mult, &self.env)) {
                continue;
            }
            let PatVar::Local(vid) = *var else {
                unreachable!()
            };
            self.env.set(vid, repr);
            let take: Cfg::M = match mult {
                // See the bound-repr path above.
                RMult::Exact(_) => avail,
                RMult::Var { var: mv, .. } => {
                    self.env.set_mult(*mv, avail);
                    avail
                }
            };
            residual[ri].1 = avail.saturating_sub(take);
            return Some(ri);
        }
        None
    }

    fn ac_undo(
        &mut self,
        elems: &[(PatVar, RMult)],
        residual: &mut [(Cfg::G, Cfg::M)],
        ei: usize,
        ri: usize,
    ) {
        let (var, mult) = &elems[ei];
        let restore: Cfg::M = match mult {
            // `ac_scan` only took this entry because the literal equalled its
            // stored multiplicity, so the literal is representable at the
            // configured width.
            RMult::Exact(n) => Cfg::M::try_from_u64(*n)
                .expect("Exact multiplicity matched a stored one, so it fits the configured width"),
            RMult::Var { var: mv, .. } => self.env.get_mult(*mv),
        };
        // Summation is checked: this undoes a subtraction `ac_scan` performed on
        // the same entry, so the sum cannot exceed the width — but a wrap here
        // would silently forge a multiplicity (possibly zero) and corrupt the
        // residual multiset rather than fail a match.
        residual[ri].1 = residual[ri].1.checked_add(restore).expect(
            "ac_undo restores a multiplicity previously subtracted from this entry, so the sum fits",
        );
        if let PatVar::Local(vid) = *var {
            self.env.clear(vid);
        }
        if let RMult::Var { var: mv, .. } = mult {
            // Only clear if no earlier element uses the same mult variable
            let earlier_uses = elems[..ei]
                .iter()
                .any(|(_, m)| matches!(m, RMult::Var { var: v, .. } if *v == *mv));
            if !earlier_uses {
                self.env.set_mult(*mv, Cfg::M::ZERO);
            }
        }
    }

    fn ac_advance(
        &mut self,
        elems: &[(PatVar, RMult)],
        residual: &mut [(Cfg::G, Cfg::M)],
        ri_at: &mut [usize],
        ei: &mut usize,
    ) -> bool {
        if elems.is_empty() || *ei != elems.len() {
            return false;
        }
        // Undo last element, try next residual entry. If exhausted, undo previous, etc.
        let mut e = elems.len() - 1;
        loop {
            self.ac_undo(elems, residual, e, ri_at[e]);
            ri_at[e] += 1;
            // Try to find a valid entry for element e and all subsequent elements.
            // ac_scan only looks at element e; if it succeeds we try e+1.. from scratch.
            if let Some(ri) = self.ac_scan(elems, residual, e, ri_at[e]) {
                ri_at[e] = ri;
                // Now try to bind e+1..end from scratch.
                let mut ok = true;
                for e2 in (e + 1)..elems.len() {
                    ri_at[e2] = 0;
                    match self.ac_scan(elems, residual, e2, 0) {
                        Some(ri2) => ri_at[e2] = ri2,
                        None => {
                            // Undo e2-1..=e+1 that we just bound, then undo e and try next.
                            for undo in (e + 1..e2).rev() {
                                self.ac_undo(elems, residual, undo, ri_at[undo]);
                            }
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    *ei = elems.len();
                    return true;
                }
                // ac_scan for e succeeded but downstream failed. Undo e and try next ri.
                self.ac_undo(elems, residual, e, ri_at[e]);
                ri_at[e] += 1;
                continue;
            }
            // No more entries for element e. Backtrack to e-1.
            ri_at[e] = 0;
            if e == 0 {
                *ei = 0;
                return false;
            }
            e -= 1;
        }
    }

    // -- ACI helpers --

    fn aci_find_first(
        &mut self,
        elems: &[PatVar],
        residual: &[Cfg::G],
        used: &mut crate::containers::bitset::BitSet,
        ri_at: &mut [usize],
        from: usize,
    ) -> bool {
        let mut ei = from;
        while ei < elems.len() {
            let start = if ei == from { ri_at[ei] } else { 0 };
            match self.aci_scan(elems, residual, used, ei, start) {
                Some(ri) => {
                    ri_at[ei] = ri;
                    ei += 1;
                }
                None => {
                    ri_at[ei] = 0;
                    if ei == 0 {
                        return false;
                    }
                    ei -= 1;
                    self.aci_undo(elems, used, ei, ri_at[ei]);
                    ri_at[ei] += 1;
                }
            }
        }
        true
    }

    fn aci_scan(
        &mut self,
        elems: &[PatVar],
        residual: &[Cfg::G],
        used: &mut crate::containers::bitset::BitSet,
        ei: usize,
        start: usize,
    ) -> Option<usize> {
        let var = elems[ei];
        let bound_repr = match var {
            PatVar::Global(gid) => Some(canon(self.index, self.eg, self.globals.binding(gid))),
            PatVar::Local(vid) => self.env.nodes[vid.idx()].map(|v| canon(self.index, self.eg, v)),
        };
        if let Some(repr) = bound_repr {
            for ri in start..residual.len() {
                if !used.test(ri) && residual[ri] == repr {
                    used.set(ri);
                    return Some(ri);
                }
            }
            return None;
        }
        let PatVar::Local(vid) = var else {
            unreachable!()
        };
        for ri in start..residual.len() {
            if used.test(ri) {
                continue;
            }
            self.env.set(vid, residual[ri]);
            used.set(ri);
            return Some(ri);
        }
        None
    }

    fn aci_undo(
        &mut self,
        elems: &[PatVar],
        used: &mut crate::containers::bitset::BitSet,
        ei: usize,
        ri: usize,
    ) {
        used.clear(ri);
        if let PatVar::Local(vid) = elems[ei] {
            self.env.clear(vid);
        }
    }

    fn aci_advance(
        &mut self,
        elems: &[PatVar],
        residual: &[Cfg::G],
        used: &mut crate::containers::bitset::BitSet,
        ri_at: &mut [usize],
        ei: &mut usize,
    ) -> bool {
        if elems.is_empty() || *ei != elems.len() {
            return false;
        }
        let mut e = elems.len() - 1;
        loop {
            self.aci_undo(elems, used, e, ri_at[e]);
            ri_at[e] += 1;
            if let Some(ri) = self.aci_scan(elems, residual, used, e, ri_at[e]) {
                ri_at[e] = ri;
                let mut ok = true;
                for e2 in (e + 1)..elems.len() {
                    ri_at[e2] = 0;
                    match self.aci_scan(elems, residual, used, e2, 0) {
                        Some(ri2) => ri_at[e2] = ri2,
                        None => {
                            for undo in (e + 1..e2).rev() {
                                self.aci_undo(elems, used, undo, ri_at[undo]);
                            }
                            ok = false;
                            break;
                        }
                    }
                }
                if ok {
                    *ei = elems.len();
                    return true;
                }
                self.aci_undo(elems, used, e, ri_at[e]);
                ri_at[e] += 1;
                continue;
            }
            ri_at[e] = 0;
            if e == 0 {
                *ei = 0;
                return false;
            }
            e -= 1;
        }
    }
}

enum Enter {
    Advanced,
    Failed,
    Pushed(bool),
}

/// Convenience: collect all matches using the iterator.
pub fn run_query_iter<Cfg, L, const T: bool, const P: bool>(
    plan: &QueryPlan<Cfg::O, Cfg::Index, L>,
    eg: &EGraph<Cfg, L, T, P>,
    index: &VariantIndex<'_, Cfg>,
) -> Vec<Match<Cfg>>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let empty: crate::resolve::GlobalCtx<(), Cfg::G> = crate::resolve::GlobalCtx::new();
    let mut it = MatchIterator::new(plan, eg, index, &empty);
    let mut out = Vec::new();
    while it.next_match() {
        out.push(it.env().clone());
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{ENodeId, OpId, SortId};
    use crate::literal::{NiraLitVal, NiraModel};
    use crate::nodes::DefaultConfig;
    use crate::registry::{OpRegistry, SortRegistry};
    use crate::resolve::MatchShape;
    use crate::resolve::resolve;
    use crate::schedule::schedule;
    use crate::sortcheck::flatten_surface as flatten;
    use crate::test_helpers::parse_pattern;

    type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;

    fn make_eg() -> EG {
        let mut eg = EG::from_model(&NiraModel);
        let e = eg.intern_sort("IExpr");
        eg.register_op2("f", e, e, e);
        eg.register_op1("g", e, e);
        eg.register_op2("h", e, e, e);
        eg.register_op0("a", e);
        eg.register_op0("b", e);
        eg.register_op0("c", e);
        eg.register_a("concat", e, e, crate::registry::AssocDir::Right);
        eg.register_mset("add", e, e);
        eg.register_set("union", e, e);
        eg
    }

    fn query<const TRACK: bool>(
        eg: &EGraph<DefaultConfig, NiraLitVal, TRACK, false>,
        ops: &OpRegistry<OpId, SortId, TRACK>,
        sorts: &SortRegistry<SortId, TRACK>,
        srcs: &[&str],
    ) -> Vec<Match<DefaultConfig>> {
        let model = NiraModel;
        let pats: Vec<_> = srcs.iter().map(|s| parse_pattern(s)).collect();
        let fq = flatten(&pats, ops).unwrap();
        let rq = resolve(
            &fq,
            ops,
            sorts,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let plan = schedule(&rq);
        let index = IndexStore::build(eg);
        let index = VariantIndex::naive(&index);
        run_query(
            &plan,
            eg,
            &index,
            &crate::resolve::GlobalCtx::<(), _>::new(),
        )
    }

    #[test]
    fn empty_egraph_no_matches() {
        let eg = make_eg();
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(f x y)"]);
        assert!(matches.is_empty());
    }

    /// A pool reused across queries yields the same matches as a fresh one.
    ///
    /// This is the property the pool's recycled storage could break and nothing
    /// else would catch: the match slots and the decompose child buffers both
    /// survive `clear()`, so a query that reads a buffer before filling it, or
    /// reads a match slot past `len`, would see the *previous* query's data.
    /// Every pattern shape that owns recycled storage is driven twice, in an
    /// order that guarantees each second run inherits a non-empty pool.
    #[test]
    fn reused_pool_matches_a_fresh_pool() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b, c]);
        eg.add(eg.ops().id_by_name("union").unwrap(), &[a, b, c]);
        eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);
        eg.rebuild();

        // ExpandA (`concat`), DecomposeAC (`add`), DecomposeACI (`union`) and a
        // plain join — one per recycled-storage kind.
        let shapes = [
            "(f x y)",
            "(add x:1 ..rest)",
            "(union x ..rest)",
            "(concat x y ..rest)",
        ];

        let index = IndexStore::build(&eg);
        let index = VariantIndex::naive(&index);
        let ng = crate::resolve::GlobalCtx::<(), _>::new();

        let plans: Vec<_> = shapes
            .iter()
            .map(|src| {
                let pats = [parse_pattern(src)];
                let fq = flatten(&pats, eg.ops()).unwrap();
                let rq = resolve(
                    &fq,
                    eg.ops(),
                    eg.sorts(),
                    &NiraModel,
                    &crate::resolve::GlobalCtx::<_, ()>::new(),
                )
                .unwrap();
                schedule(&rq)
            })
            .collect();

        let mut shared = MatchPool::new();
        // Two passes, so the second sees a pool warmed by all four shapes.
        for _ in 0..2 {
            for plan in &plans {
                let mut fresh = MatchPool::new();
                run_query_into(plan, &eg, &index, &ng, &mut fresh);
                run_query_into(plan, &eg, &index, &ng, &mut shared);

                assert_eq!(shared.len(), fresh.len(), "match count diverged");
                let expect: Vec<_> = (0..fresh.len())
                    .map(|j| env_key(&fresh.clone_match(j), &eg))
                    .collect();
                let got: Vec<_> = (0..shared.len())
                    .map(|j| env_key(&shared.clone_match(j), &eg))
                    .collect();
                assert_eq!(got, expect, "reused pool produced different bindings");
            }
        }
    }

    #[test]
    fn single_node_match() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _f = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(f x y)"]);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn two_f_nodes() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _f1 = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        let _f2 = eg.add(eg.ops().id_by_name("f").unwrap(), &[b, a]);
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(f x y)"]);
        assert_eq!(matches.len(), 2);
    }

    #[test]
    fn nested_pattern() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let g_a = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        let _f = eg.add(eg.ops().id_by_name("f").unwrap(), &[b, g_a]);
        // (f x (g y)) should match
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(f x (g y))"]);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn nested_no_match() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _f = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        // (f x (g y)) should NOT match — second child is b, not a g-node
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(f x (g y))"]);
        assert!(matches.is_empty());
    }

    #[test]
    fn nonlinear_match() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let _f = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, a]);
        // (f x x) — same var both positions
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(f x x)"]);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn nonlinear_no_match() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _f = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        // (f x x) — a != b, should not match
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(f x x)"]);
        assert!(matches.is_empty());
    }

    #[test]
    fn multi_pattern() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _f = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        let _g = eg.add(eg.ops().id_by_name("g").unwrap(), &[b]);
        // (f x y), (g y) — y shared, b must appear in both
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(f x y)", "(g y)"]);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn multi_pattern_no_match() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _f = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        let _g = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]); // g(a), not g(b)
        // (f x y), (g y) — y=b from f, but g(b) doesn't exist
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(f x y)", "(g y)"]);
        assert!(matches.is_empty());
    }

    #[test]
    fn binding_values_correct() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _f = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);

        let model = NiraModel;
        let pat = parse_pattern("(f x y)");
        let fq = flatten(&[pat], eg.ops()).unwrap();
        let rq = resolve(
            &fq,
            eg.ops(),
            eg.sorts(),
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let plan = schedule(&rq);
        let index = IndexStore::build(&eg);
        let index = VariantIndex::naive(&index);
        let matches = run_query(
            &plan,
            &eg,
            &index,
            &crate::resolve::GlobalCtx::<(), _>::new(),
        );

        assert_eq!(matches.len(), 1);
        let x = rq.shape.find_var("x").unwrap();
        let y = rq.shape.find_var("y").unwrap();
        assert_eq!(eg.find_const(matches[0].get(x)), eg.find_const(a));
        assert_eq!(eg.find_const(matches[0].get(y)), eg.find_const(b));
    }

    #[test]
    fn deep_nesting() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let g_a = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        let g_g_a = eg.add(eg.ops().id_by_name("g").unwrap(), &[g_a]);
        let _f = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, g_g_a]);
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(f x (g (g y)))"]);
        assert_eq!(matches.len(), 1);
    }

    // -- AC matching --

    #[test]
    fn ac_exact_match() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _add = eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b]);
        // {x:1 y:1} exact — should match, binding x and y to a,b in some order
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(add x:1 y:1)"]);
        assert_eq!(matches.len(), 2); // x=a,y=b and x=b,y=a
    }

    #[test]
    fn ac_exact_no_match_extra() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let _add = eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b, c]);
        // {x:1 y:1} exact — 3 elements, only 2 pattern vars → no match
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(add x:1 y:1)"]);
        assert!(matches.is_empty());
    }

    #[test]
    fn ac_subset_match() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let _add = eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b, c]);
        // {x:1 ..rest} — should match 3 times (x=a, x=b, x=c)
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(add x:1 ..rest)"]);
        assert_eq!(matches.len(), 3);
    }

    #[test]
    fn ac_mult_exact() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        // add(a, a, a) → AC node {a:3}
        let _add = eg.add(eg.ops().id_by_name("add").unwrap(), &[a, a, a]);
        // {x:2 ..rest} — x:2 means multiplicity must be exactly 2. a has 3 → no match.
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(add x:2 ..rest)"]);
        assert_eq!(matches.len(), 0);
        // {x:3 ..rest} — a has exactly 3 → match
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(add x:3 ..rest)"]);
        assert_eq!(matches.len(), 1);
        // {x:k>=2 ..rest} — a has 3 >= 2 → match, k=3
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(add x:k>=2 ..rest)"]);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn ac_mult_exact_no_match() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        // add(a) → AC node {a:1}
        let _add = eg.add(eg.ops().id_by_name("add").unwrap(), &[a]);
        // {x:2 ..rest} — need mult ≥ 2, only have 1
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(add x:2 ..rest)"]);
        assert!(matches.is_empty());
    }

    // -- A (sequence) matching --

    #[test]
    fn a_exact_match() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _cat = eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b]);
        // [x y] exact
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(concat x y)"]);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn a_exact_wrong_length() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let _cat = eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);
        // [x y] exact — 3 children, 2 vars → no match
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(concat x y)"]);
        assert!(matches.is_empty());
    }

    #[test]
    fn a_prefix_match() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let _cat = eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);
        // [..pre x] — x = last element (c), pre = [a, b]
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(concat ..pre x)"]);
        assert_eq!(matches.len(), 1);
    }

    #[test]
    fn a_sliding_window() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let _cat = eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);
        // [..pre x ..suf] — x slides over a, b, c → 3 matches
        let matches = query(&eg, eg.ops(), eg.sorts(), &["(concat ..pre x ..suf)"]);
        assert_eq!(matches.len(), 3);
    }

    fn query_named<const TRACK: bool>(
        eg: &EGraph<DefaultConfig, NiraLitVal, TRACK, false>,
        ops: &OpRegistry<OpId, SortId, TRACK>,
        sorts: &SortRegistry<SortId, TRACK>,
        srcs: &[&str],
    ) -> (Vec<Match<DefaultConfig>>, MatchShape) {
        let model = NiraModel;
        let pats: Vec<_> = srcs.iter().map(|s| parse_pattern(s)).collect();
        let fq = flatten(&pats, ops).unwrap();
        let rq = resolve(
            &fq,
            ops,
            sorts,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let plan = schedule(&rq);
        let index = IndexStore::build(eg);
        let index = VariantIndex::naive(&index);
        (
            run_query(
                &plan,
                eg,
                &index,
                &crate::resolve::GlobalCtx::<(), _>::new(),
            ),
            rq.shape,
        )
    }

    /// Extract (var_name → node_op_name) map from a binding, filtering out internal vars.
    fn binding_map<const TRACK: bool>(
        m: &Match<DefaultConfig>,
        vars: &MatchShape,
        eg: &EGraph<DefaultConfig, NiraLitVal, TRACK, false>,
    ) -> Vec<(String, String)> {
        vars.nodes
            .iter()
            .enumerate()
            .filter(|(_, name)| !name.starts_with('#')) // skip internal vars
            .filter_map(|(vi, name)| {
                m.nodes[vi].map(|g| (name.clone(), eg.node_op_name(g).to_string()))
            })
            .collect()
    }

    fn has_binding<const TRACK: bool>(
        matches: &[Match<DefaultConfig>],
        vars: &MatchShape,
        eg: &EGraph<DefaultConfig, NiraLitVal, TRACK, false>,
        expected: &[(&str, &str)],
    ) -> bool {
        matches.iter().any(|m| {
            let bm = binding_map(m, vars, eg);
            expected
                .iter()
                .all(|&(var, op)| bm.iter().any(|(v, o)| v == var && o == op))
        })
    }

    #[test]
    fn verify_plain_f_x_y() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let g_a = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        eg.add(eg.ops().id_by_name("f").unwrap(), &[b, g_a]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(f x y)"]);
        assert_eq!(matches.len(), 2);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "a"), ("y", "b")]));
        assert!(has_binding(&matches, &vars, &eg, &[("x", "b"), ("y", "g")]));
    }

    #[test]
    fn verify_nested_f_x_g_y() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let g_a = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        eg.add(eg.ops().id_by_name("f").unwrap(), &[b, g_a]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(f x (g y))"]);
        assert_eq!(matches.len(), 1);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "b"), ("y", "a")]));
    }

    #[test]
    fn verify_ac_subset() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b, c]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(add x:1 ..rest)"]);
        assert_eq!(matches.len(), 3);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "a")]));
        assert!(has_binding(&matches, &vars, &eg, &[("x", "b")]));
        assert!(has_binding(&matches, &vars, &eg, &[("x", "c")]));
    }

    #[test]
    fn verify_ac_exact_two_of_three() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(add x:1 y:1)"]);
        assert_eq!(matches.len(), 2);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "a"), ("y", "b")]));
        assert!(has_binding(&matches, &vars, &eg, &[("x", "b"), ("y", "a")]));
    }

    #[test]
    fn verify_ac_mult() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        // add(a, a, a, b) → {a:3, b:1}
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, a, a, b]);

        // x:2 means exactly 2. a has 3, b has 1 → no match.
        let (matches, _vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(add x:2 ..rest)"]);
        assert_eq!(matches.len(), 0);

        // x:k>=2 means at least 2. a has 3 → match.
        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(add x:k>=2 ..rest)"]);
        assert_eq!(matches.len(), 1);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "a")]));
    }

    #[test]
    fn verify_a_exact() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(concat x y z)"]);
        assert_eq!(matches.len(), 1);
        assert!(has_binding(
            &matches,
            &vars,
            &eg,
            &[("x", "a"), ("y", "b"), ("z", "c")]
        ));
    }

    #[test]
    fn verify_a_sliding_window() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(concat ..pre x ..suf)"]);
        assert_eq!(matches.len(), 3);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "a")]));
        assert!(has_binding(&matches, &vars, &eg, &[("x", "b")]));
        assert!(has_binding(&matches, &vars, &eg, &[("x", "c")]));
    }

    #[test]
    fn verify_a_suffix() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);

        // [x y ..suf] — x=a, y=b, suf=rest
        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(concat x y ..suf)"]);
        assert_eq!(matches.len(), 1);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "a"), ("y", "b")]));
    }

    #[test]
    fn verify_multi_pattern_bindings() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        eg.add(eg.ops().id_by_name("g").unwrap(), &[b]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(f x y)", "(g y)"]);
        assert_eq!(matches.len(), 1);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "a"), ("y", "b")]));
    }

    /// Run a query, print the e-graph contents, pattern, and all matches with bindings.
    /// Then assert exact match count and check each expected binding is present.
    fn fmt_match<const TRACK: bool>(
        m: &Match<DefaultConfig>,
        vars: &MatchShape,
        eg: &EGraph<DefaultConfig, NiraLitVal, TRACK, false>,
        shape: &crate::resolve::MatchShape,
    ) -> String {
        let mut parts = Vec::new();
        // Node vars
        for (vi, name) in vars.nodes.iter().enumerate() {
            if name.starts_with('#') {
                continue;
            }
            if let Some(g) = m.nodes[vi] {
                parts.push(format!("{}={}", name, eg.node_op_name(g)));
            }
        }
        // Seq rests
        for i in 0..shape.num_seq_vars() {
            let s = m.seq_slice(SeqVarId(i as u16));
            let elems: Vec<&str> = s.iter().map(|&g| eg.node_op_name(g)).collect();
            parts.push(format!("seq{}=[{}]", i, elems.join(", ")));
        }
        // Set rests
        for i in 0..shape.num_set_vars() {
            let s = m.set_slice(SetVarId(i as u16));
            let elems: Vec<&str> = s.iter().map(|&g| eg.node_op_name(g)).collect();
            parts.push(format!("set{}={{{}}}", i, elems.join(", ")));
        }
        // Mset rests
        for i in 0..shape.num_mset_vars() {
            let s = m.mset_slice(MsetVarId(i as u16));
            let elems: Vec<String> = s
                .iter()
                .map(|c| {
                    format!(
                        "{}:{}",
                        eg.node_op_name(DefaultConfig::mset_child_id(c)),
                        DefaultConfig::mset_child_mult(c)
                    )
                })
                .collect();
            parts.push(format!("mset{}={{{}}}", i, elems.join(", ")));
        }
        // Mult vars
        for i in 0..shape.num_mult_vars() {
            parts.push(format!("mult{}={}", i, m.mults[i]));
        }
        parts.join(", ")
    }

    fn check<const TRACK: bool>(
        eg: &EGraph<DefaultConfig, NiraLitVal, TRACK, false>,
        ops: &OpRegistry<OpId, SortId, TRACK>,
        sorts: &SortRegistry<SortId, TRACK>,
        label: &str,
        srcs: &[&str],
        expected_count: usize,
        expected: &[&[(&str, &str)]],
    ) {
        let model = NiraModel;
        let pats: Vec<_> = srcs.iter().map(|s| parse_pattern(s)).collect();
        let fq = flatten(&pats, ops).unwrap();
        let rq = resolve(
            &fq,
            ops,
            sorts,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let plan = schedule(&rq);
        let index = IndexStore::build(eg);
        let index = VariantIndex::naive(&index);
        let matches = run_query(
            &plan,
            eg,
            &index,
            &crate::resolve::GlobalCtx::<(), _>::new(),
        );

        println!("\n--- {label} ---");
        println!("  pattern: {}", srcs.join(" , "));
        println!("{} got match(es):", matches.len());
        for (i, m) in matches.iter().enumerate() {
            println!("    [{i}] {{ {} }}", fmt_match(m, &rq.shape, eg, &rq.shape));
        }
        assert_eq!(matches.len(), expected_count, "{label}: wrong match count");
        for (ei, exp) in expected.iter().enumerate() {
            assert!(
                has_binding(&matches, &rq.shape, eg, exp),
                "{label}: expected binding [{ei}] {:?} not found",
                exp
            );
        }
    }

    // ===================================================================
    // AC (multiset) comprehensive tests
    // ===================================================================

    #[test]
    fn ac_comprehensive() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);

        // add(a,b) → {a:1, b:1}
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b]);
        println!("\n=== AC node: add(a,b) = a:1, b:1 ===");

        // Exact 2 vars, 2 elems
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "AC exact {x:1 y:1} vs {a:1,b:1}",
            &["(add x:1 y:1)"],
            2,
            &[&[("x", "a"), ("y", "b")], &[("x", "b"), ("y", "a")]],
        );

        // Subset 1 var + rest
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "AC subset {x:1 ..rest} vs {a:1,b:1}",
            &["(add x:1 ..rest)"],
            2,
            &[&[("x", "a")], &[("x", "b")]],
        );

        // Exact 1 var, 2 elems → no match (leftover)
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "AC exact {x:1} vs {a:1,b:1}",
            &["(add x:1)"],
            0,
            &[],
        );
    }

    #[test]
    fn ac_with_multiplicities() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);

        // add(a,a,a,b,b) → {a:3, b:2}
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, a, a, b, b]);
        println!("\n=== AC node: add(a,a,a,b,b) = a:3, b:2 ===");

        // x:2 ..rest → exact mult 2. b has 2 → match. a has 3 → no.
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "AC {x:2 ..rest} vs {a:3,b:2}",
            &["(add x:2 ..rest)"],
            1,
            &[&[("x", "b")]],
        );

        // x:3 ..rest → only a
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "AC {x:3 ..rest} vs {a:3,b:2}",
            &["(add x:3 ..rest)"],
            1,
            &[&[("x", "a")]],
        );

        // x:4 ..rest → nobody has mult==4
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "AC {x:4 ..rest} vs {a:3,b:2}",
            &["(add x:4 ..rest)"],
            0,
            &[],
        );

        // x:2 y:1 ..rest → x must have mult exactly 2, y exactly 1.
        // x=b(2), y=a? a has 3≠1 → no. x=b(2), y=? no other with mult 1 → no match.
        // Actually no other child has mult 1 either. So 0 matches.
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "AC {x:2 y:1 ..rest} vs {a:3,b:2}",
            &["(add x:2 y:1 ..rest)"],
            0,
            &[],
        );

        // Exact: x:3 y:2 → a:3,b:2 consumed exactly
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "AC exact {x:3 y:2} vs {a:3,b:2}",
            &["(add x:3 y:2)"],
            1,
            &[&[("x", "a"), ("y", "b")]],
        );
    }

    // ===================================================================
    // ACI (set / idempotent) comprehensive tests
    // ===================================================================

    #[test]
    fn aci_comprehensive() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);

        // union(a,b,c,a) → {a, b, c} (idempotent, deduped)
        eg.add(eg.ops().id_by_name("union").unwrap(), &[a, b, c, a]);
        println!("\n=== ACI node: union(a,b,c,a) = a, b, c ===");

        // Exact 3 vars
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "ACI exact {x y z} vs {a,b,c}",
            &["(union x y z)"],
            6,
            &[
                &[("x", "a"), ("y", "b"), ("z", "c")],
                &[("x", "a"), ("y", "c"), ("z", "b")],
                &[("x", "b"), ("y", "a"), ("z", "c")],
                &[("x", "b"), ("y", "c"), ("z", "a")],
                &[("x", "c"), ("y", "a"), ("z", "b")],
                &[("x", "c"), ("y", "b"), ("z", "a")],
            ],
        );

        // Subset 1 var + rest
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "ACI {x ..rest} vs {a,b,c}",
            &["(union x ..rest)"],
            3,
            &[&[("x", "a")], &[("x", "b")], &[("x", "c")]],
        );

        // Subset 2 vars + rest
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "ACI {x y ..rest} vs {a,b,c}",
            &["(union x y ..rest)"],
            6,
            &[
                &[("x", "a"), ("y", "b")],
                &[("x", "a"), ("y", "c")],
                &[("x", "b"), ("y", "a")],
                &[("x", "b"), ("y", "c")],
                &[("x", "c"), ("y", "a")],
                &[("x", "c"), ("y", "b")],
            ],
        );

        // Just rest — match everything
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "ACI {..rest} vs {a,b,c}",
            &["(union ..rest)"],
            1,
            &[],
        );
    }

    #[test]
    fn aci_x_rest_printed() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let d = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);

        eg.add(eg.ops().id_by_name("union").unwrap(), &[a, b, c, d]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(union x ..rest)"]);

        println!("\n=== (union x ..rest) vs ACI node a, b, c, g(a) ===");
        println!("  {} matches:", matches.len());

        let x_var = vars.find_var("x").unwrap();
        // rest is SetVarId(0) — the first (and only) set rest variable
        let rest_id = SetVarId(0);
        for (i, m) in matches.iter().enumerate() {
            let x_name = eg.node_op_name(m.get(x_var));
            let rest_slice = m.set_slice(rest_id);
            let rest_names: Vec<&str> = rest_slice.iter().map(|&g| eg.node_op_name(g)).collect();
            println!("  [{i}] x={x_name}  rest={{{}}}", rest_names.join(", "));
            // Rest should have exactly 3 elements
            assert_eq!(rest_slice.len(), 3, "rest should have 3 elements");
        }

        assert_eq!(matches.len(), 4);
        let mut x_ops: Vec<String> = matches
            .iter()
            .map(|m| eg.node_op_name(m.get(x_var)).to_string())
            .collect();
        x_ops.sort();
        assert_eq!(x_ops, ["a", "b", "c", "g"]);
    }

    // ===================================================================
    // A (sequence) comprehensive tests
    // ===================================================================

    #[test]
    fn a_comprehensive() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);

        // concat(a, b, c) → [a, b, c]
        eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);
        println!("\n=== A node: concat(a, b, c) = a, b, c ===");

        // Exact [x y z]
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "A exact [x y z] vs [a,b,c]",
            &["(concat x y z)"],
            1,
            &[&[("x", "a"), ("y", "b"), ("z", "c")]],
        );

        // Exact wrong length [x y]
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "A exact [x y] vs [a,b,c]",
            &["(concat x y)"],
            0,
            &[],
        );

        // Prefix [..pre x]  — x = last elem
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "A prefix [..pre x] vs [a,b,c]",
            &["(concat ..pre x)"],
            1,
            &[&[("x", "c")]],
        );

        // Suffix [x ..suf]  — x = first elem
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "A suffix [x ..suf] vs [a,b,c]",
            &["(concat x ..suf)"],
            1,
            &[&[("x", "a")]],
        );

        // Suffix [x y ..suf]
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "A suffix [x y ..suf] vs [a,b,c]",
            &["(concat x y ..suf)"],
            1,
            &[&[("x", "a"), ("y", "b")]],
        );

        // Sliding [..pre x ..suf]  — 3 positions
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "A sliding [..pre x ..suf] vs [a,b,c]",
            &["(concat ..pre x ..suf)"],
            3,
            &[&[("x", "a")], &[("x", "b")], &[("x", "c")]],
        );

        // Sliding [..pre x y ..suf]  — 2 positions
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "A sliding [..pre x y ..suf] vs [a,b,c]",
            &["(concat ..pre x y ..suf)"],
            2,
            &[&[("x", "a"), ("y", "b")], &[("x", "b"), ("y", "c")]],
        );

        // Just rests [..pre ..suf]
        check(
            &eg,
            eg.ops(),
            eg.sorts(),
            "A [..pre ..suf] vs [a,b,c]",
            &["(concat ..pre ..suf)"],
            4,
            &[],
        ); // 4 split points: 0|3, 1|2, 2|1, 3|0
    }

    // ===================================================================
    // Multi-variable + rest: AC, ACI, A
    // ===================================================================

    #[test]
    fn aci_two_vars_plus_rest() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let d = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        // union(a,b,c,g(a)) → {a, b, c, g(a)}
        eg.add(eg.ops().id_by_name("union").unwrap(), &[a, b, c, d]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(union x y ..rest)"]);
        let x_var = vars.find_var("x").unwrap();
        let y_var = vars.find_var("y").unwrap();

        println!("\n=== (union x y ..rest) vs a, b, c, g(a) ===");
        let rest_id = SetVarId(0);
        for (i, m) in matches.iter().enumerate() {
            let xn = eg.node_op_name(m.get(x_var));
            let yn = eg.node_op_name(m.get(y_var));
            let rest: Vec<&str> = m
                .set_slice(rest_id)
                .iter()
                .map(|&g| eg.node_op_name(g))
                .collect();
            println!("  [{i}] x={xn}, y={yn}, rest={{{}}}", rest.join(", "));
        }

        // 4 elements, pick 2 ordered = 4*3 = 12
        assert_eq!(matches.len(), 12);
        // Every ordered pair of distinct elements should appear
        let names = ["a", "b", "c", "g"];
        for &x in &names {
            for &y in &names {
                if x == y {
                    continue;
                }
                assert!(
                    has_binding(&matches, &vars, &eg, &[("x", x), ("y", y)]),
                    "missing x={x}, y={y}"
                );
            }
        }
    }

    #[test]
    fn ac_two_vars_plus_rest() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        // add(a, b, c) → {a:1, b:1, c:1}
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b, c]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(add x:1 y:1 ..rest)"]);
        let x_var = vars.find_var("x").unwrap();
        let y_var = vars.find_var("y").unwrap();

        println!("\n=== (add x:1 y:1 ..rest) vs a:1, b:1, c:1 ===");
        let rest_id = MsetVarId(0);
        for (i, m) in matches.iter().enumerate() {
            let xn = eg.node_op_name(m.get(x_var));
            let yn = eg.node_op_name(m.get(y_var));
            let rest: Vec<String> = m
                .mset_slice(rest_id)
                .iter()
                .map(|c| {
                    let g = DefaultConfig::mset_child_id(c);
                    let k = DefaultConfig::mset_child_mult(c);
                    format!("{}:{}", eg.node_op_name(g), k)
                })
                .collect();
            println!("  [{i}] x={xn}, y={yn}, rest={{{}}}", rest.join(", "));
        }

        // 3 elements, pick 2 ordered = 3*2 = 6
        assert_eq!(matches.len(), 6);
        let names = ["a", "b", "c"];
        for &x in &names {
            for &y in &names {
                if x == y {
                    continue;
                }
                assert!(
                    has_binding(&matches, &vars, &eg, &[("x", x), ("y", y)]),
                    "missing x={x}, y={y}"
                );
            }
        }
    }

    #[test]
    fn ac_two_vars_with_mult_plus_rest() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        // add(a,a,a, b,b, c) → {a:3, b:2, c:1}
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, a, a, b, b, c]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(add x:2 y:1 ..rest)"]);
        let x_var = vars.find_var("x").unwrap();
        let y_var = vars.find_var("y").unwrap();

        println!("\n=== (add x:2 y:1 ..rest) vs a:3, b:2, c:1 ===");
        let rest_id = MsetVarId(0);
        for (i, m) in matches.iter().enumerate() {
            let xn = eg.node_op_name(m.get(x_var));
            let yn = eg.node_op_name(m.get(y_var));
            let rest: Vec<String> = m
                .mset_slice(rest_id)
                .iter()
                .map(|c| {
                    let g = DefaultConfig::mset_child_id(c);
                    let k = DefaultConfig::mset_child_mult(c);
                    format!("{}:{}", eg.node_op_name(g), k)
                })
                .collect();
            println!("  [{i}] x={xn}, y={yn}, rest={{{}}}", rest.join(", "));
        }

        // x:2 means exactly mult 2. Against {a:3, b:2, c:1}:
        // x=b(mult==2) → residual {a:3, c:1}, y:1 → y=c(mult==1) → 1 match
        // x=a? a has 3≠2 → no. x=c? c has 1≠2 → no.
        // Total: 1
        assert_eq!(matches.len(), 1);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "b"), ("y", "c")]));
    }

    // ===================================================================
    // A (sequence) splits
    // ===================================================================

    #[test]
    fn a_prefix_suffix_all_splits() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let d = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        // concat(a, b, c, g(a)) → [a, b, c, g(a)]
        eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c, d]);

        let (matches, _vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(concat ..pre ..suf)"]);

        println!("\n=== (concat ..pre ..suf) vs a, b, c, g(a) ===");
        println!("{} matches (split points):", matches.len());
        let pre_id = SeqVarId(0);
        let suf_id = SeqVarId(1);
        for (i, m) in matches.iter().enumerate() {
            let pre: Vec<&str> = m
                .seq_slice(pre_id)
                .iter()
                .map(|&g| eg.node_op_name(g))
                .collect();
            let suf: Vec<&str> = m
                .seq_slice(suf_id)
                .iter()
                .map(|&g| eg.node_op_name(g))
                .collect();
            println!("  [{i}] pre=[{}], suf=[{}]", pre.join(", "), suf.join(", "));
        }

        // 4 elements → 5 split points: 0|4, 1|3, 2|2, 3|1, 4|0
        assert_eq!(matches.len(), 5);
    }

    #[test]
    fn a_prefix_xy_suffix_all_positions() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let d = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        // concat(a, b, c, g(a)) → [a, b, c, g(a)]
        eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c, d]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(concat ..pre x y ..suf)"]);
        let x_var = vars.find_var("x").unwrap();
        let y_var = vars.find_var("y").unwrap();

        println!("\n=== (concat ..pre x y ..suf) vs a, b, c, g(a) ===");
        let pre_id = SeqVarId(0);
        let suf_id = SeqVarId(1);
        for (i, m) in matches.iter().enumerate() {
            let xn = eg.node_op_name(m.get(x_var));
            let yn = eg.node_op_name(m.get(y_var));
            let pre: Vec<&str> = m
                .seq_slice(pre_id)
                .iter()
                .map(|&g| eg.node_op_name(g))
                .collect();
            let suf: Vec<&str> = m
                .seq_slice(suf_id)
                .iter()
                .map(|&g| eg.node_op_name(g))
                .collect();
            println!(
                "  [{i}] pre=[{}], x={xn}, y={yn}, suf=[{}]",
                pre.join(", "),
                suf.join(", ")
            );
        }

        // 4 elements, window of 2 → 3 positions
        assert_eq!(matches.len(), 3);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "a"), ("y", "b")])); // offset 0
        assert!(has_binding(&matches, &vars, &eg, &[("x", "b"), ("y", "c")])); // offset 1
        assert!(has_binding(&matches, &vars, &eg, &[("x", "c"), ("y", "g")])); // offset 2
    }

    // ===================================================================
    // Iterator vs recursive comparison
    // ===================================================================

    fn query_both<const TRACK: bool>(
        eg: &EGraph<DefaultConfig, NiraLitVal, TRACK, false>,
        ops: &OpRegistry<OpId, SortId, TRACK>,
        sorts: &SortRegistry<SortId, TRACK>,
        srcs: &[&str],
    ) -> (Vec<Match<DefaultConfig>>, Vec<Match<DefaultConfig>>) {
        let model = NiraModel;
        let pats: Vec<_> = srcs.iter().map(|s| parse_pattern(s)).collect();
        let fq = flatten(&pats, ops).unwrap();
        let rq = resolve(
            &fq,
            ops,
            sorts,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let plan = schedule(&rq);
        let index = IndexStore::build(eg);
        let index = VariantIndex::naive(&index);
        let recursive = run_query(
            &plan,
            eg,
            &index,
            &crate::resolve::GlobalCtx::<(), _>::new(),
        );
        let iter = run_query_iter(&plan, eg, &index);
        (recursive, iter)
    }

    fn env_key(m: &Match<DefaultConfig>, eg: &EG) -> Vec<Option<u32>> {
        m.nodes
            .iter()
            .map(|o| o.map(|g| eg.find_const(g).raw()))
            .collect()
    }

    fn assert_same(
        label: &str,
        recursive: &[Match<DefaultConfig>],
        iter: &[Match<DefaultConfig>],
        eg: &EG,
    ) {
        assert_eq!(
            recursive.len(),
            iter.len(),
            "{label}: count mismatch (recursive={}, iter={})",
            recursive.len(),
            iter.len()
        );
        let mut rkeys: Vec<_> = recursive.iter().map(|m| env_key(m, eg)).collect();
        let mut ikeys: Vec<_> = iter.iter().map(|m| env_key(m, eg)).collect();
        rkeys.sort();
        ikeys.sort();
        assert_eq!(rkeys, ikeys, "{label}: binding mismatch");
    }

    #[test]
    fn iter_vs_recursive_plain() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let g_a = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        eg.add(eg.ops().id_by_name("f").unwrap(), &[b, g_a]);

        for pat in &["(f x y)", "(f x (g y))", "(f x x)"] {
            let (r, i) = query_both(&eg, eg.ops(), eg.sorts(), &[pat]);
            assert_same(pat, &r, &i, &eg);
        }
    }

    #[test]
    fn iter_vs_recursive_multi_pattern() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        eg.add(eg.ops().id_by_name("g").unwrap(), &[b]);
        let (r, i) = query_both(&eg, eg.ops(), eg.sorts(), &["(f x y)", "(g y)"]);
        assert_same("multi", &r, &i, &eg);
    }

    #[test]
    fn iter_vs_recursive_ac() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b, c]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, a, a, b, b]);

        for pat in &[
            "(add x:1 y:1)",
            "(add x:1 ..rest)",
            "(add x:2 ..rest)",
            "(add x:2 y:1 ..rest)",
            "(add x:3 y:2)",
        ] {
            let (r, i) = query_both(&eg, eg.ops(), eg.sorts(), &[pat]);
            assert_same(pat, &r, &i, &eg);
        }
    }

    #[test]
    fn iter_vs_recursive_aci() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let d = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        eg.add(eg.ops().id_by_name("union").unwrap(), &[a, b, c, d]);

        for pat in &[
            "(union x y z)",
            "(union x ..rest)",
            "(union x y ..rest)",
            "(union ..rest)",
        ] {
            let (r, i) = query_both(&eg, eg.ops(), eg.sorts(), &[pat]);
            assert_same(pat, &r, &i, &eg);
        }
    }

    #[test]
    fn iter_vs_recursive_a() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);

        for pat in &[
            "(concat x y z)",
            "(concat ..pre x)",
            "(concat x ..suf)",
            "(concat ..pre x ..suf)",
            "(concat ..pre x y ..suf)",
            "(concat ..pre ..suf)",
        ] {
            let (r, i) = query_both(&eg, eg.ops(), eg.sorts(), &[pat]);
            assert_same(pat, &r, &i, &eg);
        }
    }

    // ===================================================================
    // Benchmark: recursive vs iterator
    // ===================================================================

    #[test]
    fn bench_recursive_vs_iterator() {
        use crate::registry::AssocDir;
        // Build a dedicated registry with many nullary ops for distinct leaves.
        let model = NiraModel;
        let mut eg = EGraph::<DefaultConfig, NiraLitVal, false, false>::from_model(&model);
        let e = eg.intern_sort("IExpr");
        // 200 distinct nullary ops
        let leaf_names: Vec<String> = (0..200).map(|i| format!("n{i}")).collect();
        for name in &leaf_names {
            eg.register_op0(name, e);
        }
        eg.register_op2("f", e, e, e);
        eg.register_op1("g", e, e);
        eg.register_op2("h", e, e, e);
        eg.register_a("concat", e, e, AssocDir::Right);
        eg.register_mset("add", e, e);
        eg.register_set("union", e, e);

        let mut leaves = Vec::new();
        for name in &leaf_names {
            leaves.push(eg.add(eg.ops().id_by_name(name).unwrap(), &[]));
        }
        for i in 0..100 {
            let a = leaves[i];
            let b = leaves[i + 100];
            eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
            eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
            eg.add(eg.ops().id_by_name("h").unwrap(), &[a, b]);
        }
        for i in 0..50 {
            eg.add(
                eg.ops().id_by_name("add").unwrap(),
                &[
                    leaves[i],
                    leaves[i + 50],
                    leaves[i + 100],
                    leaves[i],
                    leaves[i + 50],
                ],
            );
        }
        for i in 0..50 {
            eg.add(
                eg.ops().id_by_name("union").unwrap(),
                &[leaves[i], leaves[i + 50], leaves[i + 100], leaves[i + 150]],
            );
        }
        for i in 0..50 {
            eg.add(
                eg.ops().id_by_name("concat").unwrap(),
                &[leaves[i], leaves[i + 50], leaves[i + 100]],
            );
        }

        let patterns: &[&str] = &[
            "(f x y)",
            "(f x (g y))",
            "(add x:1 ..rest)",
            "(add x:1 y:1 ..rest)",
            "(union x ..rest)",
            "(union x y ..rest)",
            "(concat ..pre x ..suf)",
            "(concat ..pre x y ..suf)",
        ];

        let model = NiraModel;
        let index = IndexStore::build(&eg);
        let index = VariantIndex::naive(&index);

        for pat in patterns {
            let p = parse_pattern(pat);
            let fq = flatten(&[p], eg.ops()).unwrap();
            let rq = resolve(
                &fq,
                eg.ops(),
                eg.sorts(),
                &model,
                &crate::resolve::GlobalCtx::<_, ()>::new(),
            )
            .unwrap();
            let plan = schedule(&rq);

            let iters = 100;

            let t0 = std::time::Instant::now();
            let mut n_rec = 0;
            for _ in 0..iters {
                n_rec = run_query(
                    &plan,
                    &eg,
                    &index,
                    &crate::resolve::GlobalCtx::<(), _>::new(),
                )
                .len();
            }
            let d_rec = t0.elapsed();

            let t1 = std::time::Instant::now();
            let mut n_iter = 0;
            for _ in 0..iters {
                n_iter = run_query_iter(&plan, &eg, &index).len();
            }
            let d_iter = t1.elapsed();

            assert_eq!(n_rec, n_iter);
            let us_rec = d_rec.as_micros() as f64 / iters as f64;
            let us_iter = d_iter.as_micros() as f64 / iters as f64;
            let ratio = us_iter / us_rec;
            println!(
                "{pat:40} matches={n_rec:5}  rec={us_rec:8.1}µs  iter={us_iter:8.1}µs  ratio={ratio:.2}x"
            );
        }
    }

    // ===================================================================
    // MatchSet tests
    // ===================================================================

    fn make_match_set<const TRACK: bool>(
        eg: &EGraph<DefaultConfig, NiraLitVal, TRACK, false>,
        ops: &OpRegistry<OpId, SortId, TRACK>,
        sorts: &SortRegistry<SortId, TRACK>,
        srcs: &[&str],
    ) -> (MatchSet<DefaultConfig>, crate::resolve::MatchShape) {
        let model = NiraModel;
        let pats: Vec<_> = srcs.iter().map(|s| parse_pattern(s)).collect();
        let fq = flatten(&pats, ops).unwrap();
        let rq = resolve(
            &fq,
            ops,
            sorts,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let shape = rq.shape.clone();
        let plan = schedule(&rq);
        let index = IndexStore::build(eg);
        let index = VariantIndex::naive(&index);
        let ng = crate::resolve::GlobalCtx::<(), _>::new();
        let mut iter = MatchIterator::new(&plan, eg, &index, &ng);
        let set = iter.collect_set(&shape);
        (set, shape)
    }

    /// Find VarId by name in a MatchShape.
    fn ni(shape: &crate::resolve::MatchShape, name: &str) -> VarId {
        let i = shape.nodes.iter().position(|n| n == name).unwrap();
        VarId::new(i as u16)
    }

    #[test]
    fn matchset_plain_bindings() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);
        eg.add(eg.ops().id_by_name("f").unwrap(), &[b, a]);

        let (set, shape) = make_match_set(&eg, eg.ops(), eg.sorts(), &["(f x y)"]);
        assert_eq!(set.count, 2);
        let xi = ni(&shape, "x");
        let yi = ni(&shape, "y");
        let mut pairs: Vec<_> = (0..set.count)
            .map(|j| {
                (
                    eg.find_const(set.get_node(xi, j)).raw(),
                    eg.find_const(set.get_node(yi, j)).raw(),
                )
            })
            .collect();
        pairs.sort();
        let a_r = eg.find_const(a).raw();
        let b_r = eg.find_const(b).raw();
        let mut expected = vec![(a_r, b_r), (b_r, a_r)];
        expected.sort();
        assert_eq!(pairs, expected);
    }

    #[test]
    fn matchset_ac_with_mset_rest() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b, c]);

        let (set, shape) = make_match_set(&eg, eg.ops(), eg.sorts(), &["(add x:1 ..rest)"]);
        assert_eq!(set.count, 3);
        assert_eq!(shape.msets.len(), 1);
        let xi = ni(&shape, "x");
        for j in 0..set.count {
            let rest_slice = set.mset_slice(MsetVarId(0), j);
            // x takes 1 element, rest has 2
            assert_eq!(
                rest_slice.len(),
                2,
                "match {j}: rest should have 2 elements"
            );
            // x + rest should recompose to {a, b, c}
            let mut ids: Vec<u32> = rest_slice
                .iter()
                .map(|c| eg.find_const(DefaultConfig::mset_child_id(c)).raw())
                .collect();
            ids.push(eg.find_const(set.get_node(xi, j)).raw());
            ids.sort();
            let mut orig = vec![
                eg.find_const(a).raw(),
                eg.find_const(b).raw(),
                eg.find_const(c).raw(),
            ];
            orig.sort();
            assert_eq!(ids, orig, "match {j}: recomposition failed");
        }
    }

    #[test]
    fn matchset_aci_with_set_rest() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("union").unwrap(), &[a, b, c]);

        let (set, shape) = make_match_set(&eg, eg.ops(), eg.sorts(), &["(union x ..rest)"]);
        assert_eq!(set.count, 3);
        assert_eq!(shape.sets.len(), 1);
        let xi = ni(&shape, "x");
        for j in 0..set.count {
            let rest_slice = set.set_slice(SetVarId(0), j);
            assert_eq!(rest_slice.len(), 2);
            let mut ids: Vec<u32> = rest_slice.iter().map(|&g| eg.find_const(g).raw()).collect();
            ids.push(eg.find_const(set.get_node(xi, j)).raw());
            ids.sort();
            let mut orig = vec![
                eg.find_const(a).raw(),
                eg.find_const(b).raw(),
                eg.find_const(c).raw(),
            ];
            orig.sort();
            assert_eq!(ids, orig, "match {j}: recomposition failed");
        }
    }

    #[test]
    fn matchset_a_sliding_window() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);

        let (set, shape) = make_match_set(&eg, eg.ops(), eg.sorts(), &["(concat ..pre x ..suf)"]);
        assert_eq!(set.count, 3);
        assert_eq!(shape.seqs.len(), 2);
        let xi = ni(&shape, "x");
        for j in 0..set.count {
            let pre_s = set.seq_slice(SeqVarId(0), j);
            let suf_s = set.seq_slice(SeqVarId(1), j);
            // pre + [x] + suf should recompose to [a, b, c]
            let mut recomp: Vec<u32> = pre_s.iter().map(|&g| eg.find_const(g).raw()).collect();
            recomp.push(eg.find_const(set.get_node(xi, j)).raw());
            recomp.extend(suf_s.iter().map(|&g| eg.find_const(g).raw()));
            let orig: Vec<u32> = [a, b, c].iter().map(|&g| eg.find_const(g).raw()).collect();
            assert_eq!(recomp, orig, "match {j}: recomposition failed");
        }
    }

    #[test]
    fn matchset_agrees_with_vec_match() {
        // Verify MatchSet contents match Vec<Match> from recursive engine.
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, a, b, c]);

        let model = NiraModel;
        let pat = parse_pattern("(add x:1 y:1 ..rest)");
        let fq = flatten(&[pat], eg.ops()).unwrap();
        let rq = resolve(
            &fq,
            eg.ops(),
            eg.sorts(),
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let plan = schedule(&rq);
        let index = IndexStore::build(&eg);
        let index = VariantIndex::naive(&index);

        let ng = crate::resolve::GlobalCtx::<(), _>::new();
        let vec_matches = run_query(&plan, &eg, &index, &ng);
        let shape = rq.shape.clone();
        let mut iter = MatchIterator::new(&plan, &eg, &index, &ng);
        let set = iter.collect_set(&shape);

        assert_eq!(vec_matches.len(), set.count);
        let xi = ni(&shape, "x");
        let yi = ni(&shape, "y");
        let x_vid = shape.find_var("x").unwrap();
        let y_vid = shape.find_var("y").unwrap();
        for j in 0..set.count {
            assert_eq!(
                eg.find_const(set.get_node(xi, j)),
                eg.find_const(vec_matches[j].get(x_vid))
            );
            assert_eq!(
                eg.find_const(set.get_node(yi, j)),
                eg.find_const(vec_matches[j].get(y_vid))
            );
            assert_eq!(
                set.mset_slice(MsetVarId(0), j).len(),
                vec_matches[j].mset_slice(MsetVarId(0)).len()
            );
        }
    }

    #[test]
    fn matchset_empty() {
        let eg = make_eg();
        let (set, _) = make_match_set(&eg, eg.ops(), eg.sorts(), &["(f x y)"]);
        assert_eq!(set.count, 0);
    }

    #[test]
    fn cloned_iter_filter_take() {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("union").unwrap(), &[a, b, c]);

        let model = NiraModel;
        let pat = parse_pattern("(union x ..rest)");
        let fq = flatten(&[pat], eg.ops()).unwrap();
        let rq = resolve(
            &fq,
            eg.ops(),
            eg.sorts(),
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let plan = schedule(&rq);
        let index = IndexStore::build(&eg);
        let index = VariantIndex::naive(&index);

        let x = rq.shape.find_var("x").unwrap();
        // Use cloned_iter with filter + take
        let ng = crate::resolve::GlobalCtx::<(), _>::new();
        let iter = MatchIterator::new(&plan, &eg, &index, &ng);
        let filtered: Vec<Match<DefaultConfig>> = iter
            .cloned_iter()
            .filter(|m| eg.find_const(m.get(x)) != eg.find_const(a))
            .take(2)
            .collect();
        // 3 total matches (x=a, x=b, x=c), filter out x=a → 2 remain, take(2) gets both
        assert_eq!(filtered.len(), 2);
        for m in &filtered {
            assert_ne!(eg.find_const(m.get(x)), eg.find_const(a));
        }
    }

    #[test]
    fn ac_concrete_with_higher_mult() {
        // (Add (a) (a) (b)) → AC node {a:2, b:1}
        // Pattern: (add (a) ..rest) — concrete (a) with implicit :1
        // Question: does this match when a has multiplicity 2?
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _add = eg.add(eg.ops().id_by_name("add").unwrap(), &[a, a, b]);

        let (matches, shape) = query_named(&eg, eg.ops(), eg.sorts(), &["(add (a) ..rest)"]);
        eprintln!("=== (add (a) ..rest) against {{a:2, b:1}} ===");
        eprintln!("match count: {}", matches.len());
        for (i, m) in matches.iter().enumerate() {
            let bindings = binding_map(m, &shape, &eg);
            eprintln!("  match {i}: {bindings:?}");
            for (mi, name) in shape.msets.iter().enumerate() {
                let (start, len) = m.mset_spans[mi];
                let rest: Vec<_> = m.mset_pool[start as usize..(start + len) as usize]
                    .iter()
                    .map(|c| format!("{:?}", c))
                    .collect();
                eprintln!("    {name} = [{rest}]", rest = rest.join(", "));
            }
        }

        // Also test: (add (a):k ..rest) — bind k to multiplicity
        let (matches2, shape2) = query_named(&eg, eg.ops(), eg.sorts(), &["(add (a):k ..rest)"]);
        eprintln!("\n=== (add (a):k ..rest) against {{a:2, b:1}} ===");
        eprintln!("match count: {}", matches2.len());
        for (i, m) in matches2.iter().enumerate() {
            let bindings = binding_map(m, &shape2, &eg);
            eprintln!("  match {i}: {bindings:?}");
            for (mi, name) in shape2.msets.iter().enumerate() {
                let (start, len) = m.mset_spans[mi];
                let rest: Vec<_> = m.mset_pool[start as usize..(start + len) as usize]
                    .iter()
                    .map(|c| format!("{:?}", c))
                    .collect();
                eprintln!("    {name} = [{rest}]", rest = rest.join(", "));
            }
            for (mi, name) in shape2.mults.iter().enumerate() {
                eprintln!("    {name} = {}", m.mults[mi]);
            }
        }
    }

    #[test]
    fn ac_constraint_ge() {
        // {a:3, b:1, c:2}
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, a, a, b, c, c]);

        // x:k>=2 ..rest → matches a (k=3) and c (k=2), not b (k=1)
        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(add x:k>=2 ..rest)"]);
        eprintln!("\n=== (add x:k>=2 ..rest) against {{a:3, b:1, c:2}} ===");
        for (i, m) in matches.iter().enumerate() {
            let bindings = binding_map(m, &vars, &eg);
            let k = m.mults[0];
            eprintln!("  match {i}: {bindings:?}, k={k}");
        }
        assert_eq!(matches.len(), 2);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "a")]));
        assert!(has_binding(&matches, &vars, &eg, &[("x", "c")]));
    }

    #[test]
    fn ac_constraint_le() {
        // {a:3, b:1, c:2}
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, a, a, b, c, c]);

        // x:k<=2 ..rest → matches b (k=1) and c (k=2), not a (k=3)
        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(add x:k<=2 ..rest)"]);
        eprintln!("\n=== (add x:k<=2 ..rest) against {{a:3, b:1, c:2}} ===");
        for (i, m) in matches.iter().enumerate() {
            let bindings = binding_map(m, &vars, &eg);
            let k = m.mults[0];
            eprintln!("  match {i}: {bindings:?}, k={k}");
        }
        assert_eq!(matches.len(), 2);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "b")]));
        assert!(has_binding(&matches, &vars, &eg, &[("x", "c")]));
    }

    #[test]
    fn ac_nonlinear_mult_same_count() {
        // {a:2, b:2, c:3}
        // Pattern: (add x:k y:k ..rest) — x and y must have the SAME multiplicity
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, a, b, b, c, c, c]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(add x:k y:k ..rest)"]);
        eprintln!("\n=== (add x:k y:k ..rest) against {{a:2, b:2, c:3}} ===");
        for (i, m) in matches.iter().enumerate() {
            let bindings = binding_map(m, &vars, &eg);
            let k = m.mults[0];
            eprintln!("  match {i}: {bindings:?}, k={k}");
        }
        // x and y must have the same multiplicity k.
        // a:2 and b:2 both have mult 2 → x=a,y=b and x=b,y=a (k=2)
        // c:3 has no partner with mult 3 → no match involving c
        // Expected: 2 matches
        assert_eq!(matches.len(), 2);
        assert!(has_binding(&matches, &vars, &eg, &[("x", "a"), ("y", "b")]));
        assert!(has_binding(&matches, &vars, &eg, &[("x", "b"), ("y", "a")]));
    }

    #[test]
    fn ac_nonlinear_mult_no_match() {
        // {a:1, b:2, c:3} — all different multiplicities
        // Pattern: (add x:k y:k ..rest) — no two elements have the same mult
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b, b, c, c, c]);

        let (matches, vars) = query_named(&eg, eg.ops(), eg.sorts(), &["(add x:k y:k ..rest)"]);
        eprintln!("\n=== (add x:k y:k ..rest) against {{a:1, b:2, c:3}} ===");
        for (i, m) in matches.iter().enumerate() {
            let bindings = binding_map(m, &vars, &eg);
            let k = m.mults[0];
            eprintln!("  match {i}: {bindings:?}, k={k}");
        }
        // No two elements share the same multiplicity → 0 matches
        assert_eq!(matches.len(), 0);
    }

    #[test]
    fn ac_nonlinear_empty_interval() {
        // Pattern: (add x:k>=3 y:k<=1 ..rest)
        // Interval for k: [3, ∞) ∩ (-∞, 1] = [3, 1] = empty
        // This should be rejected at resolve time as unsatisfiable.
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, a, a]);

        let model = NiraModel;
        let pats: Vec<_> = ["(add x:k>=3 y:k<=1 ..rest)"]
            .iter()
            .map(|s| parse_pattern(s))
            .collect();
        let fq = flatten(&pats, eg.ops()).unwrap();
        let result = resolve(
            &fq,
            eg.ops(),
            eg.sorts(),
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        );
        eprintln!("\n=== (add x:k>=3 y:k<=1 ..rest) — empty interval ===");
        eprintln!("resolve result: {result:?}");
        // Should be an error: unsatisfiable multiplicity
        assert!(result.is_err(), "expected unsatisfiable interval error");
    }

    #[test]
    fn ac_nonlinear_narrow_interval() {
        // Pattern: (add x:k>=2 y:k<=3 ..rest)
        // Interval for k: [2, 3]. Only elements with mult 2 or 3 qualify.
        // Against {a:1, b:2, c:3, d:4}: only b(2) and c(3) are in [2,3]
        // x:k>=2 y:k<=3 with same k → x and y must have the SAME mult in [2,3]
        // b:2 and c:3 have different mults → no pair matches
        // But b:2 and b:2 would match if b appeared twice... it doesn't.
        // So: 0 matches.
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b, b, c, c, c]);

        let (matches, vars) =
            query_named(&eg, eg.ops(), eg.sorts(), &["(add x:k>=2 y:k<=3 ..rest)"]);
        eprintln!("\n=== (add x:k>=2 y:k<=3 ..rest) against {{a:1, b:2, c:3}} ===");
        for (i, m) in matches.iter().enumerate() {
            let bindings = binding_map(m, &vars, &eg);
            let k = m.mults[0];
            eprintln!("  match {i}: {bindings:?}, k={k}");
        }
        // b has mult 2 (in [2,3]), c has mult 3 (in [2,3]), but 2≠3 → non-linear fails
        // a has mult 1 (not in [2,3])
        assert_eq!(matches.len(), 0);
    }

    // -----------------------------------------------------------------------
    // Snapshot semantics: the match set does not depend on the join order
    // -----------------------------------------------------------------------

    /// Schedule `srcs` with `first`'s operator forced to the front of the
    /// greedy order, by handing the scheduler a cardinality of 0 for it.
    /// The other operators get an equal, large cardinality, so nothing but the
    /// pin decides the first atom.
    fn plan_driven_from(
        eg: &EG,
        srcs: &[&str],
        first: &str,
        ops_in_query: &[&str],
    ) -> (RQ, QueryPlan<OpId, u32, NiraLitVal>) {
        let rq = resolve_srcs(eg, srcs);
        let mut stats = crate::schedule::IndexStats::<OpId>::new();
        for name in ops_in_query {
            stats
                .op_card
                .insert(eg.ops().id_by_name(name).unwrap(), 1000);
        }
        stats.op_card.insert(eg.ops().id_by_name(first).unwrap(), 0);
        let plan = crate::schedule::schedule_with_stats(&rq, &stats);
        (rq, plan)
    }

    type RQ = crate::resolve::ResolvedQuery<OpId, SortId, NiraLitVal>;

    /// Compile and resolve `srcs` against `eg`'s registries.
    fn resolve_srcs(eg: &EG, srcs: &[&str]) -> RQ {
        let pats: Vec<_> = srcs.iter().map(|s| parse_pattern(s)).collect();
        let fq = flatten(&pats, eg.ops()).unwrap();
        resolve(
            &fq,
            eg.ops(),
            eg.sorts(),
            &NiraModel,
            &crate::resolve::GlobalCtx::<SortId, ()>::new(),
        )
        .unwrap()
    }

    /// Run the query through all three engines and return the match set as a
    /// sorted list of binding keys.
    ///
    /// The three must agree. Static push against static pull is the check that
    /// was already here: two independent walks of one plan. Runtime-scheduled
    /// push against static pull is the oracle for the scheduling flag, and it is
    /// the strongest one available, because the pull engine shares nothing with
    /// the flag — it is a different control structure (an explicit stack, not
    /// recursion) walking a different atom order (the plan's, fixed) — so an
    /// agreement between them is not two copies of the same mistake.
    ///
    /// A divergence here is a bug in its own right, so it is asserted rather
    /// than returned.
    fn match_keys(
        eg: &EG,
        rq: &RQ,
        plan: &QueryPlan<OpId, u32, NiraLitVal>,
        index: &IndexStore<DefaultConfig>,
    ) -> Vec<Vec<Option<u32>>> {
        let vindex = VariantIndex::naive(index);
        let ng = crate::resolve::GlobalCtx::<SortId, _>::new();

        let key = |m: &Match<DefaultConfig>| -> Vec<Option<u32>> {
            m.nodes
                .iter()
                .map(|o| o.map(|g| index.round_repr(g).unwrap_or(g).raw()))
                .collect()
        };

        let mut recursive: Vec<_> = run_query(plan, eg, &vindex, &ng).iter().map(key).collect();
        let mut it = MatchIterator::new(plan, eg, &vindex, &ng);
        let mut pull = Vec::new();
        while it.next_match() {
            pull.push(key(it.env()));
        }
        set_runtime_scheduling(true);
        let mut adaptive: Vec<_> = run_query_scheduled(rq, plan, eg, &vindex, &ng)
            .iter()
            .map(key)
            .collect();
        set_runtime_scheduling(false);
        recursive.sort();
        pull.sort();
        adaptive.sort();
        assert_eq!(recursive, pull, "the two matcher engines disagree");
        assert_eq!(
            adaptive, pull,
            "runtime atom scheduling changed the match set"
        );
        recursive
    }

    /// `(f b c)` and `(g a)`, with `c` and `(g a)` in different classes at the
    /// index build and merged afterwards — the shape of a mid-round merge by an
    /// earlier rule's actions. `tall_g_class` decides which of the two classes
    /// the union-find keeps as representative, by giving the `g`-node's class a
    /// second member (hence a taller tree) before the build.
    ///
    /// The snapshot answer for `(f x (g y))` is *no match*: at the build,
    /// `(f b c)`'s second child was alone in its class and that class held no
    /// `g`-node.
    fn mid_round_merge(tall_g_class: bool) -> (EG, IndexStore<DefaultConfig>) {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let ga = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        let _fbc = eg.add(eg.ops().id_by_name("f").unwrap(), &[b, c]);
        if tall_g_class {
            let haa = eg.add(eg.ops().id_by_name("h").unwrap(), &[a, a]);
            eg.merge(ga, haa);
        }
        eg.rebuild();

        // The round's index. Everything after this point is what a rule's
        // actions do to the e-graph while later rules of the same round match.
        let index = IndexStore::build(&eg);
        eg.merge(c, ga);
        (eg, index)
    }

    /// The match set is a function of the e-graph the round's index was built
    /// from, not of the join order the scheduler happened to choose.
    ///
    /// Both orders below reach the `g` atom by a different access path — from
    /// the `f` atom it is `ByRepr` on the extracted child, from the `g` atom it
    /// is `ByChildPos` on the bound `g`-node — and a mid-round merge moves the
    /// two paths in opposite directions: whichever class the union-find keeps,
    /// exactly one of the two paths lands on a bucket that the merge made
    /// reachable. Canonicalizing with the live union-find therefore made one
    /// order report a match and the other none, on the same e-graph. Both
    /// parameterizations are here because they disagree in opposite directions;
    /// which one a given union-by-rank policy produces is not this test's
    /// business.
    #[test]
    fn match_set_is_independent_of_join_order() {
        for tall_g_class in [false, true] {
            let (eg, index) = mid_round_merge(tall_g_class);
            let from_f = plan_driven_from(&eg, &["(f x (g y))"], "f", &["f", "g"]);
            let from_g = plan_driven_from(&eg, &["(f x (g y))"], "g", &["f", "g"]);

            // The pin is worth nothing if both orders compile to the same plan.
            assert_ne!(
                from_f.1.steps, from_g.1.steps,
                "the two pins produced the same plan (tall_g_class={tall_g_class})"
            );

            let mf = match_keys(&eg, &from_f.0, &from_f.1, &index);
            let mg = match_keys(&eg, &from_g.0, &from_g.1, &index);
            assert_eq!(
                mf, mg,
                "join order changed the match set (tall_g_class={tall_g_class})"
            );
            assert!(
                mf.is_empty(),
                "matched a class membership the round's index does not have \
                 (tall_g_class={tall_g_class}): {mf:?}"
            );
        }
    }

    /// The other half of the same contract, on the equality-check path rather
    /// than the index path: two children that the round's index kept apart do
    /// not satisfy a non-linear pattern just because a later merge joined them.
    /// `CheckChildEq` used to test live equality, which admitted the match.
    #[test]
    fn nonlinear_check_uses_the_rounds_classes() {
        let mut eg = make_eg();
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let _fbc = eg.add(eg.ops().id_by_name("f").unwrap(), &[b, c]);
        eg.merge(b, c);
        eg.rebuild();

        let index = IndexStore::build(&eg);
        let driven = plan_driven_from(&eg, &["(f x x)"], "f", &["f"]);
        assert_eq!(
            match_keys(&eg, &driven.0, &driven.1, &index).len(),
            1,
            "control: a merge the index build can see does make the pattern match"
        );

        let mut eg = make_eg();
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let _fbc = eg.add(eg.ops().id_by_name("f").unwrap(), &[b, c]);
        eg.rebuild();
        let index = IndexStore::build(&eg);
        eg.merge(b, c);
        let driven = plan_driven_from(&eg, &["(f x x)"], "f", &["f"]);
        let matches = match_keys(&eg, &driven.0, &driven.1, &index);
        assert!(
            matches.is_empty(),
            "a merge after the index build made `(f x x)` match: {matches:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Runtime atom scheduling
    // -----------------------------------------------------------------------

    /// An e-graph holding one node of every shape the lowering can emit, so the
    /// sweep below reaches every branch of `emit_atom` and `try_eager_lower`.
    fn every_shape() -> EG {
        let mut eg = make_eg();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let ga = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        let gb = eg.add(eg.ops().id_by_name("g").unwrap(), &[b]);
        let f = eg.ops().id_by_name("f").unwrap();
        let fab = eg.add(f, &[a, b]);
        eg.add(f, &[ga, b]);
        eg.add(f, &[a, a]);
        eg.add(f, &[gb, ga]);
        eg.add(eg.ops().id_by_name("h").unwrap(), &[fab, gb]);
        eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);
        eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b, c]);
        eg.add(eg.ops().id_by_name("union").unwrap(), &[a, b, c]);
        eg.rebuild();
        eg
    }

    /// The flag does not change the match set, on every atom shape.
    ///
    /// `match_keys` runs the query three ways and asserts all three agree, so
    /// this is the sweep of shapes rather than the comparison itself. The
    /// property is not an accident of these patterns: the match set is a
    /// function of the round's index and the query (chapter 09, "Which
    /// Snapshot"), which is exactly what makes an order change a performance
    /// change. This is that guarantee held to the strongest oracle available.
    #[test]
    fn runtime_scheduling_matches_the_static_plan() {
        let eg = every_shape();
        let index = IndexStore::build(&eg);
        let shapes: &[&[&str]] = &[
            &["(f x y)"],
            &["(f (g x) y)"],
            &["(f x x)"],
            &["(h (f x y) (g y))"],
            &["(concat x y ..rest)"],
            &["(add x:1 ..rest)"],
            &["(union x ..rest)"],
            // Disconnected conjuncts: two atoms with no variable in common, so
            // the order is decided by cost alone.
            &["(f x y)", "(g z)"],
            // Three atoms joined through child variables — the shape whose
            // order the flag can change per binding.
            &["(f x y)", "(g x)", "(g y)"],
        ];
        for srcs in shapes {
            let rq = resolve_srcs(&eg, srcs);
            let plan = schedule(&rq);
            let m = match_keys(&eg, &rq, &plan, &index);
            assert!(!m.is_empty(), "{srcs:?}: shape must match something");
        }
    }

    /// Two bindings of one query, at the same depth, schedule different atoms.
    ///
    /// The counterpart of `op_restriction_policy_is_taken_per_binding` for the
    /// atom choice: it asserts the mechanism ran, not just that the answer came
    /// out right. `(f x y)` binds a pair of child classes; the `g` atom over `x`
    /// and the `h` atom over `y` have their bucket sizes swapped between the two
    /// `f` nodes, so a plan-time order is wrong on one of them and the per-binding
    /// choice is right on both.
    #[test]
    fn atom_order_is_chosen_per_binding() {
        let mut eg = make_eg();
        let (f, g, h) = (
            eg.ops().id_by_name("f").unwrap(),
            eg.ops().id_by_name("g").unwrap(),
            eg.ops().id_by_name("h").unwrap(),
        );
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        // Two `f` nodes over four leaf classes. `x` is read by the `h` atom at
        // position 1 and `y` by the `g` atom at position 0, neither of which is
        // where `f` puts them, so the two buckets hold only the probe nodes.
        let x0 = eg.add(g, &[a]);
        let y0 = eg.add(g, &[b]);
        let x1 = eg.add(g, &[c]);
        let y1 = eg.add(h, &[a, b]);
        eg.add(f, &[x0, y0]);
        eg.add(f, &[x1, y1]);
        // Binding 0: `x0` has two `h` parents, `y0` has none — the `g` atom is
        // the empty one. Binding 1: the other way round.
        eg.add(h, &[a, x0]);
        eg.add(h, &[b, x0]);
        eg.add(g, &[y1]);
        eg.rebuild();

        let index = IndexStore::build(&eg);
        let rq = resolve_srcs(&eg, &["(f x y)", "(h w x)", "(g y)"]);
        let plan = schedule(&rq);
        let _ = take_atom_choices();
        match_keys(&eg, &rq, &plan, &index);
        let choices = take_atom_choices();

        // The first choice is made with nothing bound and is the same for every
        // binding; what this test is about is the ones after it.
        let after_f: Vec<usize> = choices
            .iter()
            .filter(|(used, _)| *used != 0)
            .map(|(_, ai)| *ai)
            .collect();
        assert!(
            after_f.contains(&1) && after_f.contains(&2),
            "both atoms must be chosen second on some binding, got {choices:?}"
        );
    }

    // -----------------------------------------------------------------------
    // Operator-restriction policy
    // -----------------------------------------------------------------------

    /// The policy is process-wide, so the tests that pin it take turns.
    static OP_FILTER_PIN: std::sync::Mutex<()> = std::sync::Mutex::new(());

    /// The rule of `demote_by_op`, stated against the two lengths directly.
    ///
    /// Exhaustive where the e-graph tests cannot be: the filter branch needs a
    /// relation of [`OP_FILTER_MIN_RELATION`], and materializing one at every
    /// corner would cost a hundred thousand nodes per case.
    #[test]
    fn op_restriction_rule_reads_both_lengths() {
        let c = OP_FILTER_MIN_RELATION;
        let k = OP_FILTER_RELATION_PER_CANDIDATE;
        // (m, n, expected demotion)
        let cases = [
            // The threshold on the relation climbs with the bucket, so a small
            // bucket filters against a relation a large one would leapfrog.
            (1, k - 1, false),
            (1, k, true),
            (16, 16 * k - 1, false),
            (16, 16 * k, true),
            // Until it reaches the ceiling, past which no bucket size matters.
            (c / k, c, true),
            (c, c - 1, false),
            (c, c, true),
            // The hub shape: a quarter of a million parents against a relation
            // of twenty-six. This is the case the unconditional filter lost on.
            (262_144, 26, false),
            // The guard: once the bucket outgrows twice the relation, the
            // operand's `min(m, n)` work stops growing and the test's does not.
            (2 * c, c, true),
            (2 * c + 1, c, false),
            // Saturating arithmetic at both ends rather than wrapping.
            (usize::MAX, c, false),
            (usize::MAX, usize::MAX, true),
            (0, 1, true),
        ];
        for (m, n, expect) in cases {
            assert_eq!(
                demote_by_op(m, Some(n), OpFilterPolicy::Adaptive),
                expect,
                "m={m} n={n}"
            );
            // The pins ignore the lengths.
            assert!(demote_by_op(m, Some(n), OpFilterPolicy::AlwaysFilter));
            assert!(!demote_by_op(m, Some(n), OpFilterPolicy::AlwaysLeapfrog));
        }
        // A join with no `ByOp` to place decides nothing under any policy: its
        // single lookup is the only thing enumerating candidates.
        for p in [
            OpFilterPolicy::Adaptive,
            OpFilterPolicy::AlwaysFilter,
            OpFilterPolicy::AlwaysLeapfrog,
        ] {
            assert!(!demote_by_op(3, None, p));
        }
        take_op_restriction_log();
    }

    /// Two hub classes, one whose `f0` parents are read against a relation above
    /// the threshold and one whose `f1` parents are read against a relation of
    /// forty, so one query per operator drives the decision both ways.
    ///
    /// `f0`'s relation is sized from the rule's own constant rather than written
    /// down, so it stays on the filter side of the threshold if the constant
    /// moves: four parents against `4 * OP_FILTER_RELATION_PER_CANDIDATE` is
    /// exactly at it. The ceiling and the bucket guard are corners this shape
    /// cannot reach at a scale worth building; `op_restriction_rule_reads_both_lengths`
    /// covers them.
    fn op_restriction_eg() -> (EG, ENodeId, ENodeId) {
        let mut eg = EG::from_model(&NiraModel);
        let e = eg.intern_sort("IExpr");
        eg.register_op0("z", e);
        eg.register_op1("s", e, e);
        eg.register_op1("hub", e, e);
        eg.register_op2("f0", e, e, e);
        eg.register_op2("f1", e, e, e);
        let s = eg.ops().id_by_name("s").unwrap();
        let hub = eg.ops().id_by_name("hub").unwrap();
        let f0 = eg.ops().id_by_name("f0").unwrap();
        let f1 = eg.ops().id_by_name("f1").unwrap();

        // Enough distinct classes that `side * side` distinct `f0` child pairs
        // reach the relation size.
        let relation = 4 * OP_FILTER_RELATION_PER_CANDIDATE;
        let side = (relation as f64).sqrt().ceil() as usize + 1;
        let mut leaves = vec![eg.add(eg.ops().id_by_name("z").unwrap(), &[])];
        for i in 1..side {
            let prev = leaves[i - 1];
            leaves.push(eg.add(s, &[prev]));
        }
        let hub_a = eg.add(hub, &[leaves[0]]);
        let hub_b = eg.add(hub, &[leaves[1]]);

        // `by_op[f0]`: four parents of `hub_a` and the rest off the hubs.
        for k in 0..4 {
            eg.add(f0, &[hub_a, leaves[k]]);
        }
        let mut made = 4;
        'fill: for i in 0..side {
            for j in 0..side {
                if made >= relation {
                    break 'fill;
                }
                eg.add(f0, &[leaves[i], leaves[j]]);
                made += 1;
            }
        }
        // `by_op[f1]`: forty parents of `hub_b` and nothing else.
        for k in 0..40 {
            eg.add(f1, &[hub_b, leaves[k]]);
        }
        eg.rebuild();
        (eg, hub_a, hub_b)
    }

    /// Run `src` against `eg` under `policy` and return the decisions the joins
    /// made together with the match set, keyed so it can be compared across
    /// policies.
    fn op_restriction_run(
        eg: &EG,
        src: &str,
        policy: OpFilterPolicy,
    ) -> (Vec<OpRestriction>, Vec<Vec<ENodeId>>) {
        set_op_filter_policy(policy);
        let pats = [parse_pattern(src)];
        let fq = flatten(&pats, eg.ops()).unwrap();
        let rq = resolve(
            &fq,
            eg.ops(),
            eg.sorts(),
            &NiraModel,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let plan = schedule(&rq);
        let store = IndexStore::build(eg);
        let index = VariantIndex::naive(&store);
        take_op_restriction_log();
        let ms = run_query(
            &plan,
            eg,
            &index,
            &crate::resolve::GlobalCtx::<(), _>::new(),
        );
        let log = take_op_restriction_log();
        let mut keys: Vec<Vec<ENodeId>> = ms
            .iter()
            .map(|m| {
                (0..plan.shape.num_vars())
                    .map(|v| m.get(VarId(v as u16)))
                    .collect()
            })
            .collect();
        keys.sort();
        (log, keys)
    }

    /// The shipped rule decides per binding, not per atom: one query, two
    /// bindings of the same join, two mechanisms.
    ///
    /// `hub_a` has four `f0` parents and is read against the whole `f0`
    /// relation, the shape the demotion was landed for — a handful of
    /// candidates and a relation two orders larger, where the test wins.
    /// `hub_b`'s bucket holds its forty `f1` parents, which is the same
    /// position-0 bucket the `f0` join probes, and against a relation of that
    /// size the operand wins. Both decisions are taken inside one `run_query`.
    ///
    /// This is the decision gate: it asserts which mechanism ran, not how long
    /// it took, so it holds in every build profile. The timing half is
    /// `tests/ematch_op_filter.rs`.
    #[test]
    fn op_restriction_policy_is_taken_per_binding() {
        let _pin = OP_FILTER_PIN.lock().unwrap_or_else(|e| e.into_inner());
        let (eg, _, _) = op_restriction_eg();

        let (log, _) = op_restriction_run(&eg, "(f0 (hub z) y)", OpFilterPolicy::Adaptive);
        assert_eq!(
            log,
            vec![OpRestriction::Filter, OpRestriction::Leapfrog],
            "4 parents against a relation of {} must filter and 40 must not",
            4 * OP_FILTER_RELATION_PER_CANDIDATE
        );

        // Against a relation of forty, neither bucket is small enough to make
        // the test worth its per-candidate load.
        let (log, _) = op_restriction_run(&eg, "(f1 (hub z) y)", OpFilterPolicy::Adaptive);
        assert_eq!(log, vec![OpRestriction::Leapfrog; 2]);

        set_op_filter_policy(OpFilterPolicy::Adaptive);
    }

    /// The two mechanisms return the same match set on both shapes.
    ///
    /// The demotion's soundness argument is the identity
    /// `by_op[o] ∩ B = { n ∈ B : op(n) = o }` over one index build; this is that
    /// identity checked on the shapes the policy sends each way, so a change
    /// that moves the rule cannot also change what the matcher returns.
    #[test]
    fn op_restriction_mechanisms_agree_on_the_match_set() {
        let _pin = OP_FILTER_PIN.lock().unwrap_or_else(|e| e.into_inner());
        let (eg, _, _) = op_restriction_eg();
        for src in ["(f0 (hub z) y)", "(f1 (hub z) y)", "(f0 x y)"] {
            let (_, adaptive) = op_restriction_run(&eg, src, OpFilterPolicy::Adaptive);
            let (fl, filter) = op_restriction_run(&eg, src, OpFilterPolicy::AlwaysFilter);
            let (ll, leapfrog) = op_restriction_run(&eg, src, OpFilterPolicy::AlwaysLeapfrog);
            assert_eq!(adaptive, filter, "{src}: filter changed the match set");
            assert_eq!(adaptive, leapfrog, "{src}: leapfrog changed the match set");
            assert!(!adaptive.is_empty(), "{src}: shape must match something");
            // `(f0 x y)` is a one-lookup join: no `ByOp` to place, no decision.
            if src == "(f0 x y)" {
                assert!(fl.is_empty() && ll.is_empty());
            }
        }
        set_op_filter_policy(OpFilterPolicy::Adaptive);
    }
}
