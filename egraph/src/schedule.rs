// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Query scheduler: order variables and assign index constraints.
//!
//! Given a `ResolvedQuery` (OpId-based), produce a `QueryPlan` that
//! tells the execution engine which variable to bind next and how.

use crate::ast::{GlobalVarId, LitValVarId, MsetVarId, SeqVarId, SetVarId, VarId};
use crate::containers::{DenseId, IndexLike};
use crate::resolve::{MatchShape, PatVar, PredGuard, RAtom, RMult, ResolvedQuery};
use std::cell::Cell;
use std::hash::Hash;

// ---------------------------------------------------------------------------
// Index lookups — each produces a SortedVec<G> for leapfrog
// ---------------------------------------------------------------------------

/// `I` is the child-position word: [`EGraphConfig::Index`], the same width the
/// e-graph indexes its child pool with. A position is an offset into one node's
/// children, so its range is the node's arity, and a variadic node's arity is a
/// span in that pool — bounded by `I` and by nothing narrower. Hard-coding `u32`
/// here would cap a 63-bit session's node arity at 2^32 children, and the cap
/// would be reached silently: the counter in [`IndexStore::build`] wrapped, and
/// the child at position 2^32 landed in bucket 0, where it would match patterns
/// written for the first argument.
///
/// [`EGraphConfig::Index`]: crate::config::EGraphConfig::Index
/// [`IndexStore::build`]: crate::index::IndexStore::build
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IndexLookup<O, I> {
    ByOp { op: O },
    ByChildPos { child: PatVar, pos: I },
    ByRepr { repr: VarId },
    ByContains { child: PatVar },
}

// ---------------------------------------------------------------------------
// Execution steps
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step<O, I, V> {
    Join {
        target: VarId,
        lookups: Vec<IndexLookup<O, I>>,
        /// Stable atom index in the compile-time numbering. Bridges the
        /// fixed atom order (which defines semi-naive variants) to the
        /// dynamic execution order chosen by the scheduler. Not used by
        /// the naive matcher; consumed by semi-naive variant dispatch.
        atom_id: usize,
    },
    ExtractChild {
        target: VarId,
        parent: VarId,
        /// Child position, `I`-wide for the same reason as
        /// [`IndexLookup::ByChildPos`]: it is read back through
        /// `EGraph::child_at`, which offsets into the node's span in the child pool.
        pos: I,
    },
    CheckChildEq {
        parent: VarId,
        pos: I,
        expected: PatVar,
    },
    CheckEq {
        a: VarId,
        b: VarId,
    },
    CheckEqGlobal {
        local: VarId,
        global: GlobalVarId,
    },
    /// Bind an as-yet unbound variable to a global's class. The dual of
    /// `CheckEqGlobal`: an `(= x g)` atom CHECKS when `x` already has a value
    /// and BINDS when it does not. Without this a rule whose only atom is such
    /// an equality compiles to a plan that binds nothing, and materializing a
    /// match then reads an unset variable.
    BindGlobal {
        target: VarId,
        global: GlobalVarId,
    },
    CopyBinding {
        target: VarId,
        other: VarId,
    },
    ExpandA {
        node: VarId,
        children: Vec<PatVar>,
        pre: Option<SeqVarId>,
        suf: Option<SeqVarId>,
    },
    DecomposeAC {
        node: VarId,
        elems: Vec<(PatVar, RMult)>,
        rest: Option<MsetVarId>,
        idempotent: bool,
    },
    DecomposeACI {
        node: VarId,
        elems: Vec<PatVar>,
        rest: Option<SetVarId>,
    },
    ExtractLitVal {
        node: VarId,
        val: LitValVarId,
    },
    /// Keep the match only if `node`'s literal payload equals `value`. The constant
    /// counterpart of [`Step::ExtractLitVal`]: that one binds the payload to a pattern
    /// variable, this one pins it to a literal written in the pattern.
    CheckLit {
        node: VarId,
        value: V,
    },
    /// Keep the match only if the guard evaluates to a true boolean over the literal
    /// values bound so far.
    CheckPred {
        guard: PredGuard<O, V>,
    },
}

#[derive(Clone, Debug)]
pub struct QueryPlan<O, I, V> {
    pub steps: Vec<Step<O, I, V>>,
    pub shape: MatchShape,
}

// ---------------------------------------------------------------------------
// Stats
// ---------------------------------------------------------------------------

pub struct IndexStats<O: Eq + Hash> {
    /// Per-op driver-scan cardinality (`|by_op[op]|`). The base estimate for an
    /// atom when no per-atom override is present — correct for naive matching,
    /// where every atom of an op reads the same full bucket.
    pub op_card: std::collections::HashMap<O, usize>,
    /// Measured mean fan-out of each access path, from the round's index build.
    /// The default is all-unmeasured, which prices every bound key at the fixed
    /// halving this model replaces; see `path_selectivity`.
    pub fanouts: crate::index::FanOuts<O>,
    /// Per-atom (`atom_id`) driver-scan cardinality, overriding `op_card` for
    /// that atom. Needed for semi-naive: an atom's base cardinality is set by
    /// its **mode** (delta / full / full∖delta), which is per-atom, not per-op —
    /// two atoms with the same op can have different modes in one flavor (e.g.
    /// `(f (f x y) z)` variant 1: atom 0 is full∖delta, atom 1 is delta, both
    /// op `f`). `op_card` cannot represent that; `atom_card` can.
    pub atom_card: std::collections::HashMap<usize, usize>,
}

impl<O: Eq + Hash> Default for IndexStats<O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: Eq + Hash> IndexStats<O> {
    pub fn new() -> Self {
        Self {
            op_card: std::collections::HashMap::new(),
            atom_card: std::collections::HashMap::new(),
            fanouts: crate::index::FanOuts::default(),
        }
    }
}

impl<O: Eq + Hash + Copy> IndexStats<O> {
    pub fn from_index<Cfg>(index: &crate::index::IndexStore<Cfg>) -> Self
    where
        Cfg: crate::config::EGraphConfig<O = O>,
        crate::canon::MSetCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
    {
        Self {
            op_card: index.op_cardinalities().collect(),
            atom_card: std::collections::HashMap::new(),
            fanouts: index.fanouts.clone(),
        }
    }
}

// ---------------------------------------------------------------------------
// Scheduler
// ---------------------------------------------------------------------------

/// A child position in the plan's index word.
///
/// The argument is a *pattern's* arity, authored in a rewrite rule, so in practice a
/// handful — but the value is compared against and used to offset into positions the
/// e-graph assigns to real nodes ([`IndexStore::build`], [`EGraph::child_at`]), whose
/// range is the child pool's. Narrowing it silently would probe or read the wrong
/// argument, so it is checked rather than cast.
///
/// [`IndexStore::build`]: crate::index::IndexStore::build
/// [`EGraph::child_at`]: crate::egraph::EGraph::child_at
fn child_pos<I: IndexLike>(pos: usize) -> I {
    I::try_from_usize(pos)
        .expect("pattern child position exceeds EGraphConfig::Index; configure a wider index word")
}

fn pv_is_bound(pv: &PatVar, bound: &[bool]) -> bool {
    match pv {
        PatVar::Local(vid) => bound[vid.idx()],
        PatVar::Global(_) => true,
    }
}

fn pv_mark_bound(pv: &PatVar, bound: &mut [bool]) {
    if let PatVar::Local(vid) = pv {
        bound[vid.idx()] = true;
    }
}

/// Base driver-scan cardinality for an atom: its per-atom override
/// (`atom_card[atom_id]`, set per semi-naive flavor) if present, else the
/// per-op bucket size (`op_card[op]`, the naive default).
fn base_card<O: Eq + Hash>(op: &O, atom_id: usize, stats: &IndexStats<O>) -> usize {
    stats
        .atom_card
        .get(&atom_id)
        .copied()
        .or_else(|| stats.op_card.get(op).copied())
        .unwrap_or(usize::MAX)
}

/// Fraction of an atom's relation that survives intersecting one index bucket.
///
/// `fanout` is the bucket size a probe on that path lands in, measured by
/// [`FanOuts`](crate::index::FanOuts), and `denom` the relation the bucket
/// filters: `|by_op[op]|` for `by_child_pos` and `by_contains`, the whole
/// indexed node count for `by_repr`. The ratio replaces a fixed halving
/// heuristic that cannot distinguish access paths. The concrete values in the
/// scheduler regression below are a captured fixture, not branch-tip workload
/// statistics.
///
/// Falls back to the halving when the path was never measured, which is every
/// call from [`schedule`], the stats-free entry point.
fn path_selectivity(fanout: Option<f64>, denom: usize) -> f64 {
    match fanout {
        Some(f) if denom > 0 => (f / denom as f64).clamp(0.0, 1.0),
        _ => 0.5,
    }
}

// ---------------------------------------------------------------------------
// Sampled cross-index selectivity
// ---------------------------------------------------------------------------

/// Where in an emitter atom's node a variable that atom bound sits.
///
/// The scheduler needs it to reproduce, at plan time, the key a later atom's
/// probe will be handed at run time: the runtime key is the class of the
/// emitter node's child at some position, so a sample of emitter nodes plus a
/// site is a sample of probe keys.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum KeySite {
    /// The node variable itself; the key is the node's own class.
    Node,
    /// The child at this position of a fixed-arity node.
    Child(usize),
    /// An element of a variadic node, which has no fixed position: the
    /// decomposition binds the variable to each element in turn, so every
    /// child of the node is an equally likely key.
    Element,
}

/// The access path a candidate atom's join opens for one bound key.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ProbePath {
    /// `by_child_pos[(key, pos)]`, restricted to the atom's operator.
    ChildPos(usize),
    /// `by_contains[key]`, restricted to the atom's operator.
    Contains,
}

/// Knobs for sampled cross-index selectivity; see [`set_sampled_selectivity`].
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SamplerConfig {
    /// Emitter nodes drawn per estimate.
    pub k: usize,
    /// Bootstrap resamples used to guard the estimate. `0` disables the guard.
    pub bootstrap: usize,
    /// Coefficient of variation of the bootstrap mean above which the estimate
    /// is discarded for the size-biased mean.
    pub cv_threshold: f64,
}

impl Default for SamplerConfig {
    fn default() -> Self {
        Self {
            k: 32,
            bootstrap: 0,
            cv_threshold: 1.0,
        }
    }
}

thread_local! {
    /// Sampling configuration, or `None` for the size-biased mean model.
    ///
    /// Thread-local for the same reason as `ematch::RUNTIME_SCHEDULING`: it is
    /// read once per scheduled query rather than on a per-candidate path, and
    /// the differential tests run one plan with it on against another with it
    /// off, which a process-wide flag would make order-dependent under the test
    /// harness's thread pool.
    static SAMPLED_SELECTIVITY: Cell<Option<SamplerConfig>> = const { Cell::new(None) };
}

/// Price a bound key by sampling the emitter's relation instead of by the
/// round's size-biased mean fan-out. Off by default.
///
/// The mean assumes the emitter's key distribution mirrors the probed index's
/// marginal. It does not have to: an emitter whose nodes point only at leaf
/// classes never probes the hub buckets that dominate the mean, and the mean
/// then over-prices the probe by the hub's size. Sampling reads the joint
/// distribution directly — draw emitter nodes, extract the keys they expose,
/// read the buckets those keys actually select. See design chapter 20.
pub fn set_sampled_selectivity(cfg: Option<SamplerConfig>) {
    SAMPLED_SELECTIVITY.with(|c| c.set(cfg));
}

/// The sampling configuration in force on this thread, if any.
pub fn sampled_selectivity() -> Option<SamplerConfig> {
    SAMPLED_SELECTIVITY.with(|c| c.get())
}

thread_local! {
    /// Estimates taken, and estimates the bootstrap guard sent back to the
    /// size-biased mean.
    static SAMPLE_TALLY: Cell<(u64, u64)> = const { Cell::new((0, 0)) };
}

/// `(estimates taken, estimates the bootstrap guard rejected)` since the last
/// [`reset_sample_tally`].
///
/// The guard is the only part of the estimator whose effect is invisible in the
/// plan — a rejected estimate produces the order the mean model would have
/// produced anyway — so whether it fires on a given workload is a question only
/// a counter answers. Incremented on the sampling path alone, so the flag-off
/// scheduler does not touch it.
pub fn sample_tally() -> (u64, u64) {
    SAMPLE_TALLY.with(|c| c.get())
}

/// Zero the counters [`sample_tally`] reports.
pub fn reset_sample_tally() {
    SAMPLE_TALLY.with(|c| c.set((0, 0)));
}

fn tally(rejected: bool) {
    SAMPLE_TALLY.with(|c| {
        let (t, r) = c.get();
        c.set((t + 1, r + u64::from(rejected)));
    });
}

/// Plan-time read access to the round's buckets, for sampled selectivity.
///
/// A trait, and phrased in `usize` ids, so that the scheduler stays generic
/// over the operator alone: threading the e-graph's whole configuration through
/// [`IndexStats`] would put a second type parameter and a lifetime on every
/// signature that carries stats. [`IndexSampler`](crate::index::IndexSampler)
/// is the one implementation.
pub trait CrossSampler<O> {
    /// Up to `k` node ids of the slice atom `atom_id` will enumerate, in
    /// ascending id order.
    ///
    /// The draw is an even stride over the sorted bucket rather than a random
    /// sample: a plan must be a function of the e-graph and the rule, and
    /// nothing else, so that a run is reproducible and a differential test can
    /// compare two engines on the same order.
    fn driver_sample(&self, atom_id: usize, op: O, k: usize, out: &mut Vec<usize>);

    /// The classes a variable bound at `site` takes for emitter node `node`.
    /// One class for [`KeySite::Node`] and [`KeySite::Child`]; for
    /// [`KeySite::Element`], every distinct class among the node's children.
    fn key_classes(&self, node: usize, site: KeySite, out: &mut Vec<usize>);

    /// Nodes of operator `op` in the bucket `path` selects for `class` — the
    /// candidate count the join's intersection with `by_op[op]` can propose.
    fn probe_len(&self, class: usize, path: ProbePath, op: O) -> usize;
}

/// One sampled estimate's cache key: emitter atom, the site it binds the
/// variable at, and the probe the candidate atom would make.
type SampleKey = (usize, KeySite, usize, ProbePath);

/// Sampling state for one [`schedule_with_stats_sampled`] call: the emitter
/// draws and the finished estimates, both memoized because the greedy loop
/// re-costs every unused atom after each choice and the index does not move
/// underneath it.
struct Sampling<'a, O> {
    sampler: &'a dyn CrossSampler<O>,
    cfg: SamplerConfig,
    drivers: Vec<(usize, Vec<usize>)>,
    memo: Vec<(SampleKey, Option<f64>)>,
    classes: Vec<usize>,
    draws: Vec<f64>,
    means: Vec<f64>,
}

impl<'a, O: DenseId + Copy> Sampling<'a, O> {
    fn new(sampler: &'a dyn CrossSampler<O>, cfg: SamplerConfig) -> Self {
        Self {
            sampler,
            cfg,
            drivers: Vec::new(),
            memo: Vec::new(),
            classes: Vec::new(),
            draws: Vec::new(),
            means: Vec::new(),
        }
    }

    /// Index of `atom_id`'s emitter draw, taking it if this is the first ask.
    fn driver(&mut self, atom_id: usize, op: O) -> usize {
        if let Some(i) = self.drivers.iter().position(|(a, _)| *a == atom_id) {
            return i;
        }
        let mut nodes = Vec::new();
        self.sampler
            .driver_sample(atom_id, op, self.cfg.k, &mut nodes);
        self.drivers.push((atom_id, nodes));
        self.drivers.len() - 1
    }

    /// Mean bucket length the candidate's probe returns over the emitter's
    /// sampled keys, or `None` when the emitter's slice is empty or the
    /// bootstrap guard rejects the draw.
    fn estimate(
        &mut self,
        emitter: usize,
        emitter_op: O,
        site: KeySite,
        path: ProbePath,
        probe_op: O,
    ) -> Option<f64> {
        let key: SampleKey = (emitter, site, probe_op.to_usize(), path);
        if let Some((_, v)) = self.memo.iter().find(|(k, _)| *k == key) {
            return *v;
        }
        let v = self.measure(emitter, emitter_op, site, path, probe_op);
        self.memo.push((key, v));
        v
    }

    fn measure(
        &mut self,
        emitter: usize,
        emitter_op: O,
        site: KeySite,
        path: ProbePath,
        probe_op: O,
    ) -> Option<f64> {
        let di = self.driver(emitter, emitter_op);
        // Taken out and put back so the per-sample scratch below can be
        // borrowed mutably while the draw is read.
        let nodes = std::mem::take(&mut self.drivers[di].1);
        let out = self.sample_draws(&nodes, site, path, probe_op);
        self.drivers[di].1 = nodes;
        out
    }

    fn sample_draws(
        &mut self,
        nodes: &[usize],
        site: KeySite,
        path: ProbePath,
        probe_op: O,
    ) -> Option<f64> {
        if nodes.is_empty() {
            return None;
        }
        self.draws.clear();
        for &n in nodes {
            self.classes.clear();
            self.sampler.key_classes(n, site, &mut self.classes);
            if self.classes.is_empty() {
                continue;
            }
            // Every class the site can take is an equally likely key, which is
            // one class except under `Element`, where the decomposition binds
            // the variable to each element of the node in turn.
            let sum: usize = self
                .classes
                .iter()
                .map(|&c| self.sampler.probe_len(c, path, probe_op))
                .sum();
            self.draws.push(sum as f64 / self.classes.len() as f64);
        }
        if self.draws.is_empty() {
            return None;
        }
        let mean = self.draws.iter().sum::<f64>() / self.draws.len() as f64;
        let rejected = self.cfg.bootstrap > 0 && !self.bootstrap_ok(mean);
        tally(rejected);
        if rejected { None } else { Some(mean) }
    }

    /// Resample the draws with replacement and reject the estimate when the
    /// resampled means scatter too far.
    ///
    /// The stride is deterministic but arbitrary with respect to the key
    /// distribution, so a draw can miss a mode that dominates the true mean.
    /// The bootstrap prices that risk from the draw itself: a sample whose mean
    /// is stable under resampling is one the stride did not decide. The
    /// generator is a fixed-seed SplitMix64, so the verdict is a function of the
    /// draw and plans stay reproducible.
    fn bootstrap_ok(&mut self, mean: f64) -> bool {
        if mean <= 0.0 {
            // A draw of all zeros has no scale to be uncertain on, and its
            // relative spread is 0/0. The estimate is exact: no key the emitter
            // produces selects anything.
            return self.draws.iter().all(|&d| d == 0.0);
        }
        let n = self.draws.len();
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        self.means.clear();
        for _ in 0..self.cfg.bootstrap {
            let mut acc = 0.0;
            for _ in 0..n {
                acc += self.draws[(splitmix64(&mut state) % n as u64) as usize];
            }
            self.means.push(acc / n as f64);
        }
        let b = self.means.len() as f64;
        let bmean = self.means.iter().sum::<f64>() / b;
        let var = self
            .means
            .iter()
            .map(|m| (m - bmean) * (m - bmean))
            .sum::<f64>()
            / b;
        var.sqrt() / mean <= self.cfg.cv_threshold
    }
}

/// SplitMix64, the reference generator for the bootstrap resample.
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// The atom each variable was bound by, and where in that atom's node it sits.
type Emitters = Vec<Option<(usize, KeySite)>>;

/// Record every variable the atoms newly lowered by this step bind, first
/// writer winning — the atom that binds a variable is the first lowered atom
/// that mentions it, and later atoms only re-check it.
fn record_emitters<O, S, V>(
    atoms: &[RAtom<O, S, V>],
    before: &[bool],
    used: &[bool],
    em: &mut Emitters,
) {
    fn set(em: &mut Emitters, v: usize, src: (usize, KeySite)) {
        if em[v].is_none() {
            em[v] = Some(src);
        }
    }
    fn set_pv(em: &mut Emitters, pv: &PatVar, src: (usize, KeySite)) {
        if let PatVar::Local(v) = pv {
            set(em, v.idx(), src);
        }
    }
    for (ai, atom) in atoms.iter().enumerate() {
        if used[ai] == before[ai] {
            continue;
        }
        match atom {
            RAtom::Plain { node, children, .. } => {
                set(em, (*node).idx(), (ai, KeySite::Node));
                for (pos, cv) in children.iter().enumerate() {
                    set_pv(em, cv, (ai, KeySite::Child(pos)));
                }
            }
            RAtom::AExact { node, children, .. } => {
                set(em, (*node).idx(), (ai, KeySite::Node));
                for cv in children {
                    set_pv(em, cv, (ai, KeySite::Element));
                }
            }
            RAtom::APrefix { node, fixed, .. }
            | RAtom::ASuffix { node, fixed, .. }
            | RAtom::ABoth { node, fixed, .. } => {
                set(em, (*node).idx(), (ai, KeySite::Node));
                for cv in fixed {
                    set_pv(em, cv, (ai, KeySite::Element));
                }
            }
            RAtom::ACExact { node, elems, .. } | RAtom::ACSub { node, elems, .. } => {
                set(em, (*node).idx(), (ai, KeySite::Node));
                for (ev, _) in elems {
                    set_pv(em, ev, (ai, KeySite::Element));
                }
            }
            RAtom::ACIExact { node, elems, .. } | RAtom::ACISub { node, elems, .. } => {
                set(em, (*node).idx(), (ai, KeySite::Node));
                for ev in elems {
                    set_pv(em, ev, (ai, KeySite::Element));
                }
            }
            RAtom::Lit { node, .. } | RAtom::LitBind { node, .. } => {
                set(em, (*node).idx(), (ai, KeySite::Node))
            }
            // `CopyBinding` propagates a binding rather than producing one, so
            // the copy's emitter is the original's.
            RAtom::Eq(a, b) => {
                if em[(*a).idx()].is_none() {
                    em[(*a).idx()] = em[(*b).idx()];
                } else if em[(*b).idx()].is_none() {
                    em[(*b).idx()] = em[(*a).idx()];
                }
            }
            // A guard binds nothing, so it emits nothing.
            RAtom::EqGlobal(..) | RAtom::Pred { .. } => {}
        }
    }
}

/// The relation an atom scans, for the emitter draw. Mirrors
/// [`saturate::atom_op`](crate::saturate::atom_op) — the same partition into
/// scanning and non-scanning atoms the semi-naive decomposition uses.
fn emitter_op<O: Copy, S, V>(atom: &RAtom<O, S, V>) -> Option<O> {
    crate::saturate::atom_op(atom)
}

/// Everything the cost model reads: the round's aggregates, which atom bound
/// each variable, and the sampler when it is on.
struct Cost<'a, O: Eq + Hash> {
    stats: &'a IndexStats<O>,
    emitters: Emitters,
    sampling: Option<Sampling<'a, O>>,
}

impl<'a, O: DenseId + Hash + Copy> Cost<'a, O> {
    /// Sampled fan-out of one bound key of a candidate atom, or `None` when
    /// sampling is off, the key was not bound by a scheduled atom (a global, or
    /// a variable an eager step produced from one), or the guard rejected it.
    fn sampled<S, V>(
        &mut self,
        atoms: &[RAtom<O, S, V>],
        key: &PatVar,
        path: ProbePath,
        probe_op: O,
    ) -> Option<f64> {
        let PatVar::Local(v) = key else { return None };
        let (emitter, site) = (*self.emitters.get(v.idx())?)?;
        let emitter_op = emitter_op(atoms.get(emitter)?)?;
        self.sampling
            .as_mut()?
            .estimate(emitter, emitter_op, site, path, probe_op)
    }
}

/// Expected number of candidate nodes an atom's join enumerates, given which
/// of its keys the scheduler has already bound.
///
/// The join drives from `by_op[op]` — or, under semi-naive, from the slice of
/// it the atom's mode reads, which is what [`base_card`] returns — and
/// intersects one bucket per bound key. Each intersection multiplies in the
/// measured selectivity of its access path, so `k` bound keys multiply `k`
/// measured fractions where the previous model multiplied `k` halves. Two
/// consequences the halving did not have: the estimate for one bound key is
/// the size of the bucket that key's probe lands in rather than half the
/// relation, and a delta-restricted atom is priced by the delta's cardinality
/// at any position of the order, not only when it drives the scan.
///
/// The three paths follow `emit_atom`: a `Plain` atom intersects
/// `by_child_pos` per bound child, every variadic atom (A*/AC*/ACI*, including
/// `AExact`) intersects `by_contains` per bound element, and an atom whose
/// node variable is already bound re-joins within its class through `by_repr`.
fn estimate_cost<O: DenseId + Hash + Copy, S, V>(
    atoms: &[RAtom<O, S, V>],
    atom_id: usize,
    bound: &[bool],
    ctx: &mut Cost<'_, O>,
) -> f64 {
    let atom = &atoms[atom_id];
    let stats = ctx.stats;
    match atom {
        RAtom::Plain { node, op, children } => {
            if bound[(*node).idx()] {
                return by_repr_cost(op, atom_id, stats);
            }
            let full = stats.op_card.get(op).copied().unwrap_or(0);
            let mut cost = base_card(op, atom_id, stats) as f64;
            for (pos, cv) in children.iter().enumerate() {
                if pv_is_bound(cv, bound) {
                    let f = ctx
                        .sampled(atoms, cv, ProbePath::ChildPos(pos), *op)
                        .or_else(|| ctx.stats.fanouts.by_child_pos.get(&(*op, pos)).copied());
                    cost *= path_selectivity(f, full);
                }
            }
            cost
        }
        RAtom::AExact { node, op, children } => {
            by_contains_cost(atoms, node, op, atom_id, children, bound, ctx)
        }
        RAtom::APrefix {
            node, op, fixed, ..
        }
        | RAtom::ASuffix {
            node, op, fixed, ..
        }
        | RAtom::ABoth {
            node, op, fixed, ..
        } => by_contains_cost(atoms, node, op, atom_id, fixed, bound, ctx),
        RAtom::ACExact { node, op, elems }
        | RAtom::ACSub {
            node, op, elems, ..
        } => {
            let evs: Vec<PatVar> = elems.iter().map(|(ev, _)| *ev).collect();
            by_contains_cost(atoms, node, op, atom_id, &evs, bound, ctx)
        }
        RAtom::ACIExact { node, op, elems }
        | RAtom::ACISub {
            node, op, elems, ..
        } => by_contains_cost(atoms, node, op, atom_id, elems, bound, ctx),
        RAtom::Lit { op, .. } | RAtom::LitBind { op, .. } => base_card(op, atom_id, stats) as f64,
        RAtom::Eq(..) | RAtom::EqGlobal(..) | RAtom::Pred { .. } => 0.0,
    }
}

/// Cost of re-joining an atom whose node variable is already bound: the class's
/// nodes, intersected with the op's. The denominator is every indexed node,
/// because a class holds nodes of every op.
fn by_repr_cost<O: Eq + Hash>(op: &O, atom_id: usize, stats: &IndexStats<O>) -> f64 {
    let sel = path_selectivity(Some(stats.fanouts.by_repr), stats.fanouts.nodes);
    base_card(op, atom_id, stats) as f64 * sel
}

/// Cost of a variadic atom's join: `by_contains` per bound element, or the
/// class re-join when the node variable itself is bound (`emit_variadic_join`
/// emits one or the other).
#[allow(clippy::too_many_arguments)]
fn by_contains_cost<O: DenseId + Hash + Copy, S, V>(
    atoms: &[RAtom<O, S, V>],
    node: &VarId,
    op: &O,
    atom_id: usize,
    elems: &[PatVar],
    bound: &[bool],
    ctx: &mut Cost<'_, O>,
) -> f64 {
    if bound[(*node).idx()] {
        return by_repr_cost(op, atom_id, ctx.stats);
    }
    let full = ctx.stats.op_card.get(op).copied().unwrap_or(0);
    let mut cost = base_card(op, atom_id, ctx.stats) as f64;
    for e in elems {
        if pv_is_bound(e, bound) {
            let f = ctx
                .sampled(atoms, e, ProbePath::Contains, *op)
                .or_else(|| ctx.stats.fanouts.by_contains.get(op).copied());
            cost *= path_selectivity(f, full);
        }
    }
    cost
}

pub fn schedule<O: DenseId + Hash + Copy, S: DenseId + Copy, V: Clone, I: IndexLike>(
    rq: &ResolvedQuery<O, S, V>,
) -> QueryPlan<O, I, V> {
    schedule_with_stats(rq, &IndexStats::new())
}

pub fn schedule_with_stats<O: DenseId + Hash + Copy, S: DenseId + Copy, V: Clone, I: IndexLike>(
    rq: &ResolvedQuery<O, S, V>,
    stats: &IndexStats<O>,
) -> QueryPlan<O, I, V> {
    schedule_inner(rq, stats, None)
}

/// [`schedule_with_stats`] with plan-time access to the round's buckets, so
/// that a bound key can be priced by sampling the emitter's relation rather
/// than by the round's mean fan-out.
///
/// Whether it does is [`set_sampled_selectivity`]'s to decide: with the flag
/// off this is `schedule_with_stats` and `sampler` is never called, so a caller
/// that always has a sampler in hand needs no branch of its own.
pub fn schedule_with_stats_sampled<
    O: DenseId + Hash + Copy,
    S: DenseId + Copy,
    V: Clone,
    I: IndexLike,
>(
    rq: &ResolvedQuery<O, S, V>,
    stats: &IndexStats<O>,
    sampler: &dyn CrossSampler<O>,
) -> QueryPlan<O, I, V> {
    schedule_inner(rq, stats, sampled_selectivity().map(|cfg| (sampler, cfg)))
}

fn schedule_inner<O: DenseId + Hash + Copy, S: DenseId + Copy, V: Clone, I: IndexLike>(
    rq: &ResolvedQuery<O, S, V>,
    stats: &IndexStats<O>,
    sampling: Option<(&dyn CrossSampler<O>, SamplerConfig)>,
) -> QueryPlan<O, I, V> {
    let mut bound = vec![false; rq.shape.num_vars()];
    let mut steps = Vec::new();
    let mut used = vec![false; rq.atoms.len()];
    let mut ctx = Cost {
        stats,
        emitters: vec![None; rq.shape.num_vars()],
        sampling: sampling.map(|(s, cfg)| Sampling::new(s, cfg)),
    };
    let mut before = used.clone();
    loop {
        // Eager pass: Eq, Lit, already-bound nodes.
        lower_eager(&rq.atoms, &mut used, &mut bound, &mut steps);
        record_emitters(&rq.atoms, &before, &used, &mut ctx.emitters);
        before.copy_from_slice(&used);

        // Pick the cheapest unprocessed atom.
        // The estimate is an expected cardinality, so it is compared as an
        // `f64`: rounding it to an integer would tie every selective atom at 0.
        // Every value is finite (`path_selectivity` guards its divisor), and the
        // fold replaces only on a strict improvement, so equal minima keep the
        // lowest atom index and the choice is a function of the atom order.
        // Costs are taken once per atom per pass rather than inside a
        // comparator, which under sampling would redraw them per comparison.
        let mut best: Option<(usize, f64)> = None;
        for ai in 0..rq.atoms.len() {
            if used[ai]
                || matches!(
                    &rq.atoms[ai],
                    RAtom::Eq(..) | RAtom::EqGlobal(..) | RAtom::Pred { .. }
                )
            {
                continue;
            }
            let c = estimate_cost(&rq.atoms, ai, &bound, &mut ctx);
            if best.is_none_or(|(_, b)| c < b) {
                best = Some((ai, c));
            }
        }

        let Some((ai, _)) = best else { break };
        emit_atom(&rq.atoms[ai], ai, &mut bound, &mut steps);
        used[ai] = true;
        record_emitters(&rq.atoms, &before, &used, &mut ctx.emitters);
        before.copy_from_slice(&used);
    }

    if dump_plan_enabled() {
        dump_plan(&steps, rq.atoms.len());
    }
    QueryPlan {
        steps,
        shape: rq.shape.clone(),
    }
}

/// Whether `EGRAPH_DUMP_PLAN` is set, read once. The variable is read at the first
/// scheduled query and cached, so an unset environment costs one relaxed load per plan.
fn dump_plan_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("EGRAPH_DUMP_PLAN").is_some())
}

/// Print the scheduled plan to stderr, one line per step, in the form chapter 8's
/// "Example Plan" section uses. Variables are printed by their resolved index, so a
/// step's `v3` is variable 3 of the query's `MatchShape`.
///
/// This is the diagnostic the pre-bound-child defect in `ematch.rs` was found with: the
/// dump showed a `Join` keyed on `v0` scheduled after an `ExpandA` that listed `v0`
/// among its fixed children, which is the order that made the expansion's cleanup unbind
/// a variable the join then read.
fn dump_plan<O: std::fmt::Debug, I: std::fmt::Debug, V>(steps: &[Step<O, I, V>], atoms: usize) {
    eprintln!("=== plan: {} atoms, {} steps ===", atoms, steps.len());
    for (i, st) in steps.iter().enumerate() {
        eprintln!("step[{i}]: {}", fmt_step(st));
    }
}

fn fmt_step<O: std::fmt::Debug, I: std::fmt::Debug, V>(st: &Step<O, I, V>) -> String {
    match st {
        Step::BindGlobal { target, global } => {
            format!("BindGlobal target=v{} global={global:?}", target.idx())
        }
        Step::Join {
            target,
            lookups,
            atom_id,
        } => format!(
            "Join target=v{} atom={atom_id} lookups={lookups:?}",
            target.idx()
        ),
        Step::ExtractChild {
            target,
            parent,
            pos,
        } => format!(
            "ExtractChild target=v{} parent=v{} pos={pos:?}",
            target.idx(),
            parent.idx()
        ),
        Step::CheckChildEq {
            parent,
            pos,
            expected,
        } => format!(
            "CheckChildEq parent=v{} pos={pos:?} expected={expected:?}",
            parent.idx()
        ),
        Step::CheckEq { a, b } => format!("CheckEq v{} v{}", a.idx(), b.idx()),
        Step::CheckEqGlobal { local, global } => {
            format!("CheckEqGlobal v{} global={global:?}", local.idx())
        }
        Step::CopyBinding { target, other } => {
            format!("CopyBinding target=v{} from=v{}", target.idx(), other.idx())
        }
        Step::ExpandA {
            node,
            children,
            pre,
            suf,
        } => format!(
            "ExpandA node=v{} children={children:?} pre={pre:?} suf={suf:?}",
            node.idx()
        ),
        Step::DecomposeAC {
            node,
            elems,
            rest,
            idempotent,
        } => format!(
            "DecomposeAC node=v{} elems={elems:?} rest={rest:?} idempotent={idempotent}",
            node.idx()
        ),
        Step::DecomposeACI { node, elems, rest } => format!(
            "DecomposeACI node=v{} elems={elems:?} rest={rest:?}",
            node.idx()
        ),
        Step::ExtractLitVal { node, val } => {
            format!("ExtractLitVal node=v{} val={val:?}", node.idx())
        }
        Step::CheckLit { node, .. } => format!("CheckLit node=v{}", node.idx()),
        Step::CheckPred { .. } => "CheckPred".to_string(),
    }
}

fn emit_read_children<O: DenseId + Hash + Copy, S, V, I: IndexLike>(
    atom: &RAtom<O, S, V>,
    bound: &mut [bool],
    steps: &mut Vec<Step<O, I, V>>,
) {
    if let RAtom::Plain { node, children, .. } = atom {
        for (pos, &cv) in children.iter().enumerate() {
            if !pv_is_bound(&cv, bound) {
                let PatVar::Local(vid) = cv else {
                    unreachable!()
                };
                steps.push(Step::ExtractChild {
                    target: vid,
                    parent: *node,
                    pos: child_pos::<I>(pos),
                });
                pv_mark_bound(&cv, bound);
            } else {
                steps.push(Step::CheckChildEq {
                    parent: *node,
                    pos: child_pos::<I>(pos),
                    expected: cv,
                });
            }
        }
    }
}

/// Run the eager pass to fixpoint: lower every atom the current bindings make
/// free (see [`try_eager_lower`]), marking each one used and binding whatever it
/// binds, until no unused atom is free any more.
///
/// Shared by the static scheduler's Phase A and the runtime-scheduled matcher,
/// which reaches the same fixpoint at each of its decision points before it
/// costs the remaining atoms.
pub(crate) fn lower_eager<O: DenseId + Hash + Copy, S, V: Clone, I: IndexLike>(
    atoms: &[RAtom<O, S, V>],
    used: &mut [bool],
    bound: &mut [bool],
    steps: &mut Vec<Step<O, I, V>>,
) {
    let mut progress = true;
    while progress {
        progress = false;
        for ai in 0..atoms.len() {
            if used[ai] {
                continue;
            }
            // A guard is free exactly when the atoms binding its values have run.
            // That is a condition on `used`, not on `bound`, and it has to be: the
            // node variable of a `LitBind` atom is bound by the enclosing pattern's
            // `ExtractChild`, one step before the `ExtractLitVal` that fills the
            // value slot the guard reads.
            if let RAtom::Pred { guard, deps } = &atoms[ai] {
                if deps.iter().all(|d| used[*d]) {
                    steps.push(Step::CheckPred {
                        guard: guard.clone(),
                    });
                    used[ai] = true;
                    progress = true;
                }
                continue;
            }
            if let Some(eager) = try_eager_lower(&atoms[ai], ai, bound) {
                steps.extend(eager);
                used[ai] = true;
                progress = true;
            }
        }
    }
}

pub(crate) fn emit_atom<O: DenseId + Hash + Copy, S, V: Clone, I: IndexLike>(
    atom: &RAtom<O, S, V>,
    atom_id: usize,
    bound: &mut [bool],
    steps: &mut Vec<Step<O, I, V>>,
) {
    match atom {
        RAtom::Plain { node, op, children } => {
            let mut lookups = vec![IndexLookup::ByOp { op: *op }];
            for (pos, &cv) in children.iter().enumerate() {
                if pv_is_bound(&cv, bound) {
                    lookups.push(IndexLookup::ByChildPos {
                        child: cv,
                        pos: child_pos::<I>(pos),
                    });
                }
            }
            steps.push(Step::Join {
                target: *node,
                lookups,
                atom_id,
            });
            bound[(*node).idx()] = true;
            for (pos, &cv) in children.iter().enumerate() {
                if !pv_is_bound(&cv, bound) {
                    let PatVar::Local(vid) = cv else {
                        unreachable!()
                    };
                    steps.push(Step::ExtractChild {
                        target: vid,
                        parent: *node,
                        pos: child_pos::<I>(pos),
                    });
                    pv_mark_bound(&cv, bound);
                } else {
                    steps.push(Step::CheckChildEq {
                        parent: *node,
                        pos: child_pos::<I>(pos),
                        expected: cv,
                    });
                }
            }
        }
        RAtom::Lit {
            node, op, value, ..
        } => {
            if !bound[(*node).idx()] {
                steps.push(Step::Join {
                    target: *node,
                    lookups: vec![IndexLookup::ByOp { op: *op }],
                    atom_id,
                });
                bound[(*node).idx()] = true;
            }
            steps.push(Step::CheckLit {
                node: *node,
                value: value.clone(),
            });
        }
        RAtom::LitBind { node, op, val } => {
            if !bound[(*node).idx()] {
                steps.push(Step::Join {
                    target: *node,
                    lookups: vec![IndexLookup::ByOp { op: *op }],
                    atom_id,
                });
                bound[(*node).idx()] = true;
            }
            steps.push(Step::ExtractLitVal {
                node: *node,
                val: *val,
            });
        }
        // Never selected by phase B: the equalities and the guards have no join to
        // cost, and `schedule_inner`/`choose_atom` skip them for that reason. The
        // eager pass owns them.
        RAtom::Eq(..) | RAtom::EqGlobal(..) | RAtom::Pred { .. } => {}
        RAtom::AExact { node, op, children } => {
            emit_variadic_join(node, *op, atom_id, children, bound, steps);
            steps.push(Step::ExpandA {
                node: *node,
                children: children.clone(),
                pre: None,
                suf: None,
            });
            for &cv in children {
                pv_mark_bound(&cv, bound);
            }
        }
        RAtom::APrefix {
            node,
            op,
            pre,
            fixed,
        } => {
            emit_variadic_join(node, *op, atom_id, fixed, bound, steps);
            steps.push(Step::ExpandA {
                node: *node,
                children: fixed.clone(),
                pre: Some(*pre),
                suf: None,
            });
            for &cv in fixed {
                pv_mark_bound(&cv, bound);
            }
        }
        RAtom::ASuffix {
            node,
            op,
            fixed,
            suf,
        } => {
            emit_variadic_join(node, *op, atom_id, fixed, bound, steps);
            steps.push(Step::ExpandA {
                node: *node,
                children: fixed.clone(),
                pre: None,
                suf: Some(*suf),
            });
            for &cv in fixed {
                pv_mark_bound(&cv, bound);
            }
        }
        RAtom::ABoth {
            node,
            op,
            pre,
            fixed,
            suf,
        } => {
            emit_variadic_join(node, *op, atom_id, fixed, bound, steps);
            steps.push(Step::ExpandA {
                node: *node,
                children: fixed.clone(),
                pre: Some(*pre),
                suf: Some(*suf),
            });
            for &cv in fixed {
                pv_mark_bound(&cv, bound);
            }
        }
        RAtom::ACExact { node, op, elems } => {
            let evs: Vec<PatVar> = elems.iter().map(|(ev, _)| *ev).collect();
            emit_variadic_join(node, *op, atom_id, &evs, bound, steps);
            steps.push(Step::DecomposeAC {
                node: *node,
                elems: elems.clone(),
                rest: None,
                idempotent: false,
            });
            for (ev, _) in elems {
                pv_mark_bound(ev, bound);
            }
        }
        RAtom::ACSub {
            node,
            op,
            elems,
            rest,
        } => {
            let evs: Vec<PatVar> = elems.iter().map(|(ev, _)| *ev).collect();
            emit_variadic_join(node, *op, atom_id, &evs, bound, steps);
            steps.push(Step::DecomposeAC {
                node: *node,
                elems: elems.clone(),
                rest: Some(*rest),
                idempotent: false,
            });
            for (ev, _) in elems {
                pv_mark_bound(ev, bound);
            }
        }
        RAtom::ACIExact { node, op, elems } => {
            emit_variadic_join(node, *op, atom_id, elems, bound, steps);
            steps.push(Step::DecomposeACI {
                node: *node,
                elems: elems.clone(),
                rest: None,
            });
            for &ev in elems {
                pv_mark_bound(&ev, bound);
            }
        }
        RAtom::ACISub {
            node,
            op,
            elems,
            rest,
        } => {
            emit_variadic_join(node, *op, atom_id, elems, bound, steps);
            steps.push(Step::DecomposeACI {
                node: *node,
                elems: elems.clone(),
                rest: Some(*rest),
            });
            for &ev in elems {
                pv_mark_bound(&ev, bound);
            }
        }
    }
}

/// Try to lower an atom that is *forced or free* given the current bindings —
/// the "eager pass" cases that cost nothing to resolve and only shrink the
/// problem: `Eq`/`EqGlobal` constraints between bound vars, and
/// `Lit`/`LitBind`/`Plain` whose node var is already bound (re-join within its
/// class). Returns `Some(steps)` and marks newly-bound vars if the atom is
/// eagerly resolvable now; `None` if it must wait for cost-based selection
/// (an unbound scanning atom). Single source of truth shared by the static
/// scheduler's eager pass and the runtime-adaptive matcher.
pub(crate) fn try_eager_lower<O: DenseId + Hash + Copy, S, V: Clone, I: IndexLike>(
    atom: &RAtom<O, S, V>,
    atom_id: usize,
    bound: &mut [bool],
) -> Option<Vec<Step<O, I, V>>> {
    let mut steps = Vec::new();
    match atom {
        RAtom::Eq(a, b) => {
            if bound[(*a).idx()] && bound[(*b).idx()] {
                steps.push(Step::CheckEq { a: *a, b: *b });
            } else if bound[(*a).idx()] {
                steps.push(Step::CopyBinding {
                    target: *b,
                    other: *a,
                });
                bound[(*b).idx()] = true;
            } else if bound[(*b).idx()] {
                steps.push(Step::CopyBinding {
                    target: *a,
                    other: *b,
                });
                bound[(*a).idx()] = true;
            } else {
                return None;
            }
        }
        RAtom::EqGlobal(local, global) if bound[(*local).idx()] => {
            steps.push(Step::CheckEqGlobal {
                local: *local,
                global: *global,
            });
        }
        RAtom::EqGlobal(local, global) => {
            // Unbound: the atom is what gives the variable its value.
            steps.push(Step::BindGlobal {
                target: *local,
                global: *global,
            });
            bound[(*local).idx()] = true;
        }
        RAtom::Lit {
            node, op, value, ..
        } if bound[(*node).idx()] => {
            steps.push(Step::Join {
                target: *node,
                lookups: vec![
                    IndexLookup::ByRepr { repr: *node },
                    IndexLookup::ByOp { op: *op },
                ],
                atom_id,
            });
            steps.push(Step::CheckLit {
                node: *node,
                value: value.clone(),
            });
        }
        RAtom::LitBind { node, op, val } if bound[(*node).idx()] => {
            steps.push(Step::Join {
                target: *node,
                lookups: vec![
                    IndexLookup::ByRepr { repr: *node },
                    IndexLookup::ByOp { op: *op },
                ],
                atom_id,
            });
            steps.push(Step::ExtractLitVal {
                node: *node,
                val: *val,
            });
        }
        RAtom::Plain { node, op, .. } if bound[(*node).idx()] => {
            steps.push(Step::Join {
                target: *node,
                lookups: vec![
                    IndexLookup::ByRepr { repr: *node },
                    IndexLookup::ByOp { op: *op },
                ],
                atom_id,
            });
            emit_read_children(atom, bound, &mut steps);
        }
        _ => return None,
    }
    Some(steps)
}

fn emit_variadic_join<O: DenseId + Hash + Copy, I: IndexLike, V>(
    node: &VarId,
    op: O,
    atom_id: usize,
    elems: &[PatVar],
    bound: &mut [bool],
    steps: &mut Vec<Step<O, I, V>>,
) {
    if !bound[(*node).idx()] {
        // Drive from `by_op[op]`, intersected with `by_contains[e]` for every
        // element `e` already bound. A matching variadic node MUST contain each
        // bound element, so `by_contains[e]` is a sound (membership-only) filter
        // — the following DecomposeAC/ExpandA/DecomposeACI does the precise
        // multiplicity/position check. This narrows the driver to the few
        // parents containing the bound element instead of scanning the whole
        // `by_op` bucket — the variadic analogue of `Plain`'s `ByChildPos`.
        let mut lookups = vec![IndexLookup::ByOp { op }];
        for &pv in elems {
            if pv_is_bound(&pv, bound) {
                lookups.push(IndexLookup::ByContains { child: pv });
            }
        }
        steps.push(Step::Join {
            target: *node,
            lookups,
            atom_id,
        });
        bound[(*node).idx()] = true;
    } else {
        // The node var is already bound — e.g. extracted as an enclosing
        // atom's child via `ExtractChild`. Re-join within its class
        // (`ByRepr ∩ ByOp`), exactly as the `Plain` bound-node path does, so
        // this atom still emits a `Step::Join` carrying `atom_id`. Without it,
        // the semi-naive variant mode (delta / full∖delta / full) — which is
        // realized *only* on `Step::Join` (see `ematch::run_join`) — would
        // never be applied to a parent-driven variadic atom, letting the
        // parent-driven variant re-discover matches the delta-driven variants
        // already own. In the naive path this re-join is a no-op intersection
        // (the node re-selects itself within its own class).
        steps.push(Step::Join {
            target: *node,
            lookups: vec![
                IndexLookup::ByRepr { repr: *node },
                IndexLookup::ByOp { op },
            ],
            atom_id,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{OpId, SortId};
    use crate::lit_model::LitModel;
    use crate::literal::{LitValStore, NiraLitVal, NiraModel};
    use crate::nodes::LitValId;
    use crate::registry::{OpRegistry, SortRegistry};
    use crate::resolve::MatchShape;
    use crate::resolve::resolve;
    use crate::sortcheck::flatten_surface as flatten;
    use crate::test_helpers::parse_pattern;

    fn setup() -> (
        OpRegistry<OpId, SortId, false>,
        SortRegistry<SortId, false>,
        LitValStore<NiraLitVal, LitValId, false>,
    ) {
        let model = NiraModel;
        let mut sorts: SortRegistry<SortId, false> = SortRegistry::new();
        let sort_names: Vec<&str> = model.sorts().iter().map(|s| s.name).collect();
        sorts.register_builtins(&sort_names);
        let e = sorts.intern("IExpr");
        let mut ops = OpRegistry::new();
        ops.register_builtins(&model, &sorts);
        ops.register("f", &[e, e], e);
        ops.register("g", &[e], e);
        ops.register("h", &[e, e], e);
        ops.register_a("concat", e, e, crate::registry::AssocDir::Right);
        ops.register_mset("add", e, e);
        ops.register_set("union", e, e);
        let ibig = sorts.id_by_name("IBig").expect("IBig builtin");
        ops.register("ILit", &[ibig], e);
        (ops, sorts, LitValStore::new())
    }

    fn do_plan(src: &str) -> (QueryPlan<OpId, u32, NiraLitVal>, MatchShape) {
        let (ops, sorts, _) = setup();
        let model = NiraModel;
        let pat = parse_pattern(src);
        let fq = flatten(&[pat], &ops).unwrap();
        let rq = resolve(
            &fq,
            &ops,
            &sorts,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        (schedule(&rq), rq.shape)
    }

    fn do_plan_multi(srcs: &[&str]) -> (QueryPlan<OpId, u32, NiraLitVal>, MatchShape) {
        let (ops, sorts, _) = setup();
        let model = NiraModel;
        let pats: Vec<_> = srcs.iter().map(|s| parse_pattern(s)).collect();
        let fq = flatten(&pats, &ops).unwrap();
        let rq = resolve(
            &fq,
            &ops,
            &sorts,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        (schedule(&rq), rq.shape)
    }

    fn do_plan_with_stats(
        srcs: &[&str],
        card: &[(&str, usize)],
    ) -> (QueryPlan<OpId, u32, NiraLitVal>, MatchShape) {
        let (ops, sorts, _) = setup();
        let model = NiraModel;
        let pats: Vec<_> = srcs.iter().map(|s| parse_pattern(s)).collect();
        let fq = flatten(&pats, &ops).unwrap();
        let rq = resolve(
            &fq,
            &ops,
            &sorts,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let mut stats = IndexStats::new();
        for &(name, c) in card {
            let op_id = ops.id_by_name(name).unwrap();
            stats.op_card.insert(op_id, c);
        }
        (schedule_with_stats(&rq, &stats), rq.shape)
    }

    /// A guard runs as soon as its values are bound, not at the end of the plan: the
    /// check sits immediately after the last `ExtractLitVal` it depends on, so a false
    /// guard cuts the search before the remaining atoms are joined.
    #[test]
    fn guard_runs_as_soon_as_its_values_are_bound() {
        let (plan, _) = do_plan_multi(&["(f (ILit a) (ILit b))", "(< a b)", "(g y)"]);
        let pred = plan
            .steps
            .iter()
            .position(|s| matches!(s, Step::CheckPred { .. }))
            .expect("guard step");
        let last_extract = plan
            .steps
            .iter()
            .rposition(|s| matches!(s, Step::ExtractLitVal { .. }))
            .expect("lit-val extraction");
        assert_eq!(pred, last_extract + 1);
        // The unrelated atom is still to come, so the guard cut it off.
        assert!(
            plan.steps[pred + 1..]
                .iter()
                .any(|s| matches!(s, Step::Join { .. }))
        );
    }

    /// The root-binding form costs one step when the bound name is fresh: the root is
    /// copied onto it, not re-searched.
    #[test]
    fn root_binding_copies_the_root() {
        let (plan, shape) = do_plan("(= v (g x))");
        let v = shape.find_var("v").unwrap();
        assert!(
            plan.steps
                .iter()
                .any(|s| matches!(s, Step::CopyBinding { target, .. } if *target == v))
        );
    }

    #[test]
    fn plain_flat() {
        let (qp, _) = do_plan("(f x y)");
        assert_eq!(qp.steps.len(), 3);
        assert!(matches!(&qp.steps[0], Step::Join { lookups, .. }
            if matches!(&lookups[0], IndexLookup::ByOp { .. })));
        assert!(matches!(&qp.steps[1], Step::ExtractChild { pos: 0, .. }));
        assert!(matches!(&qp.steps[2], Step::ExtractChild { pos: 1, .. }));
    }

    #[test]
    fn nested() {
        let (qp, _) = do_plan("(f x (g y))");
        let join_count = qp
            .steps
            .iter()
            .filter(|s| matches!(s, Step::Join { .. }))
            .count();
        assert_eq!(join_count, 2);
    }

    #[test]
    fn multi_atom_shared_var() {
        let (qp, vars) = do_plan_multi(&["(f x y)", "(g y)"]);
        let y = vars.find_var("y").unwrap();
        // g has 1 arg, so after f binds y, g-join should use ByChildPos(y, 0)
        let g_join = qp.steps.iter().find(|s| match s {
            Step::Join { lookups, .. } => lookups.len() > 1,
            _ => false,
        });
        assert!(g_join.is_some());
        if let Step::Join { lookups, .. } = g_join.unwrap() {
            assert!(
                lookups
                    .iter()
                    .any(|l| matches!(l, IndexLookup::ByChildPos { child, pos: 0 } if *child == PatVar::Local(y)))
            );
        }
    }

    /// A ground literal in a pattern must compile to a *satisfiable* plan: a join that
    /// actually reads an index, followed by the payload check that pins the value.
    /// Regression for the dead-literal defect — the literal atom used to emit
    /// `Join { lookups: [] }`, and an empty lookup vector makes both matcher engines
    /// abandon the query, so the whole rule was inert.
    #[test]
    fn literal_atom_joins_and_checks_payload() {
        let (qp, _) = do_plan("(f (ILit 42) x)");
        for step in &qp.steps {
            if let Step::Join { lookups, .. } = step {
                assert!(
                    !lookups.is_empty(),
                    "a join with no lookups yields no candidates: {qp:?}"
                );
            }
        }
        let checks: Vec<_> = qp
            .steps
            .iter()
            .filter(|s| matches!(s, Step::CheckLit { .. }))
            .collect();
        assert_eq!(checks.len(), 1, "expected one payload check in {qp:?}");
        assert!(
            matches!(checks[0], Step::CheckLit { value, .. } if value.to_string() == "42"),
            "payload check does not carry the pattern's literal: {qp:?}"
        );
    }

    #[test]
    fn nonlinear_check_eq() {
        let (qp, _) = do_plan("(f x x)");
        assert!(
            qp.steps
                .iter()
                .any(|s| matches!(s, Step::CheckChildEq { .. }))
        );
    }

    #[test]
    fn ac_subset() {
        let (qp, _) = do_plan("(add x:2 ..rest)");
        assert!(qp.steps.iter().any(|s| matches!(
            s,
            Step::DecomposeAC {
                rest: Some(_),
                idempotent: false,
                ..
            }
        )));
    }

    #[test]
    fn aci_subset() {
        let (qp, _) = do_plan("(union x y ..rest)");
        assert!(
            qp.steps
                .iter()
                .any(|s| matches!(s, Step::DecomposeACI { rest: Some(_), .. }))
        );
    }

    #[test]
    fn a_prefix() {
        let (qp, _) = do_plan("(concat ..pre x y)");
        assert!(qp.steps.iter().any(|s| matches!(
            s,
            Step::ExpandA {
                pre: Some(_),
                suf: None,
                ..
            }
        )));
    }

    #[test]
    fn selectivity_picks_rarest() {
        let (qp, _) = do_plan_with_stats(&["(f x (g y))"], &[("f", 10_000), ("g", 10)]);
        // First Join should be for g (rarest)
        let first_join = qp
            .steps
            .iter()
            .find(|s| matches!(s, Step::Join { .. }))
            .unwrap();
        if let Step::Join { lookups, .. } = first_join {
            let (ops, _, _) = setup();
            let g_id = ops.id_by_name("g").unwrap();
            assert!(
                lookups
                    .iter()
                    .any(|l| matches!(l, IndexLookup::ByOp { op } if *op == g_id))
            );
        }
    }

    #[test]
    fn selectivity_three_atoms() {
        let (qp, _) = do_plan_with_stats(
            &["(f x y)", "(g y)", "(h y w)"],
            &[("f", 10_000), ("g", 500), ("h", 5)],
        );
        let (ops, _, _) = setup();
        let join_ops: Vec<OpId> = qp
            .steps
            .iter()
            .filter_map(|s| match s {
                Step::Join { lookups, .. } => lookups.iter().find_map(|l| match l {
                    IndexLookup::ByOp { op } => Some(*op),
                    _ => None,
                }),
                _ => None,
            })
            .collect();
        let h = ops.id_by_name("h").unwrap();
        let g = ops.id_by_name("g").unwrap();
        let f = ops.id_by_name("f").unwrap();
        assert_eq!(join_ops, [h, g, f]);
    }

    #[test]
    fn bound_child_reduces_cost() {
        let (qp, _) = do_plan_with_stats(&["(f x y)", "(h y z)"], &[("f", 1000), ("h", 1000)]);
        let second_join = qp
            .steps
            .iter()
            .filter(|s| matches!(s, Step::Join { .. }))
            .nth(1);
        if let Some(Step::Join { lookups, .. }) = second_join {
            assert!(
                lookups
                    .iter()
                    .any(|l| matches!(l, IndexLookup::ByChildPos { .. }))
            );
        }
    }

    /// The captured fan-out constants, not the atoms' cardinalities, decide
    /// which atom is joined second. This regression retains a historically
    /// problematic shape:
    /// two `f` atoms sharing a child and joined only through their common `h`
    /// parent, with `f` = Mul and `h` = Add. Both candidates have one bound
    /// child once the first `f` is
    /// scanned, so the fixed halving compared 54,051/2 against 86,061/2 and
    /// took the `f` atom, whose `by_child_pos` probe returns 1,239 nodes
    /// instead of the 43,030 charged. With the fan-outs measured, the `h` atom
    /// is charged 1.5 and wins, and the second `f` then costs a `ByRepr`
    /// re-join within the class the `h` atom bound.
    #[test]
    fn measured_fanouts_beat_cardinalities_on_sibling_atoms() {
        let (ops, _, _) = setup();
        let f = ops.id_by_name("f").unwrap();
        let h = ops.id_by_name("h").unwrap();

        let mut stats = IndexStats::<OpId>::new();
        stats.op_card.insert(f, 54_051);
        stats.op_card.insert(h, 86_061);
        stats.fanouts.nodes = 216_061;
        stats.fanouts.by_repr = 2.51;
        // `f` nodes share their first child with 1,239 siblings on average;
        // `h` nodes almost never share theirs.
        stats.fanouts.by_child_pos.insert((f, 0), 1_239.0);
        stats.fanouts.by_child_pos.insert((f, 1), 1_239.0);
        stats.fanouts.by_child_pos.insert((h, 0), 1.5);
        stats.fanouts.by_child_pos.insert((h, 1), 1.5);

        let join_ops = |stats: &IndexStats<OpId>| -> Vec<OpId> {
            let (ops, sorts, _) = setup();
            let pats = [parse_pattern("(h (f a b) (f a c))")];
            let fq = flatten(&pats, &ops).unwrap();
            let rq = resolve(
                &fq,
                &ops,
                &sorts,
                &NiraModel,
                &crate::resolve::GlobalCtx::<_, ()>::new(),
            )
            .unwrap();
            let qp: QueryPlan<OpId, u32, NiraLitVal> = schedule_with_stats(&rq, stats);
            qp.steps
                .iter()
                .filter_map(|s| match s {
                    Step::Join { lookups, .. } => lookups.iter().find_map(|l| match l {
                        IndexLookup::ByOp { op } => Some(*op),
                        _ => None,
                    }),
                    _ => None,
                })
                .collect()
        };

        // Control: the same cardinalities with no measurements reproduce the
        // defect, so the assertion below is about the constants and not about
        // some other difference between the two runs.
        let mut halving = IndexStats::<OpId>::new();
        halving.op_card.insert(f, 54_051);
        halving.op_card.insert(h, 86_061);
        assert_eq!(
            join_ops(&halving),
            [f, f, h],
            "the fixed halving should still join the second f before h"
        );
        assert_eq!(
            join_ops(&stats),
            [f, h, f],
            "measured fan-outs should join h second, leaving the second f a class re-join"
        );
    }

    /// A bound element discounts a variadic atom's cost, just as a bound child
    /// discounts a `Plain` atom — so `estimate_cost` reflects the `by_contains`
    /// narrowing that `emit_variadic_join` performs. Without the discount a
    /// fully-bound variadic atom would be mis-costed as a full `by_op` scan.
    #[test]
    fn bound_element_discounts_variadic_cost() {
        let (ops, _, _) = setup();
        let add = ops.id_by_name("add").unwrap();
        let mut stats = IndexStats::<OpId>::new();
        stats.op_card.insert(add, 1000);

        // ACSub `(add x:1 ..rest)` with one element var `x` (VarId 0).
        let atom = RAtom::<OpId, SortId, NiraLitVal>::ACSub {
            node: VarId::new(1),
            op: add,
            elems: vec![(PatVar::Local(VarId::new(0)), RMult::Exact(1))],
            rest: crate::ast::MsetVarId::new(0),
        };

        let cost_of = |bound: &[bool]| {
            let mut ctx = Cost {
                stats: &stats,
                emitters: vec![None; bound.len()],
                sampling: None,
            };
            estimate_cost(std::slice::from_ref(&atom), 0, bound, &mut ctx)
        };

        // x unbound → full op cardinality. (atom_id 0; no per-atom override,
        // so it falls back to op_card.)
        let bound_none = [false, false];
        assert_eq!(cost_of(&bound_none), 1000.0);

        // x bound → discounted (halved per bound element), reflecting the
        // `by_contains[x]` intersection the join will apply.
        let bound_x = [true, false];
        let cost_bound = cost_of(&bound_x);
        assert!(
            cost_bound < 1000.0,
            "binding an element must discount a variadic atom's cost, got {cost_bound}"
        );
        assert_eq!(
            cost_bound, 500.0,
            "with no measured fan-out one bound element halves the estimate"
        );
    }

    /// A sampler that answers every probe with a per-operator constant, and
    /// records which atom it was asked to draw from.
    struct StubSampler {
        lens: std::collections::HashMap<OpId, usize>,
        drawn: std::cell::RefCell<Vec<usize>>,
    }

    impl CrossSampler<OpId> for StubSampler {
        fn driver_sample(&self, atom_id: usize, _op: OpId, k: usize, out: &mut Vec<usize>) {
            self.drawn.borrow_mut().push(atom_id);
            out.clear();
            out.extend(0..k);
        }
        fn key_classes(&self, node: usize, _site: KeySite, out: &mut Vec<usize>) {
            out.push(node);
        }
        fn probe_len(&self, _class: usize, _path: ProbePath, op: OpId) -> usize {
            self.lens.get(&op).copied().unwrap_or(0)
        }
    }

    /// The sampled bucket length replaces the round's mean fan-out in the cost,
    /// and the draw is taken from the atom that bound the key.
    ///
    /// `(f x y) (g y) (h y w)` with `f` cheapest, so both estimators drive from
    /// it and both then choose between `g` and `h` on the same bound `y`. The
    /// mean has `g`'s probe returning 1 node and `h`'s 500, and orders `g`
    /// second. The sampler reverses the two numbers on the same statistics, and
    /// the order reverses with them — which is only possible if the fan-out is
    /// what the sample displaces. The draw must come from atom 0: `y` is `f`'s
    /// second child, and no other scheduled atom binds it.
    #[test]
    fn a_sampled_bucket_displaces_the_mean_fanout() {
        let (ops, sorts, _) = setup();
        let (f, g, h) = (
            ops.id_by_name("f").unwrap(),
            ops.id_by_name("g").unwrap(),
            ops.id_by_name("h").unwrap(),
        );
        let mut stats = IndexStats::<OpId>::new();
        stats.op_card.insert(f, 10);
        stats.op_card.insert(g, 1_000);
        stats.op_card.insert(h, 1_000);
        stats.fanouts.by_child_pos.insert((g, 0), 1.0);
        stats.fanouts.by_child_pos.insert((h, 0), 500.0);

        let pats: Vec<_> = ["(f x y)", "(g y)", "(h y w)"]
            .iter()
            .map(|s| parse_pattern(s))
            .collect();
        let fq = flatten(&pats, &ops).unwrap();
        let rq = resolve(
            &fq,
            &ops,
            &sorts,
            &NiraModel,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let join_ops = |plan: &QueryPlan<OpId, u32, NiraLitVal>| -> Vec<OpId> {
            plan.steps
                .iter()
                .filter_map(|s| match s {
                    Step::Join { lookups, .. } => lookups.iter().find_map(|l| match l {
                        IndexLookup::ByOp { op } => Some(*op),
                        _ => None,
                    }),
                    _ => None,
                })
                .collect()
        };

        assert_eq!(
            join_ops(&schedule_with_stats(&rq, &stats)),
            [f, g, h],
            "the mean should join g second"
        );

        let stub = StubSampler {
            lens: [(g, 400usize), (h, 2usize)].into_iter().collect(),
            drawn: std::cell::RefCell::new(Vec::new()),
        };
        let cfg = SamplerConfig::default();
        let plan: QueryPlan<OpId, u32, NiraLitVal> =
            schedule_inner(&rq, &stats, Some((&stub, cfg)));
        assert_eq!(
            join_ops(&plan),
            [f, h, g],
            "the sampled lengths should join h second"
        );
        let drawn = stub.drawn.into_inner();
        assert_eq!(
            drawn,
            vec![0],
            "the draw must come once from the atom that bound the key"
        );
    }

    /// With sampling off the sampler is never consulted, so a caller may hold
    /// one unconditionally: the flag alone decides.
    #[test]
    fn the_flag_off_path_never_samples() {
        let (ops, sorts, _) = setup();
        let pats = [parse_pattern("(f x y)"), parse_pattern("(g y)")];
        let fq = flatten(&pats, &ops).unwrap();
        let rq = resolve(
            &fq,
            &ops,
            &sorts,
            &NiraModel,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let stub = StubSampler {
            lens: std::collections::HashMap::new(),
            drawn: std::cell::RefCell::new(Vec::new()),
        };
        assert_eq!(sampled_selectivity(), None, "the flag defaults to off");
        let plan: QueryPlan<OpId, u32, NiraLitVal> =
            schedule_with_stats_sampled(&rq, &IndexStats::new(), &stub);
        assert_eq!(
            plan.steps,
            schedule_with_stats::<_, _, _, u32>(&rq, &IndexStats::new()).steps
        );
        assert!(stub.drawn.into_inner().is_empty());
    }

    /// End-to-end: with a bound element, the scheduler must be willing to drive
    /// from a high-cardinality variadic atom. `(g x)` binds x cheaply; the
    /// `add` atom has 100× g's cardinality, but once x is bound its discounted
    /// cost lets `by_contains[x]` carry the join (lookups include ByContains).
    #[test]
    fn scheduler_drives_variadic_from_bound_element() {
        let (qp, vars) =
            do_plan_with_stats(&["(g x)", "(add x ..rest)"], &[("g", 10), ("add", 1000)]);
        let x = vars.find_var("x").unwrap();
        // The add-atom join must intersect by_contains on the bound element x.
        let has_by_contains = qp.steps.iter().any(|s| match s {
            Step::Join { lookups, .. } => lookups.iter().any(
                |l| matches!(l, IndexLookup::ByContains { child } if *child == PatVar::Local(x)),
            ),
            _ => false,
        });
        assert!(
            has_by_contains,
            "variadic atom with a bound element should drive via ByContains: {:?}",
            qp.steps
        );
    }
}
