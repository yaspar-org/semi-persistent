// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! SearchSession: the public API for anti-unification (§4.7, §6).
//!
//! A session is built from a frozen e-graph, runs Exact or UCT, and returns the
//! best anti-unifier found.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::literal::LitVal;

use super::actions::{ActionCache, ActionCacheToken};
use super::egraph_api::{AuSnapshot, ClassOf};
use super::mcgs::{self, AndSelector, HybridStats, McgsConfig};
use super::results::{BestResults, BestResultsToken};
use super::space::{CycleMode, SearchSpace, SpaceToken};
use super::terms::{TermOp, TermPool, TermPoolToken};
use crate::config::AuIds;

/// Term id projected from a config's AU family.
pub type TermOf<Cfg> = <<Cfg as EGraphConfig>::Au as AuIds>::Term;

/// Which algorithm to run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AuAlgorithm {
    /// The exact DP solver (§3.2).
    Exact,
    /// MCGS with UCT selection (§3.3).
    #[default]
    Uct,
}

/// Configuration for an anti-unification session.
#[derive(Debug, Clone)]
pub struct AuConfig {
    pub algorithm: AuAlgorithm,
    /// Cycle breaking for every algorithm. The side modes track left and
    /// right classes independently; [`CycleMode::Pair`] tracks ordered class
    /// pairs and selects bounded pair relaxation for root Exact.
    pub cycle_mode: CycleMode,
    pub playouts: u64,
    pub exploration_constant: f64,
    pub x_target: f64,
    /// Effort allocation at AND nodes (§3.3.5). Default `AndSelector::LctAnd`.
    pub and_selector: AndSelector,
    /// Wall-clock budget for the exact solver. `None` (the default) runs to
    /// completion and returns `Completion::Exact`. `Some(d)` makes exact
    /// anytime: on expiry it returns the root's best incumbent so far — at
    /// minimum the generalize seed, always a feasible anti-unifier — with
    /// `Completion::BudgetExhausted`, never claiming optimality. Ignored by
    /// the UCT algorithm, whose budget is `playouts`.
    pub exact_deadline: Option<std::time::Duration>,
    /// Branch-and-bound in Exact: skip a structural action or AC
    /// representation pair when its projection lower bound
    /// (`estimates::lb_pair`) strictly exceeds the pair's achieved incumbent.
    /// The comparison is size-only and strict because equal size can still
    /// improve variant mass. Contextual exact calls delegated by UCT also
    /// tighten this bound with completed children. Default `false`;
    /// `au_differential.rs::pruned_exact_matches_reference` asserts the
    /// flag-on qualities equal the unpruned reference. Ignored by UCT
    /// selection itself.
    pub exact_pruning: bool,
    /// Context-subsumption reuse for side-context Exact. Pair-mode root Exact
    /// already has one state per bare ordered pair, so reuse is inherent
    /// there. Pair-context hybrid calls currently leave this optimization off
    /// because their support proof must preserve pair correlations.
    pub context_subsumption: bool,
    /// Dominance pruning in the UCT/MCGS solver: at OR-stats creation, drop
    /// every action whose
    /// projection lower bound strictly exceeds the node's generalize value —
    /// the exact value of an always-available alternative — so a dropped
    /// action can never be optimal at that node, and a node whose every
    /// action is dropped closes at its generalize value. Shrinks the
    /// certification budget without touching soundness: the certificate's
    /// claim becomes "every action was realized or proven non-optimal", the
    /// same claim exact-side pruning makes. Default `false`: the unpruned
    /// search is the reference the differential fixture was captured
    /// against; `au_differential.rs::dominant_pruned_mcgs_is_sound` gates
    /// the flag-on behavior. Ignored by the exact algorithm.
    pub dominance_pruning: bool,
    /// The MCTS-solver closed bit: every OR node carries a bit that is set once
    /// its subgraph is fully resolved, maintained incrementally through
    /// reverse edges, and selection descends only into open subtrees. A closed
    /// subtree's value and stored result are exact and final, so the skipped
    /// visits could not have changed any answer; the freed playouts go to
    /// actions that are still unrealized, which is what makes the
    /// certification budget track the action census on deep search graphs
    /// instead of growing exponentially in their depth. Certification reads
    /// the
    /// root's bit and the run stops as soon as it is set. Every closed node is
    /// also marked exact in the session's result table, so a later run on the
    /// same session inherits the proof (that node is terminal at creation) and
    /// the proof rolls back with `restore`. Default `false`: the
    /// unrestricted search is the reference the differential fixture was
    /// captured against; `au_differential.rs::closed_bit_mcgs_is_sound` gates
    /// the flag-on behavior. Ignored by the exact algorithm.
    pub closed_bit: bool,
    /// Hybrid exact subproblems in the UCT/MCGS solver: when a new OR node's
    /// reachable-pair estimate is
    /// at or below [`Self::hybrid_threshold`], the exact solver (with
    /// `exact_pruning` and `context_subsumption` on) solves that node's own
    /// state (same class pair, same cycle contexts, same cycle mode). Its term
    /// is offered, and a completed call is marked contextually exact in the
    /// session's result table.
    /// Since an exact-marked node is terminal at creation, and terminal nodes
    /// are born closed, the proof is a closed subtree the search never enters:
    /// what would have cost `sum A(v)` playouts below that node costs one
    /// exact call. The admission thresholds estimate workload but do not bound
    /// descendant contextual states or fan-out; only `hybrid_node_budget`
    /// hard-bounds one call. Default `false`: the pure playout search is the
    /// reference the differential fixture was captured against;
    /// `au_differential.rs::hybrid_exact_mcgs_is_sound` gates the flag-on
    /// behavior. Ignored by the exact algorithm.
    pub hybrid_exact: bool,
    /// Admission estimate for [`Self::hybrid_exact`], in reachable bare class
    /// pairs (`estimates::reachable_pairs`). This can undercount contextual
    /// states and is not a hard work bound. The default is a historical
    /// compatibility value pending a current Criterion calibration.
    pub hybrid_threshold: u64,
    /// Live-incumbent arm pruning in the UCT/MCGS solver: every arm carries
    /// its admissible size
    /// lower bound, and an arm whose bound STRICTLY exceeds the node's
    /// current incumbent is excluded from selection and counts as resolved
    /// toward the certificate ("realized or proven non-optimal", the
    /// `dominance_pruning` claim evaluated against the live incumbent
    /// instead of the creation-time generalize value). Strict, size-only:
    /// an equal-size arm can still win the lexicographic tie on variant
    /// mass. Requires `closed_bit`; the run refuses the flag without it.
    /// Default `false`;
    /// `au_differential.rs::live_incumbent_pruning_is_sound` gates the
    /// flag-on behavior. Ignored by the exact algorithm.
    pub live_incumbent_pruning: bool,
    /// Hybrid exact calls fired from inside the initial rollout: every rollout
    /// frame whose subproblem passes [`Self::hybrid_exact`]'s admission gate is
    /// delegated and becomes the completed suffix of that rollout. A completed
    /// call supplies a contextually certified exact suffix; a call that
    /// exhausts `hybrid_node_budget` supplies only a feasible uncertified
    /// suffix. Only completed frames are terminal and certified when expansion
    /// reaches them. Same soundness argument as
    /// `hybrid_exact` (same class pair, context, and cycle mode). Requires
    /// `hybrid_exact`; the run refuses the flag without it. Default `false`;
    /// `au_differential.rs::rollout_hybrid_mcgs_is_sound` gates the flag-on
    /// behavior. Ignored by the exact algorithm.
    pub rollout_hybrid: bool,
    /// Session-level exact memo:
    /// side-context hybrid exact calls share one bare-pair memo of
    /// context-clean solves across the whole session, so calls over overlapping
    /// subgraphs reuse instead of re-solving (the context-clean entry merely
    /// outlives the call). Pair-context calls leave it unused until support
    /// records preserve pair correlations. The memo rolls back with the session token. Requires
    /// `hybrid_exact`. Default `false`;
    /// `au_differential.rs::persistent_memo_exact_is_sound` gates the
    /// flag-on behavior. Ignored by the exact algorithm.
    pub session_exact_memo: bool,
    /// Second admission gate for hybrid exact calls: the node's own
    /// action count must be at or below this. It complements the bare-pair
    /// rectangle estimate, but neither estimate bounds descendant contextual
    /// states or fan-out. Default `u64::MAX` (admission by rectangle alone,
    /// the reference behavior).
    /// Ignored by the exact algorithm.
    pub hybrid_action_threshold: u64,
    /// Deterministic in-call backstop for hybrid exact calls, in
    /// node entries: on exhaustion the call returns its incumbent
    /// uncertified (and keeps completed subframes under
    /// `session_exact_memo`). Default `None`. Ignored by the exact
    /// algorithm (use `exact_deadline` there).
    pub hybrid_node_budget: Option<u64>,
    /// Static child seeding:
    /// expansion seeds fresh children with their stored best size and the
    /// full initial rollout runs on a child's first selection instead of at
    /// expansion, so a k-child expansion stops paying k greedy descents for
    /// children selection may never enter. Default `false`;
    /// `au_differential.rs::static_child_seed_mcgs_is_sound` gates the
    /// flag-on soundness (matched-playout quality may legitimately differ:
    /// the flag trades estimate quality per playout for cost per playout).
    /// Ignored by the exact algorithm.
    pub static_child_seed: bool,
    /// Interval labels: every arm
    /// carries a lower bound that TIGHTENS as the search discovers its
    /// subtree is expensive (`L(and) = 1 + Σ count · L(child)`,
    /// `L(or) = min over live arms`), instead of freezing at the static
    /// creation bound. Exclusion then fires on the dynamic bound, which
    /// dominates `live_incumbent_pruning`'s static one: identical where the
    /// static bound is tight, decisive where it is loose (subterms with
    /// equal size profiles, hence equal `lb_pair`, whose anti-unifiers cost
    /// very differently). Requires `live_incumbent_pruning`. Default
    /// `false`; `au_differential.rs::interval_bounds_mcgs_is_sound` gates
    /// the flag-on behavior. Ignored by the exact algorithm.
    pub interval_bounds: bool,
}

impl Default for AuConfig {
    fn default() -> Self {
        AuConfig {
            algorithm: AuAlgorithm::Uct,
            cycle_mode: CycleMode::AncestorOnly,
            playouts: 1000,
            exploration_constant: std::f64::consts::SQRT_2,
            x_target: 0.8,
            and_selector: AndSelector::default(),
            exact_deadline: None,
            exact_pruning: false,
            context_subsumption: false,
            dominance_pruning: false,
            closed_bit: false,
            hybrid_exact: false,
            hybrid_threshold: mcgs::DEFAULT_HYBRID_THRESHOLD,
            live_incumbent_pruning: false,
            rollout_hybrid: false,
            session_exact_memo: false,
            hybrid_action_threshold: u64::MAX,
            hybrid_node_budget: None,
            static_child_seed: false,
            interval_bounds: false,
        }
    }
}

/// Whether the solver structurally completed its declared action space.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Completion {
    /// Every reachable subproblem in the configured action space was solved.
    /// Pair-mode root Exact covers the finite class-pair graph. Side-mode
    /// Exact and every UCT mode certify their configured contextual graph. Transport
    /// representation pairs whose margins exceed the solver's `u32` capacity
    /// are outside every mode's supported domain.
    Exact,
    /// The playout budget expired before the search graph was fully resolved.
    BudgetExhausted { playouts_used: u64 },
}

/// The result of an anti-unification run. Configuration-based: the id family,
/// operator, and value types all project from `Cfg`.
pub struct AuResult<Cfg: EGraphConfig> {
    pub term_id: TermOf<Cfg>,
    pub pool: TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    pub size: u32,
    pub algorithm: AuAlgorithm,
    pub completion: Completion,
    /// What `AuConfig::hybrid_exact` did during the run; all zeros for the
    /// exact algorithm and for a UCT run with the flag off.
    pub hybrid: HybridStats,
}

/// Width aliases for downstream convenience.
pub type AuResult31 = AuResult<crate::nodes::DefaultConfig>;
pub type AuResult63 = AuResult<crate::nodes::Config64>;

impl<Cfg: EGraphConfig> core::fmt::Debug for AuResult<Cfg> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AuResult")
            .field("term_id", &self.term_id)
            .field("size", &self.size)
            .field("algorithm", &self.algorithm)
            .field("completion", &self.completion)
            .finish()
    }
}

impl<Cfg: EGraphConfig> AuResult<Cfg> {
    /// Get the operator of the root term.
    pub fn root_op(&self) -> &TermOp<Cfg::O, Cfg::V> {
        self.pool.op(self.term_id)
    }

    /// Get the children of the root term.
    pub fn root_children(&self) -> &[TermOf<Cfg>] {
        self.pool.children(self.term_id)
    }

    /// Render the term as a flat one-line s-expression.
    pub fn to_string_with<F>(&self, op_name: F) -> String
    where
        F: Fn(&TermOp<Cfg::O, Cfg::V>) -> String + Copy,
    {
        super::pretty::pretty_print(&self.pool, self.term_id, op_name, usize::MAX)
    }

    /// Pretty-print the term with indentation, breaking lines that exceed
    /// `col_limit` characters.
    pub fn pretty_print_with<F>(&self, op_name: F, col_limit: usize) -> String
    where
        F: Fn(&TermOp<Cfg::O, Cfg::V>) -> String + Copy,
    {
        super::pretty::pretty_print(&self.pool, self.term_id, op_name, col_limit)
    }
}

/// Run anti-unification on a frozen e-graph between two classes.
///
/// This is the main entry point. Build a snapshot, pick an algorithm, and get back
/// the best anti-unifier found.
pub fn anti_unify<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    left: Cfg::G,
    right: Cfg::G,
    config: &AuConfig,
) -> Result<AuResult<Cfg>, super::AuError>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let l = snap
        .class_of(left)
        .ok_or(super::AuError::NoFiniteRepresentative(0))?;
    let r = snap
        .class_of(right)
        .ok_or(super::AuError::NoFiniteRepresentative(0))?;

    match config.algorithm {
        AuAlgorithm::Exact => {
            let (term, pool, complete) = if config.cycle_mode == CycleMode::Pair {
                let (run, pool) = super::exact_fixed::run(
                    snap,
                    l,
                    r,
                    config.exact_deadline,
                    config.exact_pruning,
                )?;
                (run.term, pool, run.complete)
            } else {
                let run = super::exact::run_exact(
                    snap,
                    l,
                    r,
                    config.cycle_mode,
                    config.exact_deadline,
                    config.exact_pruning,
                    config.context_subsumption,
                )?;
                (run.term, run.pool, run.complete)
            };
            let size = pool.size(term);
            // A deadline expiry surfaces the root incumbent uncertified:
            // feasible by construction, optimal only on completion. The
            // budget the exact solver exhausts is wall clock, not playouts.
            let completion = if complete {
                Completion::Exact
            } else {
                Completion::BudgetExhausted { playouts_used: 0 }
            };
            Ok(AuResult {
                term_id: term,
                pool,
                size,
                algorithm: AuAlgorithm::Exact,
                completion,
                hybrid: HybridStats::default(),
            })
        }
        AuAlgorithm::Uct => {
            let mcgs_config = McgsConfig {
                playouts: config.playouts,
                cycle_mode: config.cycle_mode,
                exploration_constant: config.exploration_constant,
                x_target: config.x_target,
                and_selector: config.and_selector,
                dominance_pruning: config.dominance_pruning,
                closed_bit: config.closed_bit,
                hybrid_exact: config.hybrid_exact,
                live_incumbent_pruning: config.live_incumbent_pruning,
                rollout_hybrid: config.rollout_hybrid,
                session_exact_memo: config.session_exact_memo,
                hybrid_action_threshold: config.hybrid_action_threshold,
                hybrid_node_budget: config.hybrid_node_budget,
                static_child_seed: config.static_child_seed,
                interval_bounds: config.interval_bounds,
                hybrid_threshold: config.hybrid_threshold,
            };
            let (term_id, pool, completion, hybrid) = mcgs::run_mcgs(snap, l, r, &mcgs_config)?;
            let size = pool.size(term_id);
            Ok(AuResult {
                term_id,
                pool,
                size,
                algorithm: AuAlgorithm::Uct,
                completion,
                hybrid,
            })
        }
    }
}

/// Compute the linear compression ratio (§2.5):
/// `(size(t) - min(best_l, best_r)) / max(best_l, best_r)`
pub fn compression_ratio<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    left: ClassOf<Cfg>,
    right: ClassOf<Cfg>,
    au_size: u32,
) -> f64
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let best_l = snap.best_size(left) as f64;
    let best_r = snap.best_size(right) as f64;
    let min_size = best_l.min(best_r);
    let max_size = best_l.max(best_r);
    if max_size == 0.0 {
        return 0.0;
    }
    (au_size as f64 - min_size) / max_size
}

// ---------------------------------------------------------------------------
// SearchSession: the semi-persistent owner of all search state (§4.7)
// ---------------------------------------------------------------------------

/// Opaque token capturing the entire search state at one point in time.
/// Created by `SearchSession::mark()`; consumed by `SearchSession::restore()`.
/// Component tokens are private; callers cannot restore individual layers.
#[derive(Debug)]
pub struct SearchToken {
    space: SpaceToken,
    terms: TermPoolToken,
    results: BestResultsToken,
    actions: ActionCacheToken,
    mcgs: super::mcgs::McgsToken,
}

/// A search session owns the search-space layer, term pool, best-result table,
/// action cache, and the MCGS statistics overlay. It provides one coherent
/// `mark()`/`restore(token)` that snapshots and rolls back all layers together.
/// The e-graph snapshot is borrowed immutably for the session's lifetime; later
/// e-graph mutations are not observed (§4.1).
pub struct SearchSession<'eg, Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    pub(crate) snap: &'eg AuSnapshot<'eg, Cfg, L, T, P>,
    pub(crate) space: SearchSpace<Cfg::Au>,
    pub(crate) pool: TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    pub(crate) results: BestResults<Cfg::Au>,
    pub(crate) action_cache: ActionCache<Cfg::O, Cfg::Au, Cfg::M>,
    pub(crate) mcgs: super::mcgs::McgsState<Cfg::Au, Cfg::O>,
}

impl<'eg, Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>
    SearchSession<'eg, Cfg, L, T, P>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    /// Create a new session from a snapshot. The snapshot must outlive the session.
    pub fn new(snap: &'eg AuSnapshot<'eg, Cfg, L, T, P>, cycle_mode: CycleMode) -> Self {
        SearchSession {
            snap,
            space: SearchSpace::new(cycle_mode),
            pool: TermPool::new(),
            results: BestResults::new(),
            // MCGS uses transport-AND-nodes for AC/ACI (no matrix actions).
            action_cache: ActionCache::without_ac_actions(usize::MAX),
            mcgs: super::mcgs::McgsState::new(),
        }
    }

    /// Snapshot the entire search state. Returns one opaque token; component
    /// tokens are not accessible. Layers are marked in dependency order.
    pub fn mark(&mut self) -> SearchToken {
        SearchToken {
            space: self.space.mark(),
            terms: self.pool.mark(),
            results: self.results.mark(),
            actions: self.action_cache.mark(),
            mcgs: self.mcgs.mark(),
        }
    }

    /// Restore the entire search state to a previous mark. Two-phase: every
    /// component token is validated against its container and branch genealogy
    /// BEFORE any layer is mutated, so a foreign or abandoned token cannot
    /// cause a partial restore. Then restores in reverse dependency order
    /// (statistics first, then results/terms, then structure).
    pub fn restore(&mut self, token: SearchToken) {
        // Phase 1: validate all (no mutation). If any check fails the panic
        // leaves all layers intact.
        assert!(
            self.mcgs.is_valid_token(&token.mcgs),
            "SearchSession: mcgs token is invalid (foreign or abandoned)"
        );
        assert!(
            self.action_cache.is_valid_token(&token.actions),
            "SearchSession: action_cache token is invalid (foreign or abandoned)"
        );
        assert!(
            self.results.is_valid_token(&token.results),
            "SearchSession: results token is invalid (foreign or abandoned)"
        );
        assert!(
            self.pool.is_valid_token(&token.terms),
            "SearchSession: term pool token is invalid (foreign or abandoned)"
        );
        assert!(
            self.space.is_valid_token(&token.space),
            "SearchSession: space token is invalid (foreign or abandoned)"
        );
        // Phase 2: restore all (all validated, cannot fail).
        self.mcgs.restore(token.mcgs);
        self.action_cache.restore(token.actions);
        self.results.restore(token.results);
        self.pool.restore(token.terms);
        self.space.restore(token.space);
    }

    /// Exact solve of the root pair on this session's persistent layers:
    /// terms intern into the session pool, and the solve warm-starts from the
    /// session's stored incumbent for the pair. The session's cycle mode
    /// chooses side-context Exact or ordered-pair fixed-point Exact.
    /// `deadline` makes the solve anytime.
    pub fn run_exact_warm(
        &mut self,
        left: Cfg::G,
        right: Cfg::G,
        pruning: bool,
        subsumption: bool,
        deadline: Option<std::time::Duration>,
    ) -> Result<(TermOf<Cfg>, Completion), super::AuError> {
        let l = self
            .snap
            .class_of(left)
            .ok_or(super::AuError::NoFiniteRepresentative(0))?;
        let r = self
            .snap
            .class_of(right)
            .ok_or(super::AuError::NoFiniteRepresentative(0))?;
        self.snap.validate_finite_from(l)?;
        self.snap.validate_finite_from(r)?;
        let (empty_l, empty_r) = self.space.empty_contexts();
        let (root_or, _) = self.space.get_or_insert_or_node(
            l,
            r,
            empty_l,
            empty_r,
            self.snap.best_size(l),
            self.snap.best_size(r),
        );
        self.results.ensure_capacity(root_or);
        if self.space.cycle_mode != CycleMode::Pair {
            if self.results.is_exact(root_or) {
                let term = self
                    .results
                    .best_term(root_or)
                    .expect("an exact result has an achieved term");
                return Ok((term, Completion::Exact));
            }
            let context = self.space.cycle_context(root_or);
            let warm = self.results.best_term(root_or);
            let run = super::exact::run_exact_at(
                self.snap,
                &mut self.pool,
                l,
                r,
                &context,
                self.space.cycle_mode,
                deadline,
                pruning,
                subsumption,
                Some(self.mcgs.exact_memo_mut()),
                None,
                warm,
            );
            self.results
                .offer(root_or, run.term, self.pool.quality(run.term));
            if run.complete {
                self.results.mark_exact(root_or);
            }
            let completion = if run.complete {
                Completion::Exact
            } else {
                Completion::BudgetExhausted { playouts_used: 0 }
            };
            return Ok((run.term, completion));
        }
        if self.results.is_global_exact(root_or) {
            let term = self
                .results
                .best_global_term(root_or)
                .expect("a globally exact result has an achieved term");
            return Ok((term, Completion::Exact));
        }
        let contextual = self.results.best_term(root_or);
        let global = self.results.best_global_term(root_or);
        let warm = match (contextual, global) {
            (Some(contextual), Some(global)) => {
                if self.results.best_global_quality(root_or) < self.results.best_quality(root_or) {
                    Some(global)
                } else {
                    Some(contextual)
                }
            }
            (contextual @ Some(_), None) => contextual,
            (None, global @ Some(_)) => global,
            (None, None) => None,
        };
        let run =
            super::exact_fixed::run_in(self.snap, &mut self.pool, l, r, deadline, pruning, warm)?;
        self.results
            .offer_global(root_or, run.term, self.pool.quality(run.term));
        if run.complete {
            self.results.mark_global_exact(root_or);
        }
        let completion = if run.complete {
            Completion::Exact
        } else {
            Completion::BudgetExhausted { playouts_used: 0 }
        };
        Ok((run.term, completion))
    }

    /// Run MCGS on this session's persistent layers. Statistics, search space,
    /// terms, and results accumulate across calls and roll back with
    /// `restore(token)`.
    ///
    /// Errors with `AuError::CycleModeMismatch` if `config.cycle_mode` differs
    /// from the mode this session's search space was created with: cycle
    /// contexts already interned under one mode cannot be reused under the
    /// other, and silently ignoring the requested mode would be worse.
    pub fn run_uct(
        &mut self,
        left: Cfg::G,
        right: Cfg::G,
        config: &McgsConfig,
    ) -> Result<(TermOf<Cfg>, Completion), super::AuError> {
        if config.cycle_mode != self.space.cycle_mode {
            return Err(super::AuError::CycleModeMismatch);
        }
        let l = self
            .snap
            .class_of(left)
            .ok_or(super::AuError::NoFiniteRepresentative(0))?;
        let r = self
            .snap
            .class_of(right)
            .ok_or(super::AuError::NoFiniteRepresentative(0))?;
        mcgs::run_mcgs_in(
            self.snap,
            &mut self.space,
            &mut self.pool,
            &mut self.action_cache,
            &mut self.results,
            &mut self.mcgs,
            l,
            r,
            config,
        )
    }

    /// What `McgsConfig::hybrid_exact` did, cumulative over every `run_uct`
    /// call on this session.
    pub fn hybrid_stats(&self) -> HybridStats {
        self.mcgs.hybrid_stats()
    }

    /// The lexicographic quality of a term in this session's pool.
    pub fn pool_quality(&self, term: TermOf<Cfg>) -> (u32, u32) {
        self.pool.quality(term)
    }

    /// The snapshot this session was built from.
    pub fn snapshot(&self) -> &AuSnapshot<'eg, Cfg, L, T, P> {
        self.snap
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::au::egraph_api::AuSnapshot;
    use crate::au::terms::TermId;
    use crate::containers::DenseId;
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

    /// run_uct must reject a config whose cycle mode differs from the mode
    /// the session's search space was created with, instead of silently
    /// ignoring the requested mode.
    #[test]
    fn run_uct_rejects_cycle_mode_mismatch() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let sort = eg.intern_sort("E");
        let a_op = eg.register_op0("a", sort);
        let b_op = eg.register_op0("b", sort);
        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let mut session = SearchSession::new(&snap, CycleMode::AncestorOnly);
        let config = McgsConfig {
            cycle_mode: CycleMode::CurrentInclusive,
            playouts: 1,
            ..Default::default()
        };
        let err = session
            .run_uct(a, b, &config)
            .expect_err("mismatched cycle mode must be rejected");
        assert_eq!(err, crate::au::AuError::CycleModeMismatch);
    }

    #[test]
    fn default_algorithm_is_uct() {
        assert_eq!(AuAlgorithm::default(), AuAlgorithm::Uct);
        assert_eq!(AuConfig::default().algorithm, AuAlgorithm::Uct);
    }

    #[test]
    fn session_exact() {
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
        let config = AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        };
        let result = anti_unify(&snap, fab, fac, &config).unwrap();
        assert_eq!(result.size, 4);
    }

    #[test]
    fn session_uct_matches_exact() {
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

        let exact_config = AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        };
        let exact_result = anti_unify(&snap, fab, fac, &exact_config).unwrap();

        let uct_config = AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts: 500,
            ..Default::default()
        };
        let uct_result = anti_unify(&snap, fab, fac, &uct_config).unwrap();

        assert_eq!(uct_result.completion, Completion::Exact);
        assert_eq!(
            uct_result.pool.quality(uct_result.term_id),
            exact_result.pool.quality(exact_result.term_id)
        );
    }

    /// A session uses the same cycle policy for UCT and warm Exact. Side mode
    /// writes a contextual certificate; pair mode additionally writes the
    /// cycle-global certificate produced by bounded pair relaxation.
    #[test]
    fn warm_exact_honors_the_session_cycle_mode() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let sort = eg.intern_sort("E");
        let a_op = eg.register_op0("a", sort);
        let f = eg.register_op1("f", sort, sort);
        let h = eg.register_op2("h", sort, sort, sort);

        let c0 = eg.add(a_op, &[]);
        let c3 = eg.add(f, &[c0]);
        let c1 = eg.add(h, &[c3, c3]);
        let c2 = eg.add(h, &[c0, c1]);
        let c3_h = eg.add(h, &[c0, c3]);
        eg.merge(c3, c3_h);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(c2).unwrap();
        let r = snap.class_of(c3).unwrap();
        for (cycle_mode, expected) in [
            (CycleMode::AncestorOnly, (9, 7)),
            (CycleMode::CurrentInclusive, (9, 9)),
            (CycleMode::Pair, (8, 3)),
        ] {
            let mut session = SearchSession::new(&snap, cycle_mode);
            let config = McgsConfig {
                playouts: 10_000,
                cycle_mode,
                closed_bit: true,
                ..Default::default()
            };

            let (uct, uct_completion) = session.run_uct(c2, c3, &config).unwrap();
            assert_eq!(uct_completion, Completion::Exact);
            assert_eq!(session.pool_quality(uct), expected);

            let (exact, exact_completion) =
                session.run_exact_warm(c2, c3, false, false, None).unwrap();
            assert_eq!(exact_completion, Completion::Exact);
            assert_eq!(session.pool_quality(exact), expected);

            let (empty_l, empty_r) = session.space.empty_contexts();
            let (root_or, _) = session.space.get_or_insert_or_node(
                l,
                r,
                empty_l,
                empty_r,
                snap.best_size(l),
                snap.best_size(r),
            );
            assert!(session.results.is_exact(root_or));
            assert_eq!(
                session.results.is_global_exact(root_or),
                cycle_mode == CycleMode::Pair
            );
        }
    }

    #[test]
    fn session_identical_returns_size_1() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let a = eg.add(a_op, &[]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();

        for alg in [AuAlgorithm::Exact, AuAlgorithm::Uct] {
            let config = AuConfig {
                algorithm: alg,
                playouts: 10,
                ..Default::default()
            };
            let result = anti_unify(&snap, a, a, &config).unwrap();
            assert_eq!(result.size, 1, "algorithm {:?} failed", alg);
        }
    }

    /// Gate: for both public algorithms, both projections of the result must contain
    /// no Variants and match a term of the source class (validity oracle, §2.7).
    #[test]
    fn projections_are_variant_free_all_algorithms() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let f_op = eg.register_op2("f", int, int, int);
        let and_op = eg.register_set("and", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let fab = eg.add(f_op, &[a, b]);
        let fcb = eg.add(f_op, &[c, b]);
        let left = eg.add(and_op, &[fab, a]);
        let right = eg.add(and_op, &[fcb, c]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();

        for alg in [AuAlgorithm::Exact, AuAlgorithm::Uct] {
            let config = AuConfig {
                algorithm: alg,
                playouts: 200,
                ..Default::default()
            };
            let mut result = anti_unify(&snap, left, right, &config).unwrap();
            let l_proj = result.pool.project(result.term_id, 0);
            let r_proj = result.pool.project(result.term_id, 1);
            assert!(
                !result.pool.has_variants(l_proj),
                "{alg:?}: left projection still has Variants"
            );
            assert!(
                !result.pool.has_variants(r_proj),
                "{alg:?}: right projection still has Variants"
            );
        }
    }

    /// Gate: the exact solver must not truncate AC matrix enumeration. With 5
    /// distinct children per side there are 5! = 120 bijections (> the MCGS
    /// A_max of 32); the optimum pairs the 4 shared children diagonally.
    #[test]
    fn exact_large_ac_not_truncated() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let ops: Vec<_> = (0..6)
            .map(|i| eg.register_op0(&format!("k{i}"), int))
            .collect();
        let and_op = eg.register_set("and", int, int);

        let ks: Vec<_> = ops.iter().map(|&o| eg.add(o, &[])).collect();
        // left = {k0..k4}, right = {k1..k5}: 4 shared children.
        let left = eg.add(and_op, &[ks[0], ks[1], ks[2], ks[3], ks[4]]);
        let right = eg.add(and_op, &[ks[1], ks[2], ks[3], ks[4], ks[5]]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let config = AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        };
        let result = anti_unify(&snap, left, right, &config).unwrap();
        // and(k1, k2, k3, k4, Variants(k0, k5)): 1 + 4 + 0 + 1 + 1 = 7.
        assert_eq!(result.size, 7);
    }

    #[test]
    fn compression_ratio_basic() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let ac = snap.class_of(a).unwrap();
        let bc = snap.class_of(b).unwrap();

        // AU(a,b) = Variants(a,b), size 2. Both inputs are size 1.
        // cr = (2 - 1) / 1 = 1.0
        let cr = compression_ratio(&snap, ac, bc, 2);
        assert!((cr - 1.0).abs() < 1e-10);
    }

    #[test]
    fn search_session_mark_restore() {
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
        let mut session = SearchSession::new(&snap, CycleMode::AncestorOnly);

        // Mark with empty state.
        let token = session.mark();

        // Do some work: insert an OR node and a term.
        let lc = snap.class_of(fab).unwrap();
        let rc = snap.class_of(fac).unwrap();
        let ctx = session.space.contexts.empty();
        let (or_id, _) = session.space.get_or_insert_or_node(
            lc,
            rc,
            ctx,
            ctx,
            snap.best_size(lc),
            snap.best_size(rc),
        );
        assert_eq!(session.space.or_arena.len(), 1);
        assert_eq!(session.pool.len(), 0);

        // Intern a term.
        let term = session.pool.intern(TermOp::EGraph(a_op), &[]);
        assert_eq!(session.pool.len(), 1);
        assert!(
            session
                .results
                .offer_global(or_id, term, session.pool.quality(term))
        );
        session.results.mark_global_exact(or_id);
        assert_eq!(session.results.best_global_term(or_id), Some(term));
        assert!(session.results.is_global_exact(or_id));

        // Restore: all state rolled back to empty.
        session.restore(token);
        assert_eq!(session.space.or_arena.len(), 0);
        assert_eq!(session.pool.len(), 0);
        assert_eq!(session.results.best_global_term(or_id), None);
        assert!(!session.results.is_global_exact(or_id));
    }

    #[test]
    fn search_session_rejects_abandoned_token_atomically() {
        use crate::au::space::OrId;

        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let sort = eg.intern_sort("E");
        let a_op = eg.register_op0("a", sort);
        let b_op = eg.register_op0("b", sort);
        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let mut session = SearchSession::new(&snap, CycleMode::AncestorOnly);
        let ac = snap.class_of(a).unwrap();
        let bc = snap.class_of(b).unwrap();
        let or0 = OrId::from_usize(0);
        let or1 = OrId::from_usize(1);
        let t0 = TermId::from_usize(0);
        let t1 = TermId::from_usize(1);

        let outer = session.mark();
        session.action_cache.insert(ac, ac, Vec::new());
        session.results.offer(or0, t0, (2, 2));
        let abandoned = session.mark();
        session.action_cache.insert(bc, bc, Vec::new());
        session.results.offer(or1, t1, (1, 1));

        // Returning to the outer frame abandons the inner token's history.
        session.restore(outer);

        // Establish a distinct current branch whose state must survive rejection.
        session.action_cache.insert(ac, ac, Vec::new());
        session.action_cache.insert(bc, bc, Vec::new());
        session.results.offer(or0, t0, (2, 2));
        session.results.offer(or1, t1, (1, 1));

        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            session.restore(abandoned);
        }));
        assert!(outcome.is_err(), "an abandoned token must be rejected");
        assert!(
            session.action_cache.get(bc, bc).is_some(),
            "failed validation must not truncate the current action-cache branch"
        );
        assert_eq!(
            session.results.best_term(or1),
            Some(t1),
            "failed validation must not truncate current best results"
        );
    }
}
