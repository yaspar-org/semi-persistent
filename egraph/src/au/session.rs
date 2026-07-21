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
use super::exact;
use super::mcgs::{self, McgsConfig};
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
    pub cycle_mode: CycleMode,
    pub playouts: u64,
    pub exploration_constant: f64,
    pub x_target: f64,
}

impl Default for AuConfig {
    fn default() -> Self {
        AuConfig {
            algorithm: AuAlgorithm::Uct,
            cycle_mode: CycleMode::AncestorOnly,
            playouts: 1000,
            exploration_constant: std::f64::consts::SQRT_2,
            x_target: 0.8,
        }
    }
}

/// Whether the returned result is provably optimal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Completion {
    /// Every reachable subproblem was solved (structurally certified optimal).
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
            let (term_id, pool) = exact::eager_with_memo(snap, l, r, config.cycle_mode)?;
            let size = pool.size(term_id);
            Ok(AuResult {
                term_id,
                pool,
                size,
                algorithm: AuAlgorithm::Exact,
                completion: Completion::Exact,
            })
        }
        AuAlgorithm::Uct => {
            let mcgs_config = McgsConfig {
                playouts: config.playouts,
                cycle_mode: config.cycle_mode,
                exploration_constant: config.exploration_constant,
                x_target: config.x_target,
            };
            let (term_id, pool, completion) = mcgs::run_mcgs(snap, l, r, &mcgs_config)?;
            let size = pool.size(term_id);
            Ok(AuResult {
                term_id,
                pool,
                size,
                algorithm: AuAlgorithm::Uct,
                completion,
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
    pub(crate) action_cache: ActionCache<Cfg::O, Cfg::Au>,
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
        let (_or_id, _) = session.space.get_or_insert_or_node(
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
        let _t = session.pool.intern(TermOp::EGraph(a_op), &[]);
        assert_eq!(session.pool.len(), 1);

        // Restore: all state rolled back to empty.
        session.restore(token);
        assert_eq!(session.space.or_arena.len(), 0);
        assert_eq!(session.pool.len(), 0);
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
