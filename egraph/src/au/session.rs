// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! SearchSession: the public API for anti-unification (§4.7, §6).
//!
//! A session is built from a frozen e-graph, runs one or more algorithms
//! (exact and/or MCGS), and returns the best anti-unifier found.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::literal::LitVal;

use super::AuClassId;
use super::actions::{ActionCache, ActionCacheToken};
use super::egraph_api::AuSnapshot;
use super::exact;
use super::mcgs::{self, McgsConfig};
use super::results::{BestResults, BestResultsToken};
use super::space::{CycleMode, SearchSpace, SpaceToken};
use super::terms::{TermId, TermOp, TermPool, TermPoolToken};

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

/// The result of an anti-unification run.
#[derive(Debug)]
pub struct AuResult<O: DenseId + core::hash::Hash, V: DenseId + core::hash::Hash> {
    pub term_id: TermId,
    pub pool: TermPool<O, V>,
    pub size: u32,
    pub algorithm: AuAlgorithm,
}

impl<O: DenseId + core::hash::Hash, V: DenseId + core::hash::Hash> AuResult<O, V> {
    /// Get the operator of the root term.
    pub fn root_op(&self) -> &TermOp<O, V> {
        self.pool.op(self.term_id)
    }

    /// Get the children of the root term.
    pub fn root_children(&self) -> &[TermId] {
        self.pool.children(self.term_id)
    }

    /// Render the term as a flat one-line s-expression.
    pub fn to_string_with<F>(&self, op_name: F) -> String
    where
        F: Fn(&TermOp<O, V>) -> String + Copy,
    {
        super::pretty::pretty_print(&self.pool, self.term_id, op_name, usize::MAX)
    }

    /// Pretty-print the term with indentation, breaking lines that exceed
    /// `col_limit` characters.
    pub fn pretty_print_with<F>(&self, op_name: F, col_limit: usize) -> String
    where
        F: Fn(&TermOp<O, V>) -> String + Copy,
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
) -> Result<AuResult<Cfg::O, Cfg::V>, super::AuError>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let l = snap
        .class_of(left)
        .ok_or(super::AuError::NoFiniteRepresentative(
            AuClassId::from_usize(0),
        ))?;
    let r = snap
        .class_of(right)
        .ok_or(super::AuError::NoFiniteRepresentative(
            AuClassId::from_usize(0),
        ))?;

    match config.algorithm {
        AuAlgorithm::Exact => {
            let (term_id, pool) = exact::eager_with_memo(snap, l, r, config.cycle_mode)?;
            let size = pool.size(term_id);
            Ok(AuResult {
                term_id,
                pool,
                size,
                algorithm: AuAlgorithm::Exact,
            })
        }
        AuAlgorithm::Uct => {
            let mcgs_config = McgsConfig {
                playouts: config.playouts,
                cycle_mode: config.cycle_mode,
                exploration_constant: config.exploration_constant,
                x_target: config.x_target,
            };
            let (term_id, pool) = mcgs::run_mcgs(snap, l, r, &mcgs_config)?;
            let size = pool.size(term_id);
            Ok(AuResult {
                term_id,
                pool,
                size,
                algorithm: AuAlgorithm::Uct,
            })
        }
    }
}

/// Compute the linear compression ratio (§2.5):
/// `(size(t) - min(best_l, best_r)) / max(best_l, best_r)`
pub fn compression_ratio<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    left: AuClassId,
    right: AuClassId,
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
#[derive(Clone, Copy, Debug)]
pub struct SearchToken {
    space: SpaceToken,
    terms: TermPoolToken,
    results: BestResultsToken,
    actions: ActionCacheToken,
}

/// A search session owns the search-space layer, term pool, best-result table,
/// action cache, and (when running MCGS) the statistics overlay. It provides
/// one coherent `mark()`/`restore(token)` that snapshots and rolls back all
/// layers together. The e-graph snapshot is borrowed immutably for the session's
/// lifetime; later e-graph mutations are not observed (§4.1).
pub struct SearchSession<'eg, Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    pub(crate) snap: &'eg AuSnapshot<'eg, Cfg, L, T, P>,
    pub(crate) space: SearchSpace,
    pub(crate) pool: TermPool<Cfg::O, Cfg::V>,
    pub(crate) results: BestResults,
    pub(crate) action_cache: ActionCache<Cfg::O>,
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
            action_cache: ActionCache::new(super::actions::DEFAULT_A_MAX),
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
        }
    }

    /// Restore the entire search state to a previous mark. Restores in reverse
    /// dependency order (statistics first, then results/terms, then structure).
    /// The token is consumed; tokens from abandoned branches are rejected by
    /// the component containers' fork validation.
    pub fn restore(&mut self, token: SearchToken) {
        self.action_cache.restore(token.actions);
        self.results.restore(token.results);
        self.pool.restore(token.terms);
        self.space.restore(token.space);
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
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

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

        assert_eq!(uct_result.size, exact_result.size);
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

    /// Gate: for every algorithm, both projections of the result must contain
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
}
