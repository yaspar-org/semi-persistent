// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Memoized exact solver: `eager_with_memo` (§3.2).
//!
//! Dynamic programming over cycle-context states. For non-AC operators: enumerates
//! every surviving action and takes the minimum. For AC/ACI: solves each cell
//! subproblem once, then finds the optimal matching via min-cost transportation.
//! Memoization on states = node sharing: each distinct subproblem is solved once.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::literal::LitVal;

use super::AuClassId;
use super::ac_repr;
use super::actions::{ActionCache, generate_actions};
use super::egraph_api::AuSnapshot;
use super::results::BestResults;
use super::space::{CycleMode, OrId, SearchSpace};
use super::terms::{TermId, TermOp, TermPool, build_best_term, evaluate_generalize_action};
use super::transport::{Cell, TransportProblem, solve_transport};

/// Memo states for the exact solver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MemoState {
    Empty,
    Visiting,
    Solved(TermId),
}

/// Run the exact solver from a root class pair, returning the optimal anti-unifier.
///
/// Errors with `AuError::NoFiniteRepresentative` if either root (or any class
/// reachable from one) has no admissible finite member (§4.1).
///
/// The action cache is unbounded here: exactness requires every matching-count
/// matrix to remain reachable (§3.4.4), so the `A_max` materialization bound
/// applies only to the anytime searcher, never to this oracle.
pub fn eager_with_memo<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l_root: AuClassId,
    r_root: AuClassId,
    cycle_mode: CycleMode,
) -> Result<(TermId, TermPool<Cfg::O, Cfg::V>), super::AuError>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    snap.validate_finite_from(l_root)?;
    snap.validate_finite_from(r_root)?;

    let mut space = SearchSpace::new(cycle_mode);
    let mut pool = TermPool::new();
    // AC/ACI pairs are solved by min-cost transport (zero matrix enumeration);
    // the cache materializes only the non-AC action kinds.
    let mut cache = ActionCache::without_ac_actions(usize::MAX);
    let mut results = BestResults::new();

    let empty_ctx = space.contexts.empty();
    let l_best = snap.best_size(l_root);
    let r_best = snap.best_size(r_root);
    let (root_or, _) =
        space.get_or_insert_or_node(l_root, r_root, empty_ctx, empty_ctx, l_best, r_best);

    let mut memo: Vec<MemoState> = Vec::new();

    let result = solve_recursive(
        snap,
        &mut space,
        &mut pool,
        &mut cache,
        &mut results,
        &mut memo,
        root_or,
    );

    Ok((result, pool))
}

fn ensure_memo(memo: &mut Vec<MemoState>, or_id: OrId) {
    let idx = or_id.to_usize();
    if idx >= memo.len() {
        memo.resize(idx + 1, MemoState::Empty);
    }
}

fn solve_recursive<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace,
    pool: &mut TermPool<Cfg::O, Cfg::V>,
    cache: &mut ActionCache<Cfg::O>,
    results: &mut BestResults,
    memo: &mut Vec<MemoState>,
    or_id: OrId,
) -> TermId
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    ensure_memo(memo, or_id);
    match memo[or_id.to_usize()] {
        MemoState::Solved(term) => return term,
        MemoState::Visiting => {
            // Unreachable by the cycle-mode rank argument (§3.2): every recursive
            // child state either strictly shrinks the reachable-class budget or is
            // a distinct cache state. A re-entry means that invariant is broken;
            // failing loudly is required — a silent fallback would let a parent be
            // marked exact with a nonminimal result.
            unreachable!("exact solver re-entered {or_id:?}: cycle-mode rank invariant violated");
        }
        MemoState::Empty => {}
    }

    memo[or_id.to_usize()] = MemoState::Visiting;

    let l = *space.or_arena.left.get(or_id.to_usize());
    let r = *space.or_arena.right.get(or_id.to_usize());

    // Terminal case: l == r.
    if l == r {
        let term = build_best_term(snap, pool, l);
        memo[or_id.to_usize()] = MemoState::Solved(term);
        results.ensure_capacity(or_id);
        results.offer(or_id, term, pool.quality(term));
        results.mark_exact(or_id);
        return term;
    }

    // Start with the generalize seed as baseline.
    let seed = evaluate_generalize_action(snap, pool, l, r);
    let mut best = seed;
    let mut best_quality = pool.quality(seed);

    // Generate actions for this class pair.
    generate_actions(snap, cache, l, r);
    let actions = cache.get(l, r).unwrap().to_vec();

    let ctx_l = *space.or_arena.left_ctx.get(or_id.to_usize());
    let ctx_r = *space.or_arena.right_ctx.get(or_id.to_usize());

    for action in &actions {
        // Check cycle filtering for each pair in this action.
        let mut blocked = false;
        for pair in &action.pairs {
            if space.is_cycle_blocked(or_id, pair.left, pair.right) {
                blocked = true;
                break;
            }
        }
        if blocked {
            continue;
        }

        // Solve each child pair.
        let mut child_terms: Vec<(TermId, u32)> = Vec::with_capacity(action.pairs.len());

        for pair in &action.pairs {
            // Derive child contexts.
            let child_ctx_l = space
                .derive_child_context(ctx_l, l, |c| snap.reachability().is_reachable(pair.left, c));
            let child_ctx_r = space.derive_child_context(ctx_r, r, |c| {
                snap.reachability().is_reachable(pair.right, c)
            });

            let l_best_sz = snap.best_size(pair.left);
            let r_best_sz = snap.best_size(pair.right);
            let (child_or, _) = space.get_or_insert_or_node(
                pair.left,
                pair.right,
                child_ctx_l,
                child_ctx_r,
                l_best_sz,
                r_best_sz,
            );

            let child_term = solve_recursive(snap, space, pool, cache, results, memo, child_or);
            child_terms.push((child_term, pair.count));
        }

        // Build the candidate term. Child order is positional semantics for
        // ordered operators and canonical-sorted for commutative ones (P0 fix:
        // sorting an ordered operator's children changes its meaning).
        let commutative = snap.op_is_commutative(action.op);
        let candidate =
            pool.intern_action_result(TermOp::EGraph(action.op), &child_terms, commutative);
        let candidate_quality = pool.quality(candidate);

        if candidate_quality < best_quality {
            best = candidate;
            best_quality = candidate_quality;
        }
    }

    // AC/ACI operators: zero matrix enumeration. For each canonical
    // representation pair, recursively solve every legal cell subproblem once,
    // then one lexicographic min-cost transportation solve returns the optimal
    // matching directly (§3.4.4). Cycle-blocked cells are forbidden edges;
    // infeasible pairs contribute no candidate.
    for op in ac_repr::common_ac_ops(snap, l, r) {
        for (lm, rm) in ac_repr::representation_pairs(snap, l, r, op) {
            let rows = lm.len();
            let cols = rm.len();

            // Solve each cell once (memoized across the whole search); blocked
            // cells become forbidden transport edges.
            let mut cost: Vec<Vec<Cell>> = vec![vec![Cell::Forbidden; cols]; rows];
            let mut cell_term: Vec<Vec<Option<TermId>>> = vec![vec![None; cols]; rows];
            for (i, &(lc, _)) in lm.iter().enumerate() {
                for (j, &(rc, _)) in rm.iter().enumerate() {
                    if space.is_cycle_blocked(or_id, lc, rc) {
                        continue;
                    }
                    let child_ctx_l = space.derive_child_context(ctx_l, l, |c| {
                        snap.reachability().is_reachable(lc, c)
                    });
                    let child_ctx_r = space.derive_child_context(ctx_r, r, |c| {
                        snap.reachability().is_reachable(rc, c)
                    });
                    let (child_or, _) = space.get_or_insert_or_node(
                        lc,
                        rc,
                        child_ctx_l,
                        child_ctx_r,
                        snap.best_size(lc),
                        snap.best_size(rc),
                    );
                    let term = solve_recursive(snap, space, pool, cache, results, memo, child_or);
                    let (s, v) = pool.quality(term);
                    cost[i][j] = Cell::Cost(s, v);
                    cell_term[i][j] = Some(term);
                }
            }

            let problem = TransportProblem {
                row_supply: lm.iter().map(|(_, k)| *k).collect(),
                col_demand: rm.iter().map(|(_, k)| *k).collect(),
                cost,
            };
            let Some(solution) = solve_transport(&problem) else {
                continue; // infeasible under cycle blocking: no candidate here
            };

            // Compose the winning matrix into a term. AC/ACI kinds are
            // commutative: canonical child order.
            let mut child_terms: Vec<(TermId, u32)> = Vec::new();
            for (i, row) in solution.flow.iter().enumerate() {
                for (j, &x) in row.iter().enumerate() {
                    if x > 0 {
                        child_terms.push((cell_term[i][j].unwrap(), x));
                    }
                }
            }
            let candidate = pool.intern_action_result(TermOp::EGraph(op), &child_terms, true);
            let candidate_quality = pool.quality(candidate);
            if candidate_quality < best_quality {
                best = candidate;
                best_quality = candidate_quality;
            }
        }
    }

    memo[or_id.to_usize()] = MemoState::Solved(best);
    results.ensure_capacity(or_id);
    results.offer(or_id, best, best_quality);
    results.mark_exact(or_id);
    best
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

    /// Identical classes: exact solver returns best_term directly.
    #[test]
    fn exact_identical_classes() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let a = eg.add(a_op, &[]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let ac = snap.class_of(a).unwrap();

        let (term, pool) = eager_with_memo(&snap, ac, ac, CycleMode::AncestorOnly).unwrap();
        assert_eq!(pool.size(term), 1);
    }

    /// Completely different nullary ops: result is Variants(a, b), size 2.
    #[test]
    fn exact_different_leaves() {
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

        let (term, pool) = eager_with_memo(&snap, ac, bc, CycleMode::AncestorOnly).unwrap();
        // Variants(a, b) = size 2.
        assert_eq!(pool.size(term), 2);
    }

    /// Partial overlap: f(a,b) vs f(a,c) -> f(a, Variants(b,c)), size 4.
    #[test]
    fn exact_partial_overlap() {
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

        let (term, pool) = eager_with_memo(&snap, lc, rc, CycleMode::AncestorOnly).unwrap();
        // f(a, Variants(b, c)): 1(f) + 1(a) + 0(V) + 1(b) + 1(c) = 4
        assert_eq!(pool.size(term), 4);
    }

    /// E-graph with rewrites: a=f(a) (self-loop). The solver should terminate.
    #[test]
    fn exact_terminates_on_cycle() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let f_op = eg.register_op1("f", int, int);

        let a = eg.add(a_op, &[]);
        let fa = eg.add(f_op, &[a]);
        let b = eg.add(b_op, &[]);
        // Create cycle: a = f(a).
        eg.merge(a, fa);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let ac = snap.class_of(a).unwrap();
        let bc = snap.class_of(b).unwrap();

        // Should terminate without stack overflow.
        let (term, pool) = eager_with_memo(&snap, ac, bc, CycleMode::AncestorOnly).unwrap();
        // Result should be valid (finite size).
        assert!(pool.size(term) < 100);
    }

    /// Both cycle modes produce valid (finite) results.
    #[test]
    fn exact_both_cycle_modes() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let f_op = eg.register_op1("f", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let fa = eg.add(f_op, &[a]);
        let fb = eg.add(f_op, &[b]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(fa).unwrap();
        let rc = snap.class_of(fb).unwrap();

        let (t1, p1) = eager_with_memo(&snap, lc, rc, CycleMode::AncestorOnly).unwrap();
        let (t2, p2) = eager_with_memo(&snap, lc, rc, CycleMode::CurrentInclusive).unwrap();

        // Both should find f(Variants(a,b)): size 3.
        assert_eq!(p1.size(t1), 3);
        assert_eq!(p2.size(t2), 3);
    }

    /// P0 regression (ordered reorder): AU(f(a,b), f(c,b)) must be
    /// f(Variants(a,c), b) — first child the Variants, second child b — and both
    /// projections must be the original terms, not child-swapped ones.
    #[test]
    fn exact_ordered_children_positional() {
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
        let fcb = eg.add(f_op, &[c, b]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(fab).unwrap();
        let rc = snap.class_of(fcb).unwrap();

        let (term, mut pool) = eager_with_memo(&snap, lc, rc, CycleMode::AncestorOnly).unwrap();
        assert_eq!(pool.size(term), 4);

        // Structure: f(Variants(a,c), b) — the hole is at position 0.
        let kids = pool.children(term).to_vec();
        assert_eq!(kids.len(), 2);
        assert_eq!(*pool.op(kids[0]), TermOp::Variants);
        assert_eq!(*pool.op(kids[1]), TermOp::EGraph(b_op));

        // Projections land on the original terms.
        let left = pool.project(term, 0);
        let lk = pool.children(left).to_vec();
        assert_eq!(*pool.op(lk[0]), TermOp::EGraph(a_op));
        assert_eq!(*pool.op(lk[1]), TermOp::EGraph(b_op));
        let right = pool.project(term, 1);
        let rk = pool.children(right).to_vec();
        assert_eq!(*pool.op(rk[0]), TermOp::EGraph(c_op));
        assert_eq!(*pool.op(rk[1]), TermOp::EGraph(b_op));
    }

    /// P0 regression (no finite representative): a class whose only admissible
    /// member references itself must produce an error, not a garbage term.
    #[test]
    fn exact_no_finite_representative_errors() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let f_op = eg.register_op1("f", int, int);

        let a = eg.add(a_op, &[]);
        let fa = eg.add(f_op, &[a]);
        eg.merge(a, fa); // class {a, f(a), ...}
        let b = eg.add(b_op, &[]);
        eg.rebuild();
        eg.subsume(a); // only admissible member is now f(self): no finite term

        let snap = AuSnapshot::new(&eg).unwrap();
        let ac = snap.class_of(a).unwrap();
        let bc = snap.class_of(b).unwrap();

        let res = eager_with_memo(&snap, ac, bc, CycleMode::AncestorOnly);
        assert!(matches!(
            res,
            Err(crate::au::AuError::NoFiniteRepresentative(_))
        ));
    }

    /// Tie-breaking: at equal size, the factored form (more backbone) wins.
    /// class{x, f(x)} vs {f(y)}: Variants(x, f(y)) and f(Variants(x,y)) are both
    /// size 3, but the factored form has variant mass 2 < 3 and must be returned.
    #[test]
    fn exact_prefers_backbone_at_equal_size() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);
        let f_op = eg.register_op1("f", int, int);

        let x = eg.add(x_op, &[]);
        let fx = eg.add(f_op, &[x]);
        let y = eg.add(y_op, &[]);
        let fy = eg.add(f_op, &[y]);
        eg.merge(x, fx); // class of x contains f(x)
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(x).unwrap();
        let rc = snap.class_of(fy).unwrap();

        let (term, pool) = eager_with_memo(&snap, lc, rc, CycleMode::AncestorOnly).unwrap();
        assert_eq!(pool.size(term), 3);
        // The root must be the factored f, not a bare Variants.
        assert_eq!(*pool.op(term), TermOp::EGraph(f_op));
        assert_eq!(pool.variant_mass(term), 2);
    }

    /// AC operator: exact solver finds optimal matching.
    #[test]
    fn exact_ac_optimal() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let and_op = eg.register_set("and", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let and_abc = eg.add(and_op, &[a, b, c]);
        let and_bcd = eg.add(and_op, &[b, c, d]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(and_abc).unwrap();
        let rc = snap.class_of(and_bcd).unwrap();

        let (term, pool) = eager_with_memo(&snap, lc, rc, CycleMode::AncestorOnly).unwrap();
        // Greedy diagonal: b,c pair with themselves, leaves AU(a,d) = Variants(a,d).
        // and(b, c, Variants(a,d)) = 1(and) + 1(b) + 1(c) + 0(V) + 1(a) + 1(d) = 5
        assert_eq!(pool.size(term), 5);
    }

    /// Regression: virtual singleton must be available even when the class has an
    /// explicit AC member (the P0 fix). X = {f(p,q), combine(a,b)} merged;
    /// AU(X, combine(X,c)) should factor as combine(X, Variants(e,c)) = size 6.
    #[test]
    fn exact_virtual_singleton_with_explicit_member() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let sort = eg.intern_sort("E");
        let p_op = eg.register_op0("p", sort);
        let q_op = eg.register_op0("q", sort);
        let a_op = eg.register_op0("a", sort);
        let b_op = eg.register_op0("b", sort);
        let c_op = eg.register_op0("c", sort);
        let e_op = eg.register_op0("e", sort);
        let f = eg.register_op2("f", sort, sort, sort);
        let combine = eg.register_mset("combine", sort, sort);

        let p = eg.add(p_op, &[]);
        let q = eg.add(q_op, &[]);
        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let e = eg.add(e_op, &[]);
        eg.set_unit_node(combine, e);

        let x_f = eg.add(f, &[p, q]);
        let x_c = eg.add(combine, &[a, b]);
        eg.merge(x_f, x_c); // X has both f and combine members
        let right = eg.add(combine, &[x_f, c]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let (term, pool) = eager_with_memo(
            &snap,
            snap.class_of(x_f).unwrap(),
            snap.class_of(right).unwrap(),
            CycleMode::AncestorOnly,
        )
        .unwrap();
        // combine(X, Variants(e, c)): 1 + 3 + 0 + 1 + 1 = 6, vmass 2.
        assert_eq!(pool.size(term), 6);
        assert_eq!(pool.variant_mass(term), 2);
    }
}
