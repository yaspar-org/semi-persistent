// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Memoized exact solver: `eager_with_memo` (§3.2).
//!
//! Dynamic programming over cycle-context states. For non-AC operators: enumerates
//! every surviving action and takes the minimum. For AC/ACI: solves each cell
//! subproblem once, then finds the optimal matching via min-cost transportation.
//! Memoization on states = node sharing: each distinct subproblem is solved once.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::{AuIds, EGraphConfig};
use crate::containers::DenseId;
use crate::literal::LitVal;

use super::ac_repr;
use super::actions::{ActionCache, generate_actions};
use super::egraph_api::{AuSnapshot, ClassOf};
use super::results::BestResults;
use super::space::{CycleMode, SearchSpace};
use super::terms::{TermOp, TermPool, build_best_term, evaluate_generalize_action};
use super::transport::{Cell, TransportProblem, solve_transport};

/// Memo states for the exact solver, generic over the term id.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MemoState<T> {
    Empty,
    Visiting,
    Solved(T),
}

/// Run the exact solver from a root class pair, returning the optimal anti-unifier.
///
/// Errors with `AuError::NoFiniteRepresentative` if either root (or any class
/// reachable from one) has no admissible finite member (§4.1).
///
/// AC/ACI operators are solved via min-cost transportation (§3.4.4): each cell
/// subproblem is solved once and the optimal matching is found by flow, so no
/// matrix is ever materialized. Non-AC actions use the cached action list.
pub fn eager_with_memo<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l_root: ClassOf<Cfg>,
    r_root: ClassOf<Cfg>,
    cycle_mode: CycleMode,
) -> Result<(<Cfg::Au as AuIds>::Term, TermPool<Cfg::O, Cfg::V, Cfg::Au>), super::AuError>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    snap.validate_finite_from(l_root)?;
    snap.validate_finite_from(r_root)?;

    let mut space: SearchSpace<Cfg::Au> = SearchSpace::new(cycle_mode);
    let mut pool = TermPool::new();
    // AC/ACI pairs are solved by min-cost transport (zero matrix enumeration);
    // the cache materializes only the non-AC action kinds.
    let mut cache: ActionCache<Cfg::O, Cfg::Au> = ActionCache::without_ac_actions(usize::MAX);
    let mut results: BestResults<Cfg::Au> = BestResults::new();

    let empty_ctx = space.contexts.empty();
    let l_best = snap.best_size(l_root);
    let r_best = snap.best_size(r_root);
    let (root_or, _) =
        space.get_or_insert_or_node(l_root, r_root, empty_ctx, empty_ctx, l_best, r_best);

    let mut memo: Vec<MemoState<<Cfg::Au as AuIds>::Term>> = Vec::new();

    let result = solve_iterative(
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

fn ensure_memo<T: Copy, O: DenseId>(memo: &mut Vec<MemoState<T>>, or_id: O) {
    let idx = or_id.to_usize();
    if idx >= memo.len() {
        memo.resize(idx + 1, MemoState::Empty);
    }
}

/// Stage of one in-progress OR-node solve (one frame of the explicit stack).
enum Stage<Cfg: EGraphConfig> {
    /// Iterating the cached non-AC actions: `action_idx` is the current
    /// action, `pair_idx` the next child pair to solve, `child_terms` the
    /// terms solved so far for the current action.
    Actions {
        action_idx: usize,
        pair_idx: usize,
        child_terms: Vec<(<Cfg::Au as AuIds>::Term, u32)>,
    },
    /// Iterating AC/ACI operators, their representation pairs, and each
    /// pair's cell subproblems (§3.4.4). `pairs` holds the current operator's
    /// representation pairs; `cells` the active pair's cell iteration.
    Transport {
        ops: Vec<Cfg::O>,
        op_idx: usize,
        pairs: Vec<(
            ac_repr::Monomial<ClassOf<Cfg>>,
            ac_repr::Monomial<ClassOf<Cfg>>,
        )>,
        pair_idx: usize,
        cells: Option<CellState<Cfg>>,
    },
}

/// Cell iteration state for one AC/ACI representation pair: row-major cursor
/// `(i, j)` over the cost matrix, solving each legal cell subproblem once.
struct CellState<Cfg: EGraphConfig> {
    lm: ac_repr::Monomial<ClassOf<Cfg>>,
    rm: ac_repr::Monomial<ClassOf<Cfg>>,
    i: usize,
    j: usize,
    cost: Vec<Vec<Cell>>,
    cell_term: Vec<Vec<Option<<Cfg::Au as AuIds>::Term>>>,
}

/// One frame of the explicit solve stack: an OR node whose actions are being
/// enumerated. `best`/`best_quality` carry the incumbent (seeded by the
/// terminal generalize action) across stages.
struct SolveFrame<Cfg: EGraphConfig> {
    or_id: <Cfg::Au as AuIds>::Or,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
    ctx_l: <Cfg::Au as AuIds>::Context,
    ctx_r: <Cfg::Au as AuIds>::Context,
    actions: Vec<super::actions::Action<Cfg::O, Cfg::Au>>,
    best: <Cfg::Au as AuIds>::Term,
    best_quality: (u32, u32),
    stage: Stage<Cfg>,
}

/// Iterative memoized solve (explicit frame stack). Semantics are those of the
/// recursive definition (§3.2/§A.5), preserved step for step:
///
/// * memo protocol: `Empty` → mark `Visiting` on entry, publish `Solved` plus
///   `BestResults` (offer + `mark_exact`) at completion; a `Visiting` re-entry
///   is unreachable by the cycle-mode rank argument and panics loudly — a
///   silent fallback would let a parent be marked exact with a nonminimal
///   result;
/// * evaluation order: terminal generalize incumbent first, then cached non-AC
///   actions in order (child pairs left to right, candidate composed and
///   compared before the next action), then AC/ACI operators in
///   `common_ac_ops` order, representation pairs per operator, cells row-major
///   — the transport solve for a pair runs immediately after its last cell;
/// * side-effect timing: child contexts are derived and child OR nodes created
///   at descent time, exactly when the recursion would create them.
///
/// State is re-fetched from the arenas at each step (no borrow is held across
/// a child evaluation), mirroring the recursive code's re-fetch pattern.
#[allow(clippy::too_many_arguments)]
fn solve_iterative<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    cache: &mut ActionCache<Cfg::O, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    memo: &mut Vec<MemoState<<Cfg::Au as AuIds>::Term>>,
    root_or: <Cfg::Au as AuIds>::Or,
) -> <Cfg::Au as AuIds>::Term
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut stack: Vec<SolveFrame<Cfg>> = Vec::new();
    let mut pending = root_or;
    loop {
        // ── Enter `pending`: memo check, terminal case, or a new frame ──
        let or_id = pending;
        ensure_memo(memo, or_id);
        let mut done: Option<<Cfg::Au as AuIds>::Term> = None;
        match memo[or_id.to_usize()] {
            MemoState::Solved(term) => done = Some(term),
            MemoState::Visiting => {
                // Unreachable by the cycle-mode rank argument (§3.2): every child
                // state either strictly shrinks the reachable-class budget or is
                // a distinct cache state. A re-entry means that invariant is broken;
                // failing loudly is required — a silent fallback would let a parent be
                // marked exact with a nonminimal result.
                unreachable!(
                    "exact solver re-entered {or_id:?}: cycle-mode rank invariant violated"
                );
            }
            MemoState::Empty => {
                memo[or_id.to_usize()] = MemoState::Visiting;

                let l = *space.or_arena.left.get(or_id.to_usize());
                let r = *space.or_arena.right.get(or_id.to_usize());

                if l == r {
                    // Terminal case: l == r.
                    let term = build_best_term(snap, pool, l);
                    memo[or_id.to_usize()] = MemoState::Solved(term);
                    results.ensure_capacity(or_id);
                    results.offer(or_id, term, pool.quality(term));
                    results.mark_exact(or_id);
                    done = Some(term);
                } else {
                    // The terminal generalize action is part of the shared action
                    // space. Eagerly evaluate it as a valid incumbent before
                    // considering structural actions.
                    let generalize = evaluate_generalize_action(snap, pool, l, r);
                    let best_quality = pool.quality(generalize);

                    // Generate actions for this class pair.
                    generate_actions(snap, cache, l, r);
                    let actions = cache.get(l, r).unwrap().to_vec();

                    let ctx_l = *space.or_arena.left_ctx.get(or_id.to_usize());
                    let ctx_r = *space.or_arena.right_ctx.get(or_id.to_usize());

                    stack.push(SolveFrame {
                        or_id,
                        l,
                        r,
                        ctx_l,
                        ctx_r,
                        actions,
                        best: generalize,
                        best_quality,
                        stage: Stage::Actions {
                            action_idx: 0,
                            pair_idx: 0,
                            child_terms: Vec::new(),
                        },
                    });
                }
            }
        }

        // ── Advance the top frame until it descends or completes ──
        'advance: loop {
            let Some(frame) = stack.last_mut() else {
                return done.expect("exact solve must produce a term for the root");
            };

            // Deliver a completed child term to the frame's current stage.
            if let Some(term) = done.take() {
                match &mut frame.stage {
                    Stage::Actions {
                        action_idx,
                        pair_idx,
                        child_terms,
                    } => {
                        let count = frame.actions[*action_idx].pairs[*pair_idx].count;
                        child_terms.push((term, count));
                        *pair_idx += 1;
                    }
                    Stage::Transport { cells, .. } => {
                        let cell = cells
                            .as_mut()
                            .expect("transport child delivered without an active cell");
                        let (s, v) = pool.quality(term);
                        cell.cost[cell.i][cell.j] = Cell::Cost(s, v);
                        cell.cell_term[cell.i][cell.j] = Some(term);
                        cell.j += 1;
                    }
                }
            }

            // Drive the current stage forward.
            match &mut frame.stage {
                Stage::Actions {
                    action_idx,
                    pair_idx,
                    child_terms,
                } => {
                    loop {
                        if *action_idx >= frame.actions.len() {
                            // Non-AC actions exhausted: move to the AC/ACI
                            // transport stage (§3.4.4).
                            frame.stage = Stage::Transport {
                                ops: ac_repr::common_ac_ops(snap, frame.l, frame.r),
                                op_idx: 0,
                                pairs: Vec::new(),
                                pair_idx: 0,
                                cells: None,
                            };
                            continue 'advance;
                        }
                        let action = &frame.actions[*action_idx];
                        // Starting this action: check cycle filtering for each
                        // pair (before any child of this action is solved).
                        if *pair_idx == 0 && child_terms.is_empty() {
                            let blocked = action
                                .pairs
                                .iter()
                                .any(|p| space.is_cycle_blocked(frame.or_id, p.left, p.right));
                            if blocked {
                                *action_idx += 1;
                                continue;
                            }
                        }
                        if *pair_idx < action.pairs.len() {
                            // Solve the next child pair: derive child contexts
                            // and create the child OR node at descent time.
                            let pair = action.pairs[*pair_idx];
                            let (l, r, ctx_l, ctx_r) = (frame.l, frame.r, frame.ctx_l, frame.ctx_r);
                            let child_ctx_l = space.derive_child_context(ctx_l, l, |c| {
                                snap.reachability().is_reachable(pair.left, c)
                            });
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
                            pending = child_or;
                            break 'advance; // descend
                        }
                        // All child pairs solved: build the candidate term.
                        // Child order is positional semantics for ordered
                        // operators and canonical-sorted for commutative ones
                        // (P0 fix: sorting an ordered operator's children
                        // changes its meaning).
                        let commutative = snap.op_is_commutative(action.op);
                        let op = action.op;
                        let candidate =
                            pool.intern_action_result(TermOp::EGraph(op), child_terms, commutative);
                        let candidate_quality = pool.quality(candidate);
                        if candidate_quality < frame.best_quality {
                            frame.best = candidate;
                            frame.best_quality = candidate_quality;
                        }
                        *action_idx += 1;
                        *pair_idx = 0;
                        child_terms.clear();
                    }
                }
                Stage::Transport {
                    ops,
                    op_idx,
                    pairs,
                    pair_idx,
                    cells,
                } => {
                    loop {
                        if let Some(cell) = cells {
                            let rows = cell.lm.len();
                            let cols = cell.rm.len();
                            // Row-major scan for the next legal cell to solve;
                            // blocked cells stay Forbidden (forbidden transport
                            // edges).
                            let mut dispatched = false;
                            while cell.i < rows {
                                if cell.j >= cols {
                                    cell.i += 1;
                                    cell.j = 0;
                                    continue;
                                }
                                let (lc, _) = cell.lm[cell.i];
                                let (rc, _) = cell.rm[cell.j];
                                if space.is_cycle_blocked(frame.or_id, lc, rc) {
                                    cell.j += 1;
                                    continue;
                                }
                                let (l, r, ctx_l, ctx_r) =
                                    (frame.l, frame.r, frame.ctx_l, frame.ctx_r);
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
                                pending = child_or;
                                dispatched = true;
                                break;
                            }
                            if dispatched {
                                break 'advance; // descend into the cell subproblem
                            }
                            // Every cell handled: one lexicographic min-cost
                            // transportation solve returns the optimal matching
                            // directly (§3.4.4). Infeasible pairs contribute no
                            // candidate.
                            let cell = cells.take().expect("cell state present");
                            let problem = TransportProblem {
                                row_supply: cell.lm.iter().map(|(_, k)| *k).collect(),
                                col_demand: cell.rm.iter().map(|(_, k)| *k).collect(),
                                cost: cell.cost,
                            };
                            if let Some(solution) = solve_transport(&problem) {
                                // Compose the winning matrix into a term. AC/ACI
                                // kinds are commutative: canonical child order.
                                let mut child_terms: Vec<(<Cfg::Au as AuIds>::Term, u32)> =
                                    Vec::new();
                                for (i, row) in solution.flow.iter().enumerate() {
                                    for (j, &x) in row.iter().enumerate() {
                                        if x > 0 {
                                            child_terms.push((cell.cell_term[i][j].unwrap(), x));
                                        }
                                    }
                                }
                                let op = ops[*op_idx - 1];
                                let candidate = pool.intern_action_result(
                                    TermOp::EGraph(op),
                                    &child_terms,
                                    true,
                                );
                                let candidate_quality = pool.quality(candidate);
                                if candidate_quality < frame.best_quality {
                                    frame.best = candidate;
                                    frame.best_quality = candidate_quality;
                                }
                            }
                            *pair_idx += 1;
                            continue;
                        }
                        if *pair_idx < pairs.len() {
                            // Begin the next representation pair: fresh cost and
                            // term matrices, all cells Forbidden until solved.
                            let (lm, rm) = pairs[*pair_idx].clone();
                            let rows = lm.len();
                            let cols = rm.len();
                            *cells = Some(CellState {
                                lm,
                                rm,
                                i: 0,
                                j: 0,
                                cost: vec![vec![Cell::Forbidden; cols]; rows],
                                cell_term: vec![vec![None; cols]; rows],
                            });
                            continue;
                        }
                        if *op_idx < ops.len() {
                            // Begin the next AC/ACI operator: enumerate its
                            // representation pairs.
                            let op = ops[*op_idx];
                            *pairs = ac_repr::representation_pairs(snap, frame.l, frame.r, op);
                            *pair_idx = 0;
                            *op_idx += 1;
                            continue;
                        }
                        // All operators exhausted: this node is solved.
                        let frame = stack.pop().expect("solve stack cannot be empty");
                        memo[frame.or_id.to_usize()] = MemoState::Solved(frame.best);
                        results.ensure_capacity(frame.or_id);
                        results.offer(frame.or_id, frame.best, frame.best_quality);
                        results.mark_exact(frame.or_id);
                        done = Some(frame.best);
                        continue 'advance; // deliver to the parent frame
                    }
                }
            }
        }
    }
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
