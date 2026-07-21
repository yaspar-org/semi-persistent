// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Monte-Carlo Graph Search for anti-unification (§3.3).
//!
//! Playout = selection (UCT at OR nodes, round-robin at AND nodes), expansion,
//! greedy rollout (§A.4) for first estimates, then path-only backpropagation:
//! every AND node on the traversed path recomputes its value idempotently from
//! its children (§2.6), composes its children's stored best results into a
//! candidate term, and offers it to its parent's best-result entry (§3.3).
//! That composition step is what lets the search improve past the initial
//! greedy rollout and converge to the exact optimum on exhausted graphs.
//!
//! Milestone scope: UCT selection and round-robin AND allocation only
//! (PUCT, uct_and/lct_and, priors, and the completion counter are deferred;
//! see anti-unification-plan.md "Delivered / Deferred").

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
use super::transport::{
    Cell, TransportProblem, TransportProblemF64, solve_transport, solve_transport_f64,
};

/// MCGS configuration.
#[derive(Debug, Clone)]
pub struct McgsConfig {
    pub playouts: u64,
    pub cycle_mode: CycleMode,
    /// UCT exploration constant C (§3.3.4). Default √2.
    pub exploration_constant: f64,
    /// Normalization target (§2.5). Default 0.8.
    pub x_target: f64,
}

impl Default for McgsConfig {
    fn default() -> Self {
        McgsConfig {
            playouts: 1000,
            cycle_mode: CycleMode::AncestorOnly,
            exploration_constant: std::f64::consts::SQRT_2,
            x_target: 0.8,
        }
    }
}

/// Per-OR-node statistics (§4.3). `value` is Q(n), maintained idempotently:
/// Q(n) = (U(n) + Σ_a N(n,a)·Q(and_a)) / (1 + Σ_a N(n,a)).
struct OrStatsData {
    /// U(n): the node's first rollout estimate, one permanent unit-weight sample.
    initial_value: f64,
    /// Q(n), recomputed from children on every backpropagation through this node.
    value: f64,
    /// min(best_size(l), best_size(r)): the perfect-compression point (§2.5).
    /// Shared normalization basis for ALL of this node's actions.
    min_size: f64,
    /// max(best_size(l), best_size(r)): the normalization scale (§2.5).
    max_size: f64,
    /// Terminal: l == r, exact, or no surviving actions.
    terminal: bool,
    /// Per-action edge visits N(n,a): how often THIS node's selector chose a (§2.6).
    edge_visits: Vec<u64>,
    /// Realized AND statistics per action (None = unrealized).
    edge_and: Vec<Option<usize>>,
}

/// Per-AND-node statistics. Q(n) = 1 + Σ_i pair_count_i · Q(child_i).
struct AndStatsData {
    /// The OR stats index this AND node belongs to.
    parent: usize,
    /// The action's operator (as raw usize; reconstructed via `Cfg::O::from_usize`).
    op_raw: usize,
    /// Whether the operator's canonical kind is commutative (child order canonical
    /// vs positional in composed result terms).
    commutative: bool,
    /// Q(n).
    value: f64,
    /// Child OR stats indices, in action-pair order. For transport-AND-nodes,
    /// only non-blocked cells appear; `transport_cell_map` maps flat (i*cols+j)
    /// to the index in this vec (or `None` for blocked cells).
    child_or_stats: Vec<usize>,
    /// Pair multiplicities, parallel to `child_or_stats`. For transport-AND-nodes
    /// these are recomputed from the transport argmin on every backprop; for fixed
    /// actions they are immutable.
    child_counts: Vec<u32>,
    /// AND-selector edge visits N(n,i), parallel to `child_or_stats` (§3.3.5).
    child_visits: Vec<u64>,
    /// Round-robin counter for the default AND selector (§3.3.5).
    round_robin: u64,
    /// For transport-AND-nodes: the row supplies (left monomial multiplicities).
    /// Empty for fixed-action AND-nodes. When set, value recomputation runs
    /// min-cost transport over the cell Qs and updates `child_counts` to the
    /// argmin flow.
    transport_rows: Vec<u32>,
    /// For transport-AND-nodes: the column demands (right monomial multiplicities).
    transport_cols: Vec<u32>,
    /// For transport-AND-nodes: maps flat cell index (i*cols+j) to the position
    /// in `child_or_stats`, or `None` for cycle-blocked cells. Empty for fixed
    /// actions.
    transport_cell_map: Vec<Option<usize>>,
}

/// The MCGS overlay state. Whole-session persistence is composed in commit 3;
/// this boundary keeps ordinary in-memory statistics only.
pub(crate) struct McgsState {
    or_stats: Vec<OrStatsData>,
    and_stats: Vec<AndStatsData>,
    or_stats_map: hashbrown::HashMap<OrId, usize>,
    stats_to_or: Vec<OrId>,
}

impl McgsState {
    pub(crate) fn new() -> Self {
        McgsState {
            or_stats: Vec::new(),
            and_stats: Vec::new(),
            or_stats_map: hashbrown::HashMap::new(),
            stats_to_or: Vec::new(),
        }
    }

    fn set_or_initial_value(&mut self, i: usize, v: f64) {
        self.or_stats[i].initial_value = v;
    }

    fn set_or_value(&mut self, i: usize, v: f64) {
        self.or_stats[i].value = v;
    }

    fn bump_or_edge_visit(&mut self, i: usize, a: usize) {
        self.or_stats[i].edge_visits[a] += 1;
    }

    fn set_or_edge_and(&mut self, i: usize, a: usize, v: Option<usize>) {
        self.or_stats[i].edge_and[a] = v;
    }

    fn set_and_value(&mut self, i: usize, v: f64) {
        self.and_stats[i].value = v;
    }

    fn set_and_child_count(&mut self, i: usize, c: usize, v: u32) {
        self.and_stats[i].child_counts[c] = v;
    }

    fn bump_and_child_visit(&mut self, i: usize, c: usize) {
        self.and_stats[i].child_visits[c] += 1;
    }

    fn bump_and_round_robin(&mut self, i: usize) {
        self.and_stats[i].round_robin += 1;
    }
}

/// Run MCGS from a root class pair, returning the best anti-unifier found.
///
/// Errors with `AuError::NoFiniteRepresentative` if either root (or any class
/// reachable from one) has no admissible finite member (§4.1).
pub fn run_mcgs<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l_root: AuClassId,
    r_root: AuClassId,
    config: &McgsConfig,
) -> Result<(TermId, TermPool<Cfg::O, Cfg::V>, super::session::Completion), super::AuError>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut space = SearchSpace::new(config.cycle_mode);
    let mut pool = TermPool::new();
    // MCGS skips AC/ACI matrix materialization; those operators use transport
    // AND-nodes instead (zero matrix enumeration, same as exact).
    let mut action_cache = ActionCache::without_ac_actions(usize::MAX);
    let mut results = BestResults::new();
    let mut state = McgsState::new();
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
    space: &mut SearchSpace,
    pool: &mut TermPool<Cfg::O, Cfg::V>,
    action_cache: &mut ActionCache<Cfg::O>,
    results: &mut BestResults,
    state: &mut McgsState,
    l_root: AuClassId,
    r_root: AuClassId,
    config: &McgsConfig,
) -> Result<(TermId, super::session::Completion), super::AuError>
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

    // Anytime floor: the syntactic seed exists from the first instant (§3.1).
    let seed = evaluate_generalize_action(snap, pool, l_root, r_root);
    results.ensure_capacity(root_or);
    results.offer(root_or, seed, pool.quality(seed));

    let root_idx = ensure_or_stats(snap, space, action_cache, results, state, root_or);

    if !state.or_stats[root_idx].terminal {
        // First estimate U(root) from the greedy rollout; its term is also a
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
fn or_postorder(state: &McgsState, root_idx: usize) -> Vec<usize> {
    let mut postorder: Vec<usize> = Vec::new();
    let mut mark: Vec<u8> = vec![0; state.or_stats.len()]; // 0 unseen, 1 active, 2 done
    let mut stack: Vec<(usize, usize)> = vec![(root_idx, 0)]; // (or_idx, child cursor)
    while let Some(&mut (or_idx, ref mut cursor)) = stack.last_mut() {
        if mark[or_idx] == 2 {
            stack.pop();
            continue;
        }
        mark[or_idx] = 1;
        let children: Vec<usize> = state.or_stats[or_idx]
            .edge_and
            .iter()
            .flatten()
            .flat_map(|&a| state.and_stats[a].child_or_stats.iter().copied())
            .collect();
        if *cursor < children.len() {
            let child = children[*cursor];
            *cursor += 1;
            if mark[child] == 0 {
                stack.push((child, 0));
            }
        } else {
            mark[or_idx] = 2;
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
    pool: &mut TermPool<Cfg::O, Cfg::V>,
    results: &mut BestResults,
    state: &mut McgsState,
    root_idx: usize,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    for &or_idx in &or_postorder(state, root_idx) {
        let edges: Vec<usize> = state.or_stats[or_idx]
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
fn close_values(state: &mut McgsState, root_idx: usize) {
    for &or_idx in &or_postorder(state, root_idx) {
        let edges: Vec<usize> = state.or_stats[or_idx]
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
fn is_structurally_complete(state: &McgsState, or_idx: usize) -> bool {
    // Tri-state: 0 = unseen, 1 = active (on current path), 2 = memoized complete.
    let mut visited: Vec<u8> = vec![0; state.or_stats.len()];
    is_or_complete(state, or_idx, &mut visited)
}

fn is_or_complete(state: &McgsState, or_idx: usize, visited: &mut [u8]) -> bool {
    match visited[or_idx] {
        2 => return true,  // memoized: already verified complete
        1 => return false, // active: cycle, conservatively reject
        _ => {}
    }
    visited[or_idx] = 1; // mark active

    let stats = &state.or_stats[or_idx];
    if stats.terminal {
        visited[or_idx] = 2;
        return true;
    }
    // Every legal action must have been expanded.
    if stats.edge_and.iter().any(|e| e.is_none()) {
        return false;
    }
    // Every expanded AND-node must be complete.
    let complete = stats.edge_and.iter().all(|e| {
        let and_idx = e.unwrap();
        is_and_complete(state, and_idx, visited)
    });
    if complete {
        visited[or_idx] = 2; // memoize
    }
    complete
}

fn is_and_complete(state: &McgsState, and_idx: usize, visited: &mut [u8]) -> bool {
    state.and_stats[and_idx]
        .child_or_stats
        .iter()
        .all(|&child| is_or_complete(state, child, visited))
}

/// One feasible AC/ACI transport action at an OR node: a representation pair
/// with its cycle-blocked cell mask. Only pairs admitting a feasible flow
/// (zero-cost transport with blocked cells Forbidden) become actions; a pair
/// with legal cells can still be Hall-infeasible (a blocked row with positive
/// supply), and such pairs must not consume an action slot.
struct TransportActionDesc<O> {
    op: O,
    left: ac_repr::Monomial,
    right: ac_repr::Monomial,
    /// Flat row-major r*c mask: true = cell is not cycle-blocked.
    legal_cells: Vec<bool>,
}

/// Enumerate the feasible transport actions for `(l, r)` at `or_id`. Single
/// source of truth for action counting, expansion indexing, and rollout.
fn transport_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &SearchSpace,
    or_id: OrId,
    l: AuClassId,
    r: AuClassId,
) -> Vec<TransportActionDesc<Cfg::O>>
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
    space: &mut SearchSpace,
    action_cache: &mut ActionCache<Cfg::O>,
    results: &mut BestResults,
    state: &mut McgsState,
    or_id: OrId,
) -> usize
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if let Some(&idx) = state.or_stats_map.get(&or_id) {
        return idx;
    }

    let l = *space.or_arena.left.get(or_id.to_usize());
    let r = *space.or_arena.right.get(or_id.to_usize());
    let l_best = *space.or_arena.left_best_size.get(or_id.to_usize()) as f64;
    let r_best = *space.or_arena.right_best_size.get(or_id.to_usize()) as f64;

    let num_actions = if l == r {
        0
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
        // Add one edge per feasible AC/ACI transport action (flow-verified).
        count += transport_actions(snap, space, or_id, l, r).len();
        count
    };

    let terminal = l == r || num_actions == 0 || results.is_exact(or_id);
    // Terminal nodes take their stored best result as their permanent value.
    let value = if terminal {
        results.best_size(or_id) as f64
    } else {
        f64::INFINITY
    };

    let idx = state.or_stats.len();
    state.or_stats.push(OrStatsData {
        initial_value: value,
        value,
        min_size: l_best.min(r_best),
        max_size: l_best.max(r_best),
        terminal,
        edge_visits: vec![0; num_actions],
        edge_and: vec![None; num_actions],
    });
    state.or_stats_map.insert(or_id, idx);
    state.stats_to_or.push(or_id);
    idx
}

/// One playout (§3.3): descend by UCT / round-robin, expand the first
/// unrealized action met, rollout fresh children, then backpropagate along the
/// traversed path (children before parents), recomputing values idempotently
/// and offering composed results.
#[allow(clippy::too_many_arguments)]
fn playout<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace,
    pool: &mut TermPool<Cfg::O, Cfg::V>,
    action_cache: &mut ActionCache<Cfg::O>,
    results: &mut BestResults,
    state: &mut McgsState,
    root_idx: usize,
    config: &McgsConfig,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    // The traversed path: AND stats indices, root-side first.
    let mut path: Vec<usize> = Vec::new();
    let mut current = root_idx;

    loop {
        if state.or_stats[current].terminal {
            break;
        }

        // First unrealized action, in ascending action order (UCT expansion §3.3.4).
        let unrealized = state.or_stats[current]
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
            for pos in 0..state.and_stats[and_idx].child_or_stats.len() {
                let child_idx = state.and_stats[and_idx].child_or_stats[pos];
                if state.or_stats[child_idx].value.is_infinite() {
                    let child_or = state.stats_to_or[child_idx];
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
        let and_idx = state.or_stats[current].edge_and[action_idx].unwrap();
        path.push(and_idx);

        // AND allocation: round-robin (§3.3.5), with its own edge visit.
        let pos = (state.and_stats[and_idx].round_robin as usize)
            % state.and_stats[and_idx].child_or_stats.len();
        state.bump_and_round_robin(and_idx);
        state.bump_and_child_visit(and_idx, pos);
        current = state.and_stats[and_idx].child_or_stats[pos];
    }

    // Backpropagation (§3.3.3): deepest AND first, then rootward. Each AND
    // recomputes Q from its children, composes their best results into a
    // candidate, and offers it to its parent OR; the parent recomputes Q.
    for &and_idx in path.iter().rev() {
        recompute_and_value(state, and_idx);
        compose_and_offer(snap, pool, results, state, and_idx);
        let parent = state.and_stats[and_idx].parent;
        recompute_or_value(state, parent);
    }
}

/// UCT score (§3.3.4):
/// `score(a) = reward(Q(and_a)) + C * sqrt(sum_N) / (1 + N(n,a))`
/// evaluated in ascending action order; the first maximum wins.
///
/// All actions are normalized against the parent OR node's own (min_size, max_size)
/// (§2.5.1 property A); per-action bases can invert the size preference.
fn select_uct(state: &McgsState, or_idx: usize, config: &McgsConfig) -> usize {
    let stats = &state.or_stats[or_idx];
    let total: u64 = stats.edge_visits.iter().sum();
    let sqrt_total = (total as f64).sqrt();

    let mut best_score = f64::NEG_INFINITY;
    let mut best_action = 0;

    for (a, edge) in stats.edge_and.iter().enumerate() {
        let and_idx = edge.expect("select_uct requires a fully expanded node");
        let and = &state.and_stats[and_idx];
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

/// AND value equation (§3.3): for fixed-action AND-nodes,
/// `Q(n) = 1 + Σ_i count_i · Q(child_i)`. For transport-AND-nodes,
/// `Q(n) = 1 + min_X Σ_ij x_ij · Q(cell_ij)` where X is the transport argmin.
fn recompute_and_value(state: &mut McgsState, and_idx: usize) {
    let is_transport = !state.and_stats[and_idx].transport_rows.is_empty();
    if is_transport {
        recompute_transport_and_value(state, and_idx);
    } else {
        let and = &state.and_stats[and_idx];
        let mut q = 1.0;
        for (i, &child) in and.child_or_stats.iter().enumerate() {
            q += and.child_counts[i] as f64 * state.or_stats[child].value;
        }
        state.set_and_value(and_idx, q);
    }
}

/// Transport-AND value recomputation: solve min-cost flow over current cell Qs,
/// update child_counts to the argmin flow, and set Q accordingly.
fn recompute_transport_and_value(state: &mut McgsState, and_idx: usize) {
    let rows = state.and_stats[and_idx].transport_rows.clone();
    let cols = state.and_stats[and_idx].transport_cols.clone();
    let n_rows = rows.len();
    let n_cols = cols.len();
    let children = state.and_stats[and_idx].child_or_stats.clone();

    // Build the float cost matrix from current child Q values via the cell map.
    // Native f64 costs: no scalarization or rounding, the exact Q argmin over
    // the represented values is preserved. Non-finite Qs are Forbidden.
    let cell_map = state.and_stats[and_idx].transport_cell_map.clone();
    let mut cost: Vec<Vec<Option<f64>>> = vec![vec![None; n_cols]; n_rows];
    for flat in 0..(n_rows * n_cols) {
        if let Some(child_pos) = cell_map[flat] {
            let q = state.or_stats[children[child_pos]].value;
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
            // Zero out child_counts (logged), then fill from flow via cell_map.
            for c in 0..state.and_stats[and_idx].child_counts.len() {
                if state.and_stats[and_idx].child_counts[c] != 0 {
                    state.set_and_child_count(and_idx, c, 0);
                }
            }
            let mut q = 1.0;
            for flat in 0..(n_rows * n_cols) {
                let i = flat / n_cols;
                let j = flat % n_cols;
                let x = solution.flow[i][j];
                if x > 0
                    && let Some(child_pos) = cell_map[flat]
                {
                    state.set_and_child_count(and_idx, child_pos, x);
                    q += x as f64 * state.or_stats[children[child_pos]].value;
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
fn recompute_or_value(state: &mut McgsState, or_idx: usize) {
    let stats = &state.or_stats[or_idx];
    if stats.terminal {
        return;
    }
    let mut sum = stats.initial_value;
    let mut total: u64 = 0;
    for (a, edge) in stats.edge_and.iter().enumerate() {
        if let Some(and_idx) = *edge {
            let n = stats.edge_visits[a];
            sum += n as f64 * state.and_stats[and_idx].value;
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
    pool: &mut TermPool<Cfg::O, Cfg::V>,
    results: &mut BestResults,
    state: &McgsState,
    and_idx: usize,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let and = &state.and_stats[and_idx];
    let is_transport = !and.transport_rows.is_empty();

    let children: Vec<(TermId, u32)> = if is_transport {
        // Solve transport over lexicographic best-result qualities for composition.
        let n_rows = and.transport_rows.len();
        let n_cols = and.transport_cols.len();
        let cell_map = &and.transport_cell_map;
        let mut cost = vec![vec![Cell::Forbidden; n_cols]; n_rows];
        let mut terms: Vec<Option<TermId>> = vec![None; n_rows * n_cols];
        for flat in 0..(n_rows * n_cols) {
            if let Some(child_pos) = cell_map[flat] {
                let child_or = state.stats_to_or[and.child_or_stats[child_pos]];
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
            row_supply: and.transport_rows.clone(),
            col_demand: and.transport_cols.clone(),
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
            let child_or = state.stats_to_or[child_idx];
            match results.best_term(child_or) {
                Some(t) => out.push((t, and.child_counts[i])),
                None => return,
            }
        }
        out
    };

    let op = Cfg::O::from_usize(and.op_raw);
    let candidate = pool.intern_action_result(TermOp::EGraph(op), &children, and.commutative);
    let parent_or = state.stats_to_or[and.parent];
    let _ = snap;
    results.offer(parent_or, candidate, pool.quality(candidate));
}

/// Realize one edge: allocate the AND statistics struct and all child OR nodes.
/// `action_idx` indexes first over non-AC cached actions, then over AC/ACI
/// representation pairs (transport-AND-nodes).
#[allow(clippy::too_many_arguments)]
fn expand_action<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace,
    pool: &mut TermPool<Cfg::O, Cfg::V>,
    action_cache: &mut ActionCache<Cfg::O>,
    results: &mut BestResults,
    state: &mut McgsState,
    or_idx: usize,
    action_idx: usize,
) -> usize
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let or_id = state.stats_to_or[or_idx];
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
        let and_idx = state.and_stats.len();
        state.and_stats.push(AndStatsData {
            parent: or_idx,
            op_raw: action.op.to_usize(),
            commutative: snap.op_is_commutative(action.op),
            value: f64::INFINITY,
            child_or_stats,
            child_counts,
            child_visits: vec![0; arity],
            round_robin: 0,
            transport_rows: Vec::new(),
            transport_cols: Vec::new(),
            transport_cell_map: Vec::new(),
        });
        and_idx
    } else {
        // AC/ACI transport-AND-node: one per feasible transport action.
        let transport_idx = action_idx - non_ac_count;
        let descs = transport_actions(snap, space, or_id, l, r);
        let desc = &descs[transport_idx];
        let (op, lm, rm) = (desc.op, &desc.left, &desc.right);
        let n_rows = lm.len();
        let n_cols = rm.len();

        // Create children for legal cells; blocked cells map to None and are
        // Forbidden in the transport combiner.
        let mut cell_map: Vec<Option<usize>> = Vec::with_capacity(n_rows * n_cols);
        let mut filtered_children: Vec<usize> = Vec::new();
        for (i, (lc, _)) in lm.iter().enumerate() {
            for (j, (rc, _)) in rm.iter().enumerate() {
                if !desc.legal_cells[i * n_cols + j] {
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
        let and_idx = state.and_stats.len();
        state.and_stats.push(AndStatsData {
            parent: or_idx,
            op_raw: op.to_usize(),
            commutative: true,
            value: f64::INFINITY,
            child_or_stats: filtered_children,
            child_counts: vec![0; arity],
            child_visits: vec![0; arity],
            round_robin: 0,
            transport_rows: lm.iter().map(|(_, k)| *k).collect(),
            transport_cols: rm.iter().map(|(_, k)| *k).collect(),
            transport_cell_map: cell_map,
        });
        and_idx
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
    l: AuClassId,
    r: AuClassId,
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
fn initial_rollout<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace,
    pool: &mut TermPool<Cfg::O, Cfg::V>,
    action_cache: &mut ActionCache<Cfg::O>,
    or_id: OrId,
) -> TermId
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let l = *space.or_arena.left.get(or_id.to_usize());
    let r = *space.or_arena.right.get(or_id.to_usize());

    if l == r {
        return build_best_term(snap, pool, l);
    }

    generate_actions(snap, action_cache, l, r);
    let actions = action_cache.get(l, r).unwrap().to_vec();
    let transport = transport_actions(snap, space, or_id, l, r);
    let ctx_l = *space.or_arena.left_ctx.get(or_id.to_usize());
    let ctx_r = *space.or_arena.right_ctx.get(or_id.to_usize());

    // Eager generalization is an explicit action and wins ties, so the
    // initializer can never return a result worse than this valid incumbent.
    let mut choice = InitialRolloutChoice::Generalize;
    let mut best_estimate = wide_quality(static_generalize_quality(snap, l, r));

    for (action_idx, action) in actions.iter().enumerate() {
        if action
            .pairs
            .iter()
            .any(|p| space.is_cycle_blocked(or_id, p.left, p.right))
        {
            continue;
        }

        let mut estimate = (1u128, 0u128);
        for pair in &action.pairs {
            let child = wide_quality(static_generalize_quality(snap, pair.left, pair.right));
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
        InitialRolloutChoice::Generalize => evaluate_generalize_action(snap, pool, l, r),
        InitialRolloutChoice::Structural(action_idx) => {
            let action = &actions[action_idx];
            let mut child_terms: Vec<(TermId, u32)> = Vec::with_capacity(action.pairs.len());
            for pair in &action.pairs {
                let child_ctx_l = space.derive_child_context(ctx_l, l, |c| {
                    snap.reachability().is_reachable(pair.left, c)
                });
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
                let child_term = initial_rollout(snap, space, pool, action_cache, child_or);
                child_terms.push((child_term, pair.count));
            }
            pool.intern_action_result(
                TermOp::EGraph(action.op),
                &child_terms,
                snap.op_is_commutative(action.op),
            )
        }
        InitialRolloutChoice::Transport { descriptor, flow } => {
            let desc = transport
                .into_iter()
                .nth(descriptor)
                .expect("selected transport descriptor disappeared");
            let n_cols = desc.right.len();
            let mut child_terms: Vec<(TermId, u32)> = Vec::new();
            for (i, (lc, _)) in desc.left.iter().enumerate() {
                for (j, (rc, _)) in desc.right.iter().enumerate() {
                    let count = flow[i][j];
                    if count == 0 {
                        continue;
                    }
                    debug_assert!(desc.legal_cells[i * n_cols + j]);
                    let child_ctx_l = space.derive_child_context(ctx_l, l, |c| {
                        snap.reachability().is_reachable(*lc, c)
                    });
                    let child_ctx_r = space.derive_child_context(ctx_r, r, |c| {
                        snap.reachability().is_reachable(*rc, c)
                    });
                    let (child_or, _) = space.get_or_insert_or_node(
                        *lc,
                        *rc,
                        child_ctx_l,
                        child_ctx_r,
                        snap.best_size(*lc),
                        snap.best_size(*rc),
                    );
                    let child_term = initial_rollout(snap, space, pool, action_cache, child_or);
                    child_terms.push((child_term, count));
                }
            }
            if child_terms.is_empty() {
                evaluate_generalize_action(snap, pool, l, r)
            } else {
                pool.intern_action_result(TermOp::EGraph(desc.op), &child_terms, true)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::au::exact::eager_with_memo;
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

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
    /// gate for "MCGS cannot improve beyond its initial greedy rollout".
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
            "MCGS must improve past its greedy rollout (size 10) to the optimum (9)"
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
        fn child_stats(value: f64) -> OrStatsData {
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

        let mut state = McgsState::new();
        // Row-major Q matrix: diagonal 1.9 + 1.9, crossed 1.1 + 1.1.
        state.or_stats = vec![
            child_stats(1.9),
            child_stats(1.1),
            child_stats(1.1),
            child_stats(1.9),
        ];
        state.and_stats.push(AndStatsData {
            parent: 0,
            op_raw: 0,
            commutative: true,
            value: f64::INFINITY,
            child_or_stats: vec![0, 1, 2, 3],
            child_counts: vec![0; 4],
            child_visits: vec![0; 4],
            round_robin: 0,
            transport_rows: vec![1, 1],
            transport_cols: vec![1, 1],
            transport_cell_map: vec![Some(0), Some(1), Some(2), Some(3)],
        });

        recompute_transport_and_value(&mut state, 0);
        assert!(
            (state.and_stats[0].value - 3.2).abs() < 1e-12,
            "transport must select the crossed fractional-Q optimum; got {}",
            state.and_stats[0].value
        );
        assert_eq!(state.and_stats[0].child_counts, vec![0, 1, 1, 0]);
    }

    #[test]
    fn structural_completion_rejects_unresolved_cycle() {
        let mut state = McgsState::new();
        state.or_stats.push(OrStatsData {
            initial_value: 3.0,
            value: 3.0,
            min_size: 1.0,
            max_size: 1.0,
            terminal: false,
            edge_visits: vec![1],
            edge_and: vec![Some(0)],
        });
        state.stats_to_or.push(OrId::from_usize(0));
        state.and_stats.push(AndStatsData {
            parent: 0,
            op_raw: 0,
            commutative: false,
            value: 3.0,
            child_or_stats: vec![0],
            child_counts: vec![1],
            child_visits: vec![1],
            round_robin: 1,
            transport_rows: Vec::new(),
            transport_cols: Vec::new(),
            transport_cell_map: Vec::new(),
        });

        assert!(
            !is_structurally_complete(&state, 0),
            "an unresolved cycle is not a finite structural optimality certificate"
        );
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
        fn child_stats(value: f64) -> OrStatsData {
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

        let mut state = McgsState::new();
        state.or_stats = vec![
            child_stats(1.0004),
            child_stats(1.0001),
            child_stats(1.0001),
            child_stats(1.0004),
        ];
        state.and_stats.push(AndStatsData {
            parent: 0,
            op_raw: 0,
            commutative: true,
            value: f64::INFINITY,
            child_or_stats: vec![0, 1, 2, 3],
            child_counts: vec![0; 4],
            child_visits: vec![0; 4],
            round_robin: 0,
            transport_rows: vec![1, 1],
            transport_cols: vec![1, 1],
            transport_cell_map: vec![Some(0), Some(1), Some(2), Some(3)],
        });

        recompute_transport_and_value(&mut state, 0);
        assert!(
            (state.and_stats[0].value - 3.0002).abs() < 1e-12,
            "transport must preserve the crossed sub-mill optimum; got {}",
            state.and_stats[0].value
        );
        assert_eq!(state.and_stats[0].child_counts, vec![0, 1, 1, 0]);
    }

    #[test]
    fn completion_closes_values_through_every_shared_parent() {
        fn or_stats(value: f64, terminal: bool, edge: Option<usize>) -> OrStatsData {
            OrStatsData {
                initial_value: value,
                value,
                min_size: 1.0,
                max_size: 20.0,
                terminal,
                edge_visits: edge.map_or_else(Vec::new, |_| vec![1]),
                edge_and: edge.map_or_else(Vec::new, |idx| vec![Some(idx)]),
            }
        }
        fn and_stats(parent: usize, value: f64, children: Vec<usize>) -> AndStatsData {
            let arity = children.len();
            AndStatsData {
                parent,
                op_raw: 0,
                commutative: false,
                value,
                child_or_stats: children,
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
        let mut state = McgsState::new();
        state.or_stats = vec![
            or_stats(20.0, false, Some(0)),
            or_stats(10.0, false, Some(1)),
            or_stats(10.0, false, Some(2)),
            or_stats(10.0, false, Some(3)),
            or_stats(1.0, true, None),
        ];
        state.and_stats = vec![
            and_stats(0, 21.0, vec![1, 2]),
            and_stats(1, 11.0, vec![3]),
            and_stats(2, 11.0, vec![3]),
            and_stats(3, 2.0, vec![4]),
        ];

        // Simulate backpropagation only along root -> left -> shared -> leaf.
        recompute_and_value(&mut state, 3);
        recompute_or_value(&mut state, 3);
        recompute_and_value(&mut state, 1);
        recompute_or_value(&mut state, 1);
        recompute_and_value(&mut state, 0);
        recompute_or_value(&mut state, 0);
        assert!(is_structurally_complete(&state, 0));

        // The children-first closure pass (run before certifying Exact)
        // propagates the final child values through EVERY incoming parent.
        close_values(&mut state, 0);
        let closed_root = state.or_stats[0].value;

        // Reference: manually push through the other incoming parent too;
        // no further improvement should be possible after the closure.
        recompute_and_value(&mut state, 2);
        recompute_or_value(&mut state, 2);
        recompute_and_value(&mut state, 0);
        recompute_or_value(&mut state, 0);
        assert_eq!(
            closed_root, state.or_stats[0].value,
            "Exact certification must close values/results through every incoming parent"
        );
    }

    #[test]
    fn mcgs_visit_counters_cover_the_supported_playout_budget() {
        let stats = OrStatsData {
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
}
