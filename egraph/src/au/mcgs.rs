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
use super::actions::{ActionCache, DEFAULT_A_MAX, generate_actions};
use super::egraph_api::AuSnapshot;
use super::results::BestResults;
use super::space::{CycleMode, OrId, SearchSpace};
use super::terms::{TermId, TermOp, TermPool, build_best_term, evaluate_generalize_action};

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
    edge_visits: Vec<u32>,
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
    /// Child OR stats indices, in action-pair order.
    child_or_stats: Vec<usize>,
    /// Pair multiplicities, parallel to `child_or_stats`.
    child_counts: Vec<u32>,
    /// AND-selector edge visits N(n,i), parallel to `child_or_stats` (§3.3.5).
    child_visits: Vec<u32>,
    /// Round-robin counter for the default AND selector (§3.3.5).
    round_robin: u32,
}

/// The MCGS overlay state. Semi-persistent by truncation: mark saves lengths,
/// restore truncates all vecs and clears the map. Surviving stats whose mutable
/// fields were modified are not individually rolled back; idempotent recomputation
/// (§2.6) re-derives their values from their (also restored) children on the next
/// playout. This is sound because values only improve monotonically toward the exact
/// optimum, so a fresh recomputation from restored child values produces a result
/// at least as good as the pre-mark state.
struct McgsState {
    or_stats: Vec<OrStatsData>,
    and_stats: Vec<AndStatsData>,
    or_stats_map: hashbrown::HashMap<OrId, usize>,
    stats_to_or: Vec<OrId>,
}

/// Token for restoring `McgsState`. Used by SearchSession.
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub(crate) struct McgsToken {
    or_stats_len: usize,
    and_stats_len: usize,
}

impl McgsState {
    fn new() -> Self {
        McgsState {
            or_stats: Vec::new(),
            and_stats: Vec::new(),
            or_stats_map: hashbrown::HashMap::new(),
            stats_to_or: Vec::new(),
        }
    }

    #[allow(dead_code)]
    fn mark(&self) -> McgsToken {
        McgsToken {
            or_stats_len: self.or_stats.len(),
            and_stats_len: self.and_stats.len(),
        }
    }

    #[allow(dead_code)]
    fn restore(&mut self, token: McgsToken) {
        self.or_stats.truncate(token.or_stats_len);
        self.and_stats.truncate(token.and_stats_len);
        self.stats_to_or.truncate(token.or_stats_len);
        // Rebuild the map from surviving entries.
        self.or_stats_map.clear();
        for (idx, &or_id) in self.stats_to_or.iter().enumerate() {
            self.or_stats_map.insert(or_id, idx);
        }
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
) -> Result<(TermId, TermPool<Cfg::O, Cfg::V>), super::AuError>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    snap.validate_finite_from(l_root)?;
    snap.validate_finite_from(r_root)?;

    let mut space = SearchSpace::new(config.cycle_mode);
    let mut pool = TermPool::new();
    let mut action_cache = ActionCache::new(DEFAULT_A_MAX);
    let mut results = BestResults::new();
    let mut state = McgsState::new();

    let empty_ctx = space.contexts.empty();
    let l_best = snap.best_size(l_root);
    let r_best = snap.best_size(r_root);
    let (root_or, _) =
        space.get_or_insert_or_node(l_root, r_root, empty_ctx, empty_ctx, l_best, r_best);

    // Anytime floor: the generalize seed exists from the first instant (§3.1).
    let seed = evaluate_generalize_action(snap, &mut pool, l_root, r_root);
    results.ensure_capacity(root_or);
    results.offer(root_or, seed, pool.quality(seed));

    let root_idx = ensure_or_stats(
        snap,
        &mut space,
        &mut action_cache,
        &mut results,
        &mut state,
        root_or,
    );

    if !state.or_stats[root_idx].terminal {
        // First estimate U(root) from the greedy rollout; its term is also a
        // valid result and is offered (§3.3.2).
        let rollout = greedy_rollout(snap, &mut space, &mut pool, &mut action_cache, root_or);
        results.offer(root_or, rollout, pool.quality(rollout));
        let sz = pool.size(rollout) as f64;
        state.or_stats[root_idx].initial_value = sz;
        state.or_stats[root_idx].value = sz;

        for _ in 0..config.playouts {
            playout(
                snap,
                &mut space,
                &mut pool,
                &mut action_cache,
                &mut results,
                &mut state,
                root_idx,
                config,
            );
        }
    }

    let best = results.best_term(root_or).unwrap_or(seed);
    Ok((best, pool))
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
            state.or_stats[current].edge_visits[action_idx] += 1;
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
            state.or_stats[current].edge_and[action_idx] = Some(and_idx);
            path.push(and_idx);

            // Rollout: first estimate for fresh children (§3.3.2).
            for pos in 0..state.and_stats[and_idx].child_or_stats.len() {
                let child_idx = state.and_stats[and_idx].child_or_stats[pos];
                if state.or_stats[child_idx].value.is_infinite() {
                    let child_or = state.stats_to_or[child_idx];
                    let rollout = greedy_rollout(snap, space, pool, action_cache, child_or);
                    results.ensure_capacity(child_or);
                    results.offer(child_or, rollout, pool.quality(rollout));
                    let sz = pool.size(rollout) as f64;
                    state.or_stats[child_idx].initial_value = sz;
                    state.or_stats[child_idx].value = sz;
                }
            }
            break;
        }

        // Fully expanded: score realized actions by UCT (§3.3.4), first max wins.
        let action_idx = select_uct(state, current, config);
        state.or_stats[current].edge_visits[action_idx] += 1;
        let and_idx = state.or_stats[current].edge_and[action_idx].unwrap();
        path.push(and_idx);

        // AND allocation: round-robin (§3.3.5), with its own edge visit.
        let and = &mut state.and_stats[and_idx];
        let pos = (and.round_robin as usize) % and.child_or_stats.len();
        and.round_robin += 1;
        and.child_visits[pos] += 1;
        current = and.child_or_stats[pos];
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
    let total: u32 = stats.edge_visits.iter().sum();
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

/// AND value equation (§3.3): `Q(n) = 1 + Σ_i pair_count_i · Q(child_i)`.
fn recompute_and_value(state: &mut McgsState, and_idx: usize) {
    let and = &state.and_stats[and_idx];
    let mut q = 1.0;
    for (i, &child) in and.child_or_stats.iter().enumerate() {
        q += and.child_counts[i] as f64 * state.or_stats[child].value;
    }
    state.and_stats[and_idx].value = q;
}

/// OR value equation (§2.6, idempotent):
/// `Q(n) = (U(n) + Σ_a N(n,a) · Q(and_a)) / (1 + Σ_a N(n,a))`.
fn recompute_or_value(state: &mut McgsState, or_idx: usize) {
    let stats = &state.or_stats[or_idx];
    if stats.terminal {
        return;
    }
    let mut sum = stats.initial_value;
    let mut total: u32 = 0;
    for (a, edge) in stats.edge_and.iter().enumerate() {
        if let Some(and_idx) = *edge {
            let n = stats.edge_visits[a];
            sum += n as f64 * state.and_stats[and_idx].value;
            total += n;
        }
    }
    state.or_stats[or_idx].value = sum / (1.0 + total as f64);
}

/// Compose the AND node's children's stored best results into a candidate term
/// and offer it to the parent OR node (§3.3: "every update also offers the
/// children's stored best results"). This is the step that propagates
/// improvements up the graph — without it the search can never beat its
/// initial rollout.
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
    let mut children: Vec<(TermId, u32)> = Vec::with_capacity(and.child_or_stats.len());
    for (i, &child_idx) in and.child_or_stats.iter().enumerate() {
        let child_or = state.stats_to_or[child_idx];
        match results.best_term(child_or) {
            Some(t) => children.push((t, and.child_counts[i])),
            // A child without a result cannot be composed (should not happen:
            // expansion seeds every child).
            None => return,
        }
    }
    let op = Cfg::O::from_usize(and.op_raw);
    let candidate = pool.intern_action_result(TermOp::EGraph(op), &children, and.commutative);
    let parent_or = state.stats_to_or[and.parent];
    let _ = snap; // op names/kinds already captured at expansion
    results.offer(parent_or, candidate, pool.quality(candidate));
}

/// Realize one action: allocate the AND statistics struct and all child OR
/// nodes/stats, seeding each child's best-result entry with its generalize seed
/// so a valid result exists from the first instant (§3.1).
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

    // The nth surviving (non-blocked) action, in cached order.
    let action = actions
        .iter()
        .filter(|action| {
            !action
                .pairs
                .iter()
                .any(|p| space.is_cycle_blocked(or_id, p.left, p.right))
        })
        .nth(action_idx)
        .expect("action index within surviving action count");

    let mut child_or_stats: Vec<usize> = Vec::with_capacity(action.pairs.len());
    let mut child_counts: Vec<u32> = Vec::with_capacity(action.pairs.len());

    for pair in &action.pairs {
        let child_ctx_l = space
            .derive_child_context(ctx_l, l, |c| snap.reachability().is_reachable(pair.left, c));
        let child_ctx_r = space.derive_child_context(ctx_r, r, |c| {
            snap.reachability().is_reachable(pair.right, c)
        });

        let l_best = snap.best_size(pair.left);
        let r_best = snap.best_size(pair.right);
        let (child_or, _) = space.get_or_insert_or_node(
            pair.left,
            pair.right,
            child_ctx_l,
            child_ctx_r,
            l_best,
            r_best,
        );

        // Seed the child's best result so composition always has an operand.
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
    });
    and_idx
}

/// Greedy rollout (§A.4): the exact recursion with "minimum over actions"
/// replaced by "first surviving action", so its result is always a valid
/// anti-unifier. Deterministic and cheap.
fn greedy_rollout<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
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

    let ctx_l = *space.or_arena.left_ctx.get(or_id.to_usize());
    let ctx_r = *space.or_arena.right_ctx.get(or_id.to_usize());

    for action in &actions {
        let blocked = action
            .pairs
            .iter()
            .any(|p| space.is_cycle_blocked(or_id, p.left, p.right));
        if blocked {
            continue;
        }

        let mut child_terms: Vec<(TermId, u32)> = Vec::with_capacity(action.pairs.len());
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

            let child_term = greedy_rollout(snap, space, pool, action_cache, child_or);
            child_terms.push((child_term, pair.count));
        }

        let commutative = snap.op_is_commutative(action.op);
        return pool.intern_action_result(TermOp::EGraph(action.op), &child_terms, commutative);
    }

    // No action survived: Variants fallback (§A.4).
    let l_term = build_best_term(snap, pool, l);
    let r_term = build_best_term(snap, pool, r);
    pool.intern(TermOp::Variants, &[l_term, r_term])
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
        let (mcgs_term, mcgs_pool) = run_mcgs(&snap, lc, rc, &config).unwrap();
        assert_eq!(mcgs_pool.size(mcgs_term), exact_size);
    }

    /// The §3.4.4 greedy counterexample: the greedy diagonal costs 10, the
    /// crossed matching costs 9. The initial rollout finds 10; only result
    /// composition through backpropagation can reach 9. This is the regression
    /// gate for "MCGS cannot improve beyond its initial greedy rollout".
    #[test]
    fn mcgs_beats_greedy_rollout() {
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
        let (mcgs_term, mcgs_pool) = run_mcgs(&snap, lc, rc, &config).unwrap();
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
        let (term, pool) = run_mcgs(&snap, ac, ac, &config).unwrap();
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
        let (term, pool) = run_mcgs(&snap, ac, bc, &config).unwrap();
        assert!(pool.size(term) < 100);
    }
}
