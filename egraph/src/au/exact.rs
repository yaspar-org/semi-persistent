// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Memoized exact solver: `eager_with_memo` (§3.2).
//!
//! Dynamic programming over cycle-context states. For non-AC operators: enumerates
//! every surviving action and takes the minimum. For AC/ACI: solves each cell
//! subproblem once, then finds the optimal matching via min-cost transportation.
//! Memoization on states = node sharing: each distinct subproblem is solved once.

use std::collections::HashMap;

use crate::canon::{MSetCanon, VarCanon};
use crate::config::{AuIds, EGraphConfig};
use crate::containers::DenseId;
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;

use super::ac_repr;
use super::actions::{ActionCache, ActionPair, generate_actions};
use super::egraph_api::{AuSnapshot, ClassOf};
use super::estimates::{lb_pair, static_generalize_quality, transport_pair_lb};
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

/// Per-side support of a completed derivation: the left classes and the right
/// classes of every child pair the winning action tree descends through,
/// collected transitively and published sorted and deduplicated.
type Support<C> = (Vec<C>, Vec<C>);

/// One bare-pair memo entry for context subsumption (plan item A6,
/// doc/au-solver-plan.md): the optimal term of a context-clean solve of
/// `(l, r)` plus the support of its winning derivation.
struct CleanEntry<T, C> {
    term: T,
    support: Support<C>,
}

/// Context-subsumption state (`AuConfig::context_subsumption`). A solve of an
/// OR state is context-clean when the entry context removed no candidate
/// that could have mattered: every structural action skipped by cycle
/// blocking had a projection bound strictly above the incumbent size (so it
/// is non-optimal under EVERY context, the A2 argument), no transport cell
/// was skipped by cycle blocking, and every child OR the frame solved was
/// clean itself. By induction over completion order a clean value equals the
/// context-free optimum `V(empty)`: clean children deliver their `V(empty)`,
/// surviving candidates therefore evaluate to their context-free values, and
/// every removed candidate (cycle-blocked above the incumbent, or A2-pruned)
/// has a context-free value strictly above the frame's result.
///
/// Reuse argument, recorded here because both memo maps rely on it. Contexts
/// only remove candidates, so `V` is monotone non-decreasing in the entry
/// context and `V(ctx') >= V(empty)` for every `ctx'`. For the upper bound,
/// the stored derivation re-executes unblocked under `ctx'` whenever its
/// support is disjoint from `ctx'`: every context along the re-execution is
/// the union of a derivation-intrinsic part (path classes filtered by
/// reachability, identical to the clean solve, where every descent of this
/// derivation executed unblocked) and a subset of `ctx'`, and no descent
/// class is in `ctx'` by disjointness. The
/// stored term is then feasible under `ctx'`, so
/// `V(ctx') <= V(empty) <= V(ctx')`: reuse is equality, and the memo entry
/// stays the exact optimum of the reusing state.
struct SubsumptionState<T, C> {
    /// Bare-pair memo: `(l, r)` as raw indices -> the first clean solve's
    /// term and support. First writer wins; every clean solve of the same
    /// pair has the same value (`V(empty)`), so which term is kept only
    /// picks among tied optima, deterministically.
    by_pair: HashMap<(usize, usize), CleanEntry<T, C>>,
    /// Per solved OR id: `Some(support)` iff the solve was context-clean.
    /// Parents read this on tuple-memo hits to propagate cleanliness.
    clean: Vec<Option<Support<C>>>,
}

impl<T, C> SubsumptionState<T, C> {
    fn new() -> Self {
        SubsumptionState {
            by_pair: HashMap::new(),
            clean: Vec::new(),
        }
    }

    fn set_clean<O: DenseId>(&mut self, or_id: O, value: Option<Support<C>>) {
        let idx = or_id.to_usize();
        if idx >= self.clean.len() {
            self.clean.resize_with(idx + 1, || None);
        }
        self.clean[idx] = value;
    }

    fn clean_of<O: DenseId>(&self, or_id: O) -> Option<Support<C>>
    where
        C: Clone,
    {
        self.clean.get(or_id.to_usize()).cloned().flatten()
    }
}

/// Do two ascending-sorted slices share no element? Merge scan; the context
/// interner stores contexts sorted and supports are sorted at publication.
fn sorted_disjoint<C: Ord>(a: &[C], b: &[C]) -> bool {
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].cmp(&b[j]) {
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Equal => return false,
        }
    }
    true
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
    // No deadline, no pruning, no subsumption: this entry point is the
    // reference search the differential fixture pins; `AuConfig`'s
    // `exact_pruning` and `context_subsumption` opt in via `run_exact`.
    let run = run_exact(snap, l_root, r_root, cycle_mode, None, false, false)?;
    Ok((run.term, run.pool))
}

/// Everything one exact solve builds: the optimal term plus the search space,
/// action cache, and best-result table it was derived from. `eager_with_memo`
/// exposes the term and pool; the test-only search-graph dump (`au::dump`)
/// reads the rest, so the extra fields are unused outside `cfg(test)`.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) struct ExactRun<Cfg: EGraphConfig> {
    pub(crate) term: <Cfg::Au as AuIds>::Term,
    pub(crate) pool: TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    pub(crate) space: SearchSpace<Cfg::Au>,
    pub(crate) cache: ActionCache<Cfg::O, Cfg::Au, Cfg::M>,
    pub(crate) results: BestResults<Cfg::Au>,
    pub(crate) root_or: <Cfg::Au as AuIds>::Or,
    /// True when the solve ran to completion (the term is the proven
    /// optimum); false when a deadline expired and `term` is the root
    /// frame's incumbent — feasible by construction, optimal only if the
    /// completed actions happened to include the optimum.
    pub(crate) complete: bool,
}

/// [`eager_with_memo`] with the full solver state returned instead of dropped.
///
/// `deadline`: `None` runs to completion (today's behavior). `Some(d)` makes
/// the solve anytime: on expiry the loop unwinds and returns the root frame's
/// incumbent — at minimum the generalize seed, better if completed actions
/// improved it — with `complete: false`. Expiry is polled every
/// [`DEADLINE_CHECK_INTERVAL`] node entries.
///
/// `pruning`: branch-and-bound on the projection lower bound (plan item A2);
/// see [`solve_iterative`]. `false` is the reference search.
///
/// `subsumption`: bare-pair reuse of context-clean results (plan item A6);
/// see [`SubsumptionState`] and [`solve_iterative`]. `false` is the
/// reference search.
pub(crate) fn run_exact<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l_root: ClassOf<Cfg>,
    r_root: ClassOf<Cfg>,
    cycle_mode: CycleMode,
    deadline: Option<std::time::Duration>,
    pruning: bool,
    subsumption: bool,
) -> Result<ExactRun<Cfg>, super::AuError>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    snap.validate_finite_from(l_root)?;
    snap.validate_finite_from(r_root)?;

    let mut space: SearchSpace<Cfg::Au> = SearchSpace::new(cycle_mode);
    let mut pool = TermPool::new();
    // AC/ACI pairs are solved by min-cost transport (zero matrix enumeration);
    // the cache materializes only the non-AC action kinds.
    let mut cache: ActionCache<Cfg::O, Cfg::Au, Cfg::M> =
        ActionCache::without_ac_actions(usize::MAX);
    let mut results: BestResults<Cfg::Au> = BestResults::new();

    let empty_ctx = space.contexts.empty();
    let l_best = snap.best_size(l_root);
    let r_best = snap.best_size(r_root);
    let (root_or, _) =
        space.get_or_insert_or_node(l_root, r_root, empty_ctx, empty_ctx, l_best, r_best);

    let mut memo: Vec<MemoState<<Cfg::Au as AuIds>::Term>> = Vec::new();

    let (term, complete) = solve_iterative(
        snap,
        &mut space,
        &mut pool,
        &mut cache,
        &mut results,
        &mut memo,
        root_or,
        deadline.map(|d| std::time::Instant::now() + d),
        pruning,
        subsumption,
    );

    Ok(ExactRun {
        term,
        pool,
        space,
        cache,
        results,
        root_or,
        complete,
    })
}

/// How many OR-node entries pass between two `Instant::now()` deadline polls.
/// 1024 keeps the poll off the per-node hot path (one syscall-free clock read
/// per ~1024 entries, negligible against per-entry solver work) while an
/// expired deadline is still noticed within milliseconds even in debug
/// builds, where 1024 entries are well under a millisecond of work.
const DEADLINE_CHECK_INTERVAL: u32 = 1024;

fn ensure_memo<T: Copy, O: DenseId>(memo: &mut Vec<MemoState<T>>, or_id: O) {
    let idx = or_id.to_usize();
    if idx >= memo.len() {
        memo.resize(idx + 1, MemoState::Empty);
    }
}

/// Lower bound on the size of one structural action's completion: 1 for the
/// operator, each solved child at its true size, each unsolved pair (from
/// `next_pair` on) at its projection bound (`lb_pair`). A solved child's true
/// size dominates its bound, so substituting it only raises the total: the
/// partial-sum re-check is at least as tight as the initial one.
///
/// `u64` saturating accumulation. Saturating keeps the total a lower bound
/// (`saturating_add <=` the exact sum), and a saturated `u64::MAX` still
/// strictly exceeds every `u32` incumbent, so the caller's `bound > incumbent`
/// comparison then discards the action — sound, because the true value is at
/// least the exact sum, which reached `u64::MAX`.
fn action_size_bound<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    pairs: &[ActionPair<Cfg::Au, Cfg::M>],
    solved: &[(<Cfg::Au as AuIds>::Term, u64)],
    next_pair: usize,
) -> u64
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut bound: u64 = 1;
    for &(term, count) in solved {
        bound = bound.saturating_add(u64::from(pool.size(term)).saturating_mul(count));
    }
    for pair in &pairs[next_pair..] {
        bound = bound.saturating_add(
            u64::from(lb_pair(snap, pair.left, pair.right).0).saturating_mul(pair.count.to_u64()),
        );
    }
    bound
}

/// Stage of one in-progress OR-node solve (one frame of the explicit stack).
enum Stage<Cfg: EGraphConfig> {
    /// Iterating the cached non-AC actions: `action_idx` is the current
    /// action, `pair_idx` the next child pair to solve, `child_terms` the
    /// terms solved so far for the current action.
    Actions {
        action_idx: usize,
        pair_idx: usize,
        child_terms: Vec<(<Cfg::Au as AuIds>::Term, u64)>,
    },
    /// Iterating AC/ACI operators, their representation pairs, and each
    /// pair's cell subproblems (§3.4.4). `pairs` holds the current operator's
    /// representation pairs; `cells` the active pair's cell iteration.
    Transport {
        ops: Vec<Cfg::O>,
        op_idx: usize,
        pairs: Vec<ac_repr::PaddedPair<ClassOf<Cfg>>>,
        pair_idx: usize,
        cells: Option<CellState<Cfg>>,
    },
}

/// Cell iteration state for one AC/ACI representation pair: row-major cursor
/// `(i, j)` over the cost matrix, solving each legal cell subproblem once.
struct CellState<Cfg: EGraphConfig> {
    lm: ac_repr::Monomial<ClassOf<Cfg>>,
    rm: ac_repr::Monomial<ClassOf<Cfg>>,
    /// The identity class when padding injected it into this pair (§3.4.4).
    /// Every cell of a padded pair carries child contexts extended with this
    /// class: the injection is not structural, so reachability-based
    /// derivation alone would let a cell repeat its ancestor's OR key and
    /// break the rank invariant the `Visiting` re-entry check enforces.
    pad_identity: Option<ClassOf<Cfg>>,
    i: usize,
    j: usize,
    cost: Vec<Vec<Cell>>,
    cell_term: Vec<Vec<Option<<Cfg::Au as AuIds>::Term>>>,
    /// Per-cell child support, recorded at delivery (context subsumption
    /// only; empty otherwise). `None` in a delivered cell means the child
    /// was not context-clean, which already tainted the frame.
    cell_support: Vec<Vec<Option<Support<ClassOf<Cfg>>>>>,
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
    actions: Vec<super::actions::Action<Cfg::O, Cfg::Au, Cfg::M>>,
    best: <Cfg::Au as AuIds>::Term,
    best_quality: (u32, u32),
    stage: Stage<Cfg>,
    /// Context subsumption only (untouched otherwise). `clean` starts true
    /// and is cleared when cycle blocking removes a candidate that is not
    /// provably non-optimal under every context, or a delivered child was
    /// not clean itself; `cur_support` accumulates the
    /// support of the action currently being evaluated; `best_support` holds
    /// the winning candidate's support, published on clean completion.
    clean: bool,
    cur_support: Support<ClassOf<Cfg>>,
    best_support: Support<ClassOf<Cfg>>,
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
///
/// `deadline` makes the solve anytime: expiry is polled with `Instant::now()`
/// once every [`DEADLINE_CHECK_INTERVAL`] node entries (the outer loop, one
/// iteration per OR-node entry — the natural unit of solver progress, and
/// each entry does bounded work before the next). On expiry the whole stack
/// is abandoned and the ROOT frame's incumbent is returned with `false`:
/// feasible by construction (the generalize seed is valid, and every
/// improvement came from a fully completed action), uncertified. No
/// `Visiting` memo entry is published and no `mark_exact` is issued for
/// abandoned frames, so nothing claims optimality it does not have.
///
/// `pruning` enables branch-and-bound on the projection lower bound
/// (`estimates::lb_pair`, plan item A2 and its soundness argument in
/// doc/au-solver-plan.md): a structural action is skipped when
/// `1 + sum count * lb_pair(pair)` strictly exceeds the frame's incumbent
/// size, re-checked with each solved child's true size substituted for its
/// bound (`action_size_bound`); an AC representation pair is skipped when the
/// min-cost flow over `lb_pair` cell costs plus 1 strictly exceeds it. Both
/// comparisons are size-only (an equal size can still win on variant mass)
/// and always against the frame's OWN incumbent, never an inherited ancestor
/// bound: pruned candidates are provably non-optimal at this node, so the min
/// over the survivors — and therefore every memo entry — is still the exact
/// optimum of its state, and memo reuse stays valid. The generalize incumbent
/// is evaluated before any action, so a bound to compare against always
/// exists. Children solved before an abandoned action stay in the memo:
/// their entries are exact optima of their own states regardless of why the
/// parent stopped.
///
/// `subsumption` enables context-subsumption reuse (plan item A6 and its
/// soundness argument in doc/au-solver-plan.md; the reuse argument and the
/// cleanliness definition are on [`SubsumptionState`]). Each frame tracks
/// whether its evaluation was context-clean: every cycle-blocked structural
/// action was provably non-optimal under every context (projection bound
/// strictly above the incumbent), no transport cell was blocked, and every
/// child OR it solved was clean itself. A clean completion publishes its term and the
/// winning derivation's support in a bare `(l, r)` map; a later OR entry on
/// the same pair reuses the stored term without expanding, provided the
/// stored support is disjoint from both of its entry contexts. The reused
/// term is offered and marked exact for the new OR id, so the results table
/// serves downstream consumers exactly as if the node had been solved.
/// A2-pruned candidates do NOT taint cleanliness: their bounds are built
/// from `lb_pair`, which is context-independent, and (when the frame is
/// still clean) from solved child values that equal their `V(empty)`, so a
/// pruned candidate is provably non-optimal under EVERY entry context, per
/// the A2 argument. The one exception is a pruned AC representation pair
/// whose lower-bound flow problem forbade a cycle-blocked cell: that prune
/// decision is context-dependent, so it taints.
///
/// Returns `(term, complete)`; `complete` is false only on deadline expiry.
#[allow(clippy::too_many_arguments)]
fn solve_iterative<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    cache: &mut ActionCache<Cfg::O, Cfg::Au, Cfg::M>,
    results: &mut BestResults<Cfg::Au>,
    memo: &mut Vec<MemoState<<Cfg::Au as AuIds>::Term>>,
    root_or: <Cfg::Au as AuIds>::Or,
    deadline: Option<std::time::Instant>,
    pruning: bool,
    subsumption: bool,
) -> (<Cfg::Au as AuIds>::Term, bool)
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut stack: Vec<SolveFrame<Cfg>> = Vec::new();
    let mut sub: SubsumptionState<<Cfg::Au as AuIds>::Term, ClassOf<Cfg>> = SubsumptionState::new();
    let mut pending = root_or;
    let mut entries: u32 = 0;
    loop {
        // ── Deadline poll: every DEADLINE_CHECK_INTERVAL node entries ──
        if let Some(expiry) = deadline {
            entries = entries.wrapping_add(1);
            if entries.is_multiple_of(DEADLINE_CHECK_INTERVAL)
                && std::time::Instant::now() >= expiry
                && !stack.is_empty()
            {
                // Unwind: abandon all in-progress frames and surface the
                // root frame's incumbent, uncertified.
                return (stack[0].best, false);
            }
        }

        // ── Enter `pending`: memo check, terminal case, or a new frame ──
        let or_id = pending;
        ensure_memo(memo, or_id);
        let mut done: Option<<Cfg::Au as AuIds>::Term> = None;
        // `Some(support)` iff the delivered child solved context-clean;
        // set and taken in lockstep with `done`. Always `None` with the
        // subsumption flag off (never read then).
        let mut done_support: Option<Support<ClassOf<Cfg>>> = None;
        match memo[or_id.to_usize()] {
            MemoState::Solved(term) => {
                done = Some(term);
                if subsumption {
                    done_support = sub.clean_of(or_id);
                }
            }
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

                let l = *space.or_arena.left.get(or_id.to_index());
                let r = *space.or_arena.right.get(or_id.to_index());

                if l == r {
                    // Terminal case: l == r. Trivially context-clean with an
                    // empty support: the evaluation consults no context.
                    let term = build_best_term(snap, pool, l);
                    memo[or_id.to_usize()] = MemoState::Solved(term);
                    results.ensure_capacity(or_id);
                    results.offer(or_id, term, pool.quality(term));
                    results.mark_exact(or_id);
                    done = Some(term);
                    if subsumption {
                        sub.set_clean(or_id, Some((Vec::new(), Vec::new())));
                        done_support = Some((Vec::new(), Vec::new()));
                    }
                } else if subsumption
                    && let Some(entry) = sub.by_pair.get(&(l.to_usize(), r.to_usize()))
                    && sorted_disjoint(
                        &entry.support.0,
                        space
                            .contexts
                            .get(*space.or_arena.left_ctx.get(or_id.to_index())),
                    )
                    && sorted_disjoint(
                        &entry.support.1,
                        space
                            .contexts
                            .get(*space.or_arena.right_ctx.get(or_id.to_index())),
                    )
                {
                    // Bare-pair reuse: a clean solve of (l, r) exists and its
                    // support is disjoint from both entry contexts, so its
                    // term is this state's exact optimum too (argument on
                    // `SubsumptionState`). Offer + mark_exact under the new
                    // OR id so the results table serves it downstream.
                    let term = entry.term;
                    let support = entry.support.clone();
                    memo[or_id.to_usize()] = MemoState::Solved(term);
                    results.ensure_capacity(or_id);
                    results.offer(or_id, term, pool.quality(term));
                    results.mark_exact(or_id);
                    sub.set_clean(or_id, Some(support.clone()));
                    done = Some(term);
                    done_support = Some(support);
                } else {
                    // The terminal generalize action is part of the shared action
                    // space. Eagerly evaluate it as a valid incumbent before
                    // considering structural actions.
                    let generalize = evaluate_generalize_action(snap, pool, l, r);
                    let best_quality = pool.quality(generalize);

                    // Generate actions for this class pair, then order the
                    // frame's copy best-first by the lazy-completion estimate
                    // the MCGS initial rollout ranks with:
                    // `(1 + sum count * generalize_size(pair), sum count *
                    // generalize_vmass(pair))`, ascending. Reordering permutes
                    // the operands of a min, so the optimal quality is
                    // unchanged; because the incumbent comparison below is
                    // strict `<`, the FIRST candidate evaluated wins exact
                    // quality ties, so ordering may change which term
                    // represents a tied optimum, never its quality. The sort
                    // is on the frame's local copy; the shared cache keeps
                    // generation order.
                    generate_actions(snap, cache, l, r);
                    let mut actions = cache.get(l, r).unwrap().to_vec();
                    actions.sort_by_cached_key(|action| {
                        let mut size = 1u128;
                        let mut vmass = 0u128;
                        for pair in &action.pairs {
                            let (s, v) = static_generalize_quality(snap, pair.left, pair.right);
                            size += u128::from(s) * u128::from(pair.count.to_u64());
                            vmass += u128::from(v) * u128::from(pair.count.to_u64());
                        }
                        (size, vmass)
                    });

                    let ctx_l = *space.or_arena.left_ctx.get(or_id.to_index());
                    let ctx_r = *space.or_arena.right_ctx.get(or_id.to_index());

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
                        clean: true,
                        cur_support: (Vec::new(), Vec::new()),
                        best_support: (Vec::new(), Vec::new()),
                    });
                }
            }
        }

        // ── Advance the top frame until it descends or completes ──
        'advance: loop {
            let Some(frame) = stack.last_mut() else {
                return (
                    done.expect("exact solve must produce a term for the root"),
                    true,
                );
            };

            // Deliver a completed child term to the frame's current stage.
            if let Some(term) = done.take() {
                match &mut frame.stage {
                    Stage::Actions {
                        action_idx,
                        pair_idx,
                        child_terms,
                    } => {
                        // Widening to the surface width, which `intern_action_result`
                        // takes so the structural and transport paths can share it.
                        let pair = frame.actions[*action_idx].pairs[*pair_idx];
                        if subsumption {
                            match done_support.take() {
                                Some((sl, sr)) => {
                                    if frame.clean {
                                        frame.cur_support.0.push(pair.left);
                                        frame.cur_support.0.extend(sl);
                                        frame.cur_support.1.push(pair.right);
                                        frame.cur_support.1.extend(sr);
                                    }
                                }
                                None => frame.clean = false,
                            }
                        }
                        child_terms.push((term, pair.count.to_u64()));
                        *pair_idx += 1;
                    }
                    Stage::Transport { cells, .. } => {
                        let cell = cells
                            .as_mut()
                            .expect("transport child delivered without an active cell");
                        let (s, v) = pool.quality(term);
                        cell.cost[cell.i][cell.j] = Cell::Cost(s, v);
                        cell.cell_term[cell.i][cell.j] = Some(term);
                        if subsumption {
                            let support = done_support.take();
                            if support.is_none() {
                                frame.clean = false;
                            }
                            cell.cell_support[cell.i][cell.j] = support;
                        }
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
                            if subsumption {
                                frame.cur_support.0.clear();
                                frame.cur_support.1.clear();
                            }
                            let blocked = action
                                .pairs
                                .iter()
                                .any(|p| space.is_cycle_blocked(frame.or_id, p.left, p.right));
                            if blocked {
                                // The entry context removed a candidate.
                                // That taints cleanliness UNLESS the
                                // candidate is provably non-optimal under
                                // every entry context anyway: its projection
                                // bound (`action_size_bound`, valid under
                                // every context per the A2 argument)
                                // strictly exceeds the incumbent size, which
                                // is at least the frame's final value. Such
                                // a candidate cannot lower the context-free
                                // optimum, so skipping it keeps the value
                                // context-free. Strict comparison only: at
                                // equal size the candidate could still win
                                // on variant mass (the A2 guardrail).
                                // Without this test every cyclic class pair
                                // taints its whole subtree through its
                                // self-re-entry action and no bare-pair
                                // entry is ever published.
                                if subsumption
                                    && action_size_bound(snap, pool, &action.pairs, &[], 0)
                                        <= u64::from(frame.best_quality.0)
                                {
                                    frame.clean = false;
                                }
                                *action_idx += 1;
                                continue;
                            }
                            // Branch-and-bound (A2): skip the action before any
                            // descent when its projection bound already strictly
                            // exceeds this frame's incumbent size. Does not
                            // taint cleanliness: the bound is `lb_pair` only,
                            // which is context-independent, so the skipped
                            // candidate is non-optimal under EVERY entry
                            // context (A2 argument).
                            if pruning
                                && action_size_bound(snap, pool, &action.pairs, &[], 0)
                                    > u64::from(frame.best_quality.0)
                            {
                                *action_idx += 1;
                                continue;
                            }
                        } else if pruning
                            && *pair_idx < action.pairs.len()
                            && action_size_bound(snap, pool, &action.pairs, child_terms, *pair_idx)
                                > u64::from(frame.best_quality.0)
                        {
                            // Partial-sum tightening (A2): solved children at
                            // their true sizes, the rest at their bounds. The
                            // children already solved stay in the memo — each is
                            // the exact optimum of its own state. No cleanliness
                            // taint: while the frame is clean, every solved
                            // child's value equals its context-free optimum, so
                            // the tightened bound is context-independent too;
                            // an unclean child already tainted at delivery.
                            *action_idx += 1;
                            *pair_idx = 0;
                            child_terms.clear();
                            continue;
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
                            if subsumption {
                                frame.best_support = std::mem::take(&mut frame.cur_support);
                            }
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
                                    // A transport edge removed by the entry
                                    // context: same taint as a blocked
                                    // structural action.
                                    if subsumption {
                                        frame.clean = false;
                                    }
                                    cell.j += 1;
                                    continue;
                                }
                                let (l, r, ctx_l, ctx_r) =
                                    (frame.l, frame.r, frame.ctx_l, frame.ctx_r);
                                let mut child_ctx_l = space.derive_child_context(ctx_l, l, |c| {
                                    snap.reachability().is_reachable(lc, c)
                                });
                                let mut child_ctx_r = space.derive_child_context(ctx_r, r, |c| {
                                    snap.reachability().is_reachable(rc, c)
                                });
                                // Padded pair: extend both child contexts with
                                // the injected identity class (see CellState).
                                if let Some(id_class) = cell.pad_identity {
                                    child_ctx_l = space.extend_context(child_ctx_l, id_class);
                                    child_ctx_r = space.extend_context(child_ctx_r, id_class);
                                }
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
                            let mut cell = cells.take().expect("cell state present");
                            // Monomials carry surface-width multiplicities; the
                            // solver's supply vectors are narrower. A pair it
                            // cannot represent contributes no candidate, exactly
                            // as an infeasible pair does — never a truncated one.
                            let problem = TransportProblem::narrowed(
                                &cell.lm.iter().map(|(_, k)| *k).collect::<Vec<_>>(),
                                &cell.rm.iter().map(|(_, k)| *k).collect::<Vec<_>>(),
                                cell.cost,
                            );
                            if let Some(solution) = problem.as_ref().and_then(solve_transport) {
                                // Compose the winning matrix into a term. AC/ACI
                                // kinds are commutative: canonical child order.
                                let mut child_terms: Vec<(<Cfg::Au as AuIds>::Term, u64)> =
                                    Vec::new();
                                let mut support: Support<ClassOf<Cfg>> = (Vec::new(), Vec::new());
                                for (i, row) in solution.flow.iter().enumerate() {
                                    for (j, &x) in row.iter().enumerate() {
                                        if x > 0 {
                                            child_terms.push((
                                                cell.cell_term[i][j].unwrap(),
                                                u64::from(x),
                                            ));
                                            if subsumption && frame.clean {
                                                let (csl, csr) =
                                                    cell.cell_support[i][j].take().expect(
                                                        "clean frame composed a transport cell \
                                                         without a recorded support",
                                                    );
                                                support.0.push(cell.lm[i].0);
                                                support.0.extend(csl);
                                                support.1.push(cell.rm[j].0);
                                                support.1.extend(csr);
                                            }
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
                                    if subsumption {
                                        frame.best_support = support;
                                    }
                                }
                            }
                            *pair_idx += 1;
                            continue;
                        }
                        if *pair_idx < pairs.len() {
                            // Begin the next representation pair: fresh cost and
                            // term matrices, all cells Forbidden until solved.
                            let (lm, rm, pad_identity) = pairs[*pair_idx].clone();
                            let rows = lm.len();
                            let cols = rm.len();
                            // Branch-and-bound (A2) on the whole representation
                            // pair: `transport_pair_lb` (shared with MCGS
                            // dominance pruning, A5) is a lower bound on the
                            // pair's achievable size, with the same Forbidden
                            // pattern and supplies as the real solve below, so
                            // an infeasible bound problem (`None`) means the
                            // real pair contributes no candidate either.
                            // Strict size-only comparison against this frame's
                            // own incumbent, as for structural actions.
                            if pruning {
                                let or_id = frame.or_id;
                                let bound = transport_pair_lb(snap, &lm, &rm, |i, j| {
                                    !space.is_cycle_blocked(or_id, lm[i].0, rm[j].0)
                                });
                                let prune = match bound {
                                    None => true,
                                    Some(b) => b > u128::from(frame.best_quality.0),
                                };
                                if prune {
                                    // Unlike the structural A2 prunes, this
                                    // bound's Forbidden pattern comes from
                                    // cycle blocking: if any cell of the pair
                                    // is blocked, the prune decision is
                                    // context-dependent and taints. With no
                                    // blocked cell the bound is `lb_pair`
                                    // flow only, context-independent.
                                    if subsumption
                                        && lm.iter().any(|&(lc, _)| {
                                            rm.iter().any(|&(rc, _)| {
                                                space.is_cycle_blocked(or_id, lc, rc)
                                            })
                                        })
                                    {
                                        frame.clean = false;
                                    }
                                    *pair_idx += 1;
                                    continue;
                                }
                            }
                            *cells = Some(CellState {
                                lm,
                                rm,
                                pad_identity,
                                i: 0,
                                j: 0,
                                cost: vec![vec![Cell::Forbidden; cols]; rows],
                                cell_term: vec![vec![None; cols]; rows],
                                cell_support: if subsumption {
                                    vec![vec![None; cols]; rows]
                                } else {
                                    Vec::new()
                                },
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
                        if subsumption && frame.clean {
                            // Clean completion: publish the winning
                            // derivation's support per side, sorted for the
                            // disjointness scan, and memoize the bare pair.
                            let (mut sl, mut sr) = frame.best_support;
                            sl.sort_unstable();
                            sl.dedup();
                            sr.sort_unstable();
                            sr.dedup();
                            sub.set_clean(frame.or_id, Some((sl.clone(), sr.clone())));
                            sub.by_pair
                                .entry((frame.l.to_usize(), frame.r.to_usize()))
                                .or_insert(CleanEntry {
                                    term: frame.best,
                                    support: (sl.clone(), sr.clone()),
                                });
                            done_support = Some((sl, sr));
                        }
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

    /// D2 regression: an identity class that itself contains an AC member
    /// (merge(e, plus{a,b}), so the theory reads a + b = 0). Padding injects
    /// the identity CLASS as a transport-cell child; without the padded-cell
    /// context extension the OR key repeats beneath itself while Visiting and
    /// the solver panics with "cycle-mode rank invariant violated".
    #[test]
    fn exact_identity_class_with_ac_member_terminates() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let e_op = eg.register_op0("e", int);
        let plus_op = eg.register_mset("plus", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let e = eg.add(e_op, &[]);
        eg.set_unit_node(plus_op, e);
        let plus_ab = eg.add(plus_op, &[a, b]);
        eg.merge(e, plus_ab);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let cc = snap.class_of(c).unwrap();
        let ec = snap.class_of(e).unwrap();

        let (term, pool) = eager_with_memo(&snap, cc, ec, CycleMode::AncestorOnly).unwrap();
        assert!(pool.size(term) >= 1);
    }

    /// D2 variant: the left class is a member child of the degenerate
    /// identity class (AU(a, e) also triggered the panic).
    #[test]
    fn exact_identity_class_with_ac_member_terminates_on_member_child() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let e_op = eg.register_op0("e", int);
        let plus_op = eg.register_mset("plus", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let e = eg.add(e_op, &[]);
        eg.set_unit_node(plus_op, e);
        let plus_ab = eg.add(plus_op, &[a, b]);
        eg.merge(e, plus_ab);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let ac = snap.class_of(a).unwrap();
        let ec = snap.class_of(e).unwrap();

        let (term, pool) = eager_with_memo(&snap, ac, ec, CycleMode::AncestorOnly).unwrap();
        assert!(pool.size(term) >= 1);
    }

    /// D2 skeleton: three-child merge (merge(e, plus{a,b,c})) and both query
    /// orientations.
    #[test]
    fn exact_identity_class_with_wider_ac_member_terminates() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let e_op = eg.register_op0("e", int);
        let plus_op = eg.register_mset("plus", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let e = eg.add(e_op, &[]);
        eg.set_unit_node(plus_op, e);
        let plus_abc = eg.add(plus_op, &[a, b, c]);
        eg.merge(e, plus_abc);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let dc = snap.class_of(d).unwrap();
        let ec = snap.class_of(e).unwrap();

        let (t1, p1) = eager_with_memo(&snap, dc, ec, CycleMode::AncestorOnly).unwrap();
        assert!(p1.size(t1) >= 1);
        let (t2, p2) = eager_with_memo(&snap, ec, dc, CycleMode::AncestorOnly).unwrap();
        assert!(p2.size(t2) >= 1);
    }

    /// D2 skeleton: set operator with its own unit (merge(t, and{a,b})).
    #[test]
    fn exact_identity_class_with_set_member_terminates() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let t_op = eg.register_op0("t", int);
        let and_op = eg.register_set("and", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let t = eg.add(t_op, &[]);
        eg.set_unit_node(and_op, t);
        let and_ab = eg.add(and_op, &[a, b]);
        eg.merge(t, and_ab);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let cc = snap.class_of(c).unwrap();
        let tc = snap.class_of(t).unwrap();

        let (term, pool) = eager_with_memo(&snap, cc, tc, CycleMode::AncestorOnly).unwrap();
        assert!(pool.size(term) >= 1);
    }
}
