// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Monte-Carlo Graph Search for anti-unification (§3.3).
//!
//! Playout = selection (UCT at OR nodes, a configurable effort selector at
//! AND nodes), expansion, initial rollout (§A.4) for first estimates, then
//! path-only backpropagation: every AND node on the traversed path recomputes
//! its value idempotently from its children (§2.6), composes its children's
//! stored best results into a candidate term, and offers it to its parent's
//! best-result entry (§3.3). That composition step is what lets the search
//! improve past the initial rollout and converge to the configured
//! cycle-filtered optimum on exhausted graphs.
//!
//! Implemented policies: UCT selection at OR nodes and three AND-node effort
//! selectors (`lct_and` default, `uct_and`, `round_robin`; §3.3.5). PUCT and
//! priors are future work; see doc/future/au-associative-operators.md.
//!
//! # The closed bit
//!
//! Under `McgsConfig::closed_bit` every OR node carries a bit that is set once
//! its subgraph is fully resolved — terminal, or every action slot realized
//! and every child of every realized AND closed — and every AND node carries
//! the count of its children that are still open. The bits are maintained
//! incrementally: an AND closes when its last open child closes, an OR closes
//! when its last open AND closes, and closure walks upward through reverse
//! edges (each OR node keeps the list of AND nodes holding it as a child), so
//! a node's bit is set the moment its subgraph resolves, through every parent
//! of a shared node rather than only along the playout's path.
//!
//! Selection then skips closed subtrees: `select_uct` never descends into an
//! action whose AND is closed (its value still enters `recompute_or_value`),
//! and the AND-node selectors skip closed children, the same gate the terminal
//! skip applies. Certification reads the root bit instead of walking the graph.
//!
//! Implementation argument. A closed subtree's value and stored result are
//! treated as contextually exact and final:
//! every action below it is realized, every descendant is closed, and the
//! closure walk recomputes each AND's value and offers its composition to its
//! parent *before* that parent can close, so an OR node's incumbent already
//! includes every action's final composition when its bit is set. Skipping
//! such a subtree therefore removes only visits that could not change any
//! value, any stored result, or the certificate; the playouts freed are spent
//! on unrealized actions instead. Answer quality at a given budget can only
//! improve or stay, and `Completion::Exact` still means what it meant: every
//! reachable action was realized (or proven non-optimal, under
//! `dominance_pruning`).
//!
//! The statistics arenas hold the propagation bookkeeping (the bits, the open
//! counters, the reverse edges), but the durable record of a closure is in
//! `BestResults`: a node that closes is marked contextually exact there, the
//! same scope delegated Exact sets, because closure asserts the same fact: the
//! stored result is no worse than every result in that node's action space
//! under the same cycle mode. Pair-mode root Exact has a separate stronger
//! global bit.
//! `ensure_or_stats` makes a node with a contextual certificate terminal at
//! creation, so that proof carries into later UCT runs on the same session
//! layers and rolls back with the results table's token. It deliberately
//! ignores the global bit because its witness may use actions filtered out of
//! this contextual graph.
//!
//! # Hybrid exact subproblems
//!
//! Under `McgsConfig::hybrid_exact` every OR node is measured once, when its
//! statistics are created, by `estimates::reachable_pairs`: the size of the
//! class-pair rectangle its subgraph lives in, two array reads off the
//! snapshot's precomputed reachability popcounts. A node at or below
//! `McgsConfig::hybrid_threshold` is handed to the exact solver instead of
//! being enumerated by playouts: `exact::run_exact_at` on that node's own class
//! pair and side-or-pair context under the run's cycle mode, with projection
//! pruning on and side-context subsumption when supported. The
//! result is offered and marked exact, which makes the node terminal through
//! the condition that was already there, and terminal nodes are born closed,
//! so under `closed_bit` the proof propagates upward as a closure with no
//! extra machinery.
//!
//! Soundness. An exact run entered at the same class pair, context, and cycle
//! mode solves the identical subproblem the MCGS node stands for: the OR key
//! records that full policy state, cycle blocking reads nothing else, and both solvers
//! generate actions from the same `generate_actions`/`transport_actions`. So
//! a completed call makes the same contextual exactness assertion that
//! `mark_exact` records, namely no worse result in this node's action space
//! under the same cycle mode. This is an implementation argument with finite
//! differential evidence, not a machine-checked solver theorem. The term is
//! safe to offer regardless: term validity
//! is context-independent (contexts exist to terminate the search, not to
//! restrict which terms are valid), so an exact-solved term projects into the
//! two classes like any other. Afterwards the write-once exact flag,
//! `offer`'s strict-improvement rule, and its finality assertion are what
//! prevent degradation.
//!
//! Admission. The reachable-pair and entry-action thresholds are O(1) and
//! local-workload estimates, respectively. They do not bound descendant
//! contextual states or fan-out. Only `hybrid_node_budget` is a deterministic
//! hard bound on one call. A call that exhausts that budget has its feasible
//! incumbent offered but is not marked exact.
//!
//! Layer separation. The exact run creates its own search space, action cache,
//! and result table, so it cannot read or write the MCGS overlay; the single
//! shared layer is the term pool, and sharing it is what makes the returned
//! term id meaningful to MCGS. That sharing is safe by construction: the pool
//! is append-only and hash-consed, so interning appends and never invalidates
//! an id MCGS already holds, and a session `restore` truncates those
//! additions with the same token bundle that rolls back the results pointing
//! at them.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::{
    AppendOnlyVec, DenseId, IndexLike, MapToken, ShrinkPolicy, SpMap, VecP, VecToken,
};
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;

use super::AuIds31;
use super::ac_repr;
use super::actions::{Action, ActionCache, generate_actions};
use super::egraph_api::{AuSnapshot, ClassOf};
use super::estimates::{lb_pair, reachable_pairs, static_generalize_quality, transport_pair_lb};
use super::results::BestResults;
use super::space::{CycleMode, SearchSpace};
use super::terms::{TermOp, TermPool, build_best_term, evaluate_generalize_action};
use super::transport::{Cell, TransportProblem, solve_transport, solve_transport_quantized};
use crate::config::AuIds;

/// Effort-allocation selector at AND nodes (§3.3.5). An AND node does not
/// choose an outcome — all children must be solved — so its selector decides
/// where the next unit of refinement effort goes.
///
/// Fairness (§2.5.1 F): `RoundRobin` gives every child equal visits by
/// rotation. `UctAnd`/`LctAnd` are fair through their exploration term,
/// `C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))`, which diverges for any neglected
/// child, so every child is still refined infinitely often.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AndSelector {
    /// `i = counter mod arity; counter += 1` — equal effort by rotation.
    /// Halves playout flux at every 2-child AND level, so certifying a
    /// depth-d branching spine needs ~2^d playouts.
    RoundRobin,
    /// `argmax_i (1 − normalize(Q(child_i))) + C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))`
    /// — refines the most promising (best-normalized-value) child first.
    UctAnd,
    /// `argmin_i (1 − normalize(Q(child_i))) − C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))`
    /// — selects by lower confidence bound, deliberately visiting the weakest
    /// child (an AND result's size is a sum, so its quality is limited by its
    /// worst child). Default: it routes effort to the least-certain child, so
    /// unexpanded/incomplete subtrees receive nearly all flux until they
    /// close, making certification cost proportional to graph size instead of
    /// exponential in depth.
    #[default]
    LctAnd,
}

/// MCGS configuration.
#[derive(Debug, Clone)]
pub struct McgsConfig {
    pub playouts: u64,
    pub cycle_mode: CycleMode,
    /// UCT exploration constant C (§3.3.4). Default √2.
    pub exploration_constant: f64,
    /// Normalization target (§2.5). Default 0.8.
    pub x_target: f64,
    /// Effort allocation at AND nodes (§3.3.5). Default `LctAnd`.
    pub and_selector: AndSelector,
    /// Dominance pruning against the generalize value: at OR-stats creation,
    /// drop every action whose
    /// projection lower bound (`estimates::lb_pair`; for transport actions
    /// the min-cost flow of `estimates::transport_pair_lb`) strictly exceeds
    /// the node's generalize value. The generalize value is the exact value
    /// of an always-available alternative, so a dropped action can never be
    /// optimal at that node; the certificate's claim becomes "every action
    /// was realized or proven non-optimal", the same claim exact-side
    /// pruning makes. A node whose every action is dropped closes
    /// (`terminal`) at its stored best result, seeded with the generalize
    /// term at node creation. Default `false`: the unpruned search is the
    /// reference the differential fixture was captured against;
    /// `au_differential.rs::dominant_pruned_mcgs_is_sound` gates the flag-on
    /// behavior.
    pub dominance_pruning: bool,
    /// The MCTS-solver closed bit: keep
    /// a per-OR-node "subgraph fully resolved" bit, maintain it incrementally
    /// through reverse edges, exclude closed subtrees from selection, and read
    /// the certificate off the root's bit instead of walking the graph. See
    /// the module doc for the rule and its soundness argument. Default
    /// `false`: the unrestricted search is the reference the differential
    /// fixture was captured against;
    /// `au_differential.rs::closed_bit_mcgs_is_sound` gates the flag-on
    /// behavior.
    pub closed_bit: bool,
    /// Hybrid exact solving on shallow subproblems: at OR-stats creation, when the node's
    /// reachable-pair estimate is at or below [`Self::hybrid_threshold`], run
    /// the exact solver on that node's own state and mark its result exact.
    /// See the module doc for the trigger and its soundness argument. Default
    /// `false`: the pure playout search is the reference the differential
    /// fixture was captured against;
    /// `au_differential.rs::hybrid_exact_mcgs_is_sound` gates the flag-on
    /// behavior.
    pub hybrid_exact: bool,
    /// Admission estimate for [`Self::hybrid_exact`]: the largest
    /// `estimates::reachable_pairs` value a subproblem may have and still be
    /// handed to the exact solver. It bounds a rectangle of bare class pairs,
    /// not the number of contextual states or the work below each state.
    /// Default 4096 as a historical compatibility value pending a current
    /// Criterion calibration.
    pub hybrid_threshold: u64,
    /// Live-incumbent arm pruning:
    /// cache every arm's admissible size lower bound at stats creation and
    /// exclude the arm the moment `bound > best_size(or)` against the node's
    /// CURRENT incumbent, which tightens as compositions arrive. STRICT
    /// comparison: the objective is lexicographic `(size, variant_mass)` and
    /// the bound is size-only, so an equal-size arm can still win the tie on
    /// variant mass (the same rule as `dominance_pruning`, whose creation-time
    /// check against the static generalize value this generalizes). An
    /// excluded arm counts as resolved for the closure walk: the certificate
    /// claim stays "every action realized or proven non-optimal". Requires
    /// `closed_bit` (the resolution accounting lives in the closure
    /// machinery); `run_mcgs_in` refuses the flag without it. Default
    /// `false`; `au_differential.rs::live_incumbent_pruning_is_sound` gates
    /// the flag-on behavior.
    pub live_incumbent_pruning: bool,
    /// Hybrid exact calls from inside the initial rollout: at every rollout frame whose
    /// subproblem passes the same admission gate as [`Self::hybrid_exact`],
    /// delegate the frame and use the result as the completed suffix. A call
    /// that completes supplies a contextually certified exact suffix; a call
    /// that exhausts `hybrid_node_budget` supplies only a feasible uncertified
    /// suffix. The node is terminal at creation when expansion later reaches it
    /// only in the completed case. The soundness
    /// argument is unchanged: same class pair, same side-or-pair context, same
    /// cycle mode, same action generators. Requires `hybrid_exact`; `run_mcgs_in` refuses the flag
    /// without it. Default `false`;
    /// `au_differential.rs::rollout_hybrid_mcgs_is_sound` gates the flag-on
    /// behavior.
    pub rollout_hybrid: bool,
    /// Session-level exact memo:
    /// side-context hybrid exact calls (`hybrid_exact`, `rollout_hybrid`) share
    /// one bare-pair memo of context-clean solves that outlives the individual
    /// call, so consecutive calls over overlapping subgraphs reuse instead of
    /// re-solving. Pair-context calls leave this memo unused until its support
    /// proof preserves pair correlations. The memo lives in the session state
    /// and rolls back with its token. Requires `hybrid_exact`.
    /// Default `false`;
    /// `au_differential.rs::persistent_memo_exact_is_sound` gates the flag-on
    /// behavior.
    pub session_exact_memo: bool,
    /// Second admission gate for hybrid exact calls: the node's own action
    /// count must be at or below this for the call to be admitted. It
    /// complements the bare-pair rectangle estimate, but neither gate bounds
    /// descendant contextual states or fan-out. Default `u64::MAX`: admission
    /// by rectangle alone, the reference behavior.
    pub hybrid_action_threshold: u64,
    /// In-call backstop for hybrid exact calls: a deterministic
    /// bound on solve work, in node entries. The admission gates read the
    /// entry node only and fan-out below it is unbounded by them, so one
    /// mis-admitted call inside playout 1 would otherwise block the first
    /// answer; on exhaustion the call returns its incumbent uncertified and
    /// (with `session_exact_memo`) keeps every completed subframe. Node
    /// entries, not wall clock, so certification stays deterministic.
    /// Default `None`: no bound, the reference behavior.
    pub hybrid_node_budget: Option<u64>,
    /// Static child seeding:
    /// expansion seeds a fresh child's value with its stored best size (at
    /// worst the generalize seed `expand_action` just offered, two array
    /// reads) instead of running a full `initial_rollout` per child, and the
    /// rollout runs on the child's FIRST SELECTION instead. Expansion of a
    /// k-child AND stops paying k greedy descents for children selection may
    /// never enter; estimates at birth are looser (the generalize value is
    /// the top of the interval instead of a sample inside it), which the
    /// normalization tolerates: it is the same U(n) role. The root keeps its
    /// eager rollout. Default `false`;
    /// `au_differential.rs::static_child_seed_mcgs_is_sound` gates the
    /// flag-on behavior (soundness, not fixture equality: the flag trades
    /// per-playout estimate quality for per-playout cost, so matched-playout
    /// quality may differ; the honest comparison is matched wall clock).
    pub static_child_seed: bool,
    /// Interval labels: carry a
    /// lower bound `L` alongside the incumbent `U` on every OR and AND stat
    /// and let it TIGHTEN from below as the search discovers that a
    /// subproblem is expensive, instead of freezing every arm at its static
    /// creation-time bound.
    ///
    /// `L(and) = 1 + Σ count · L(child)` (min-cost flow over child `L` for a
    /// transport arm) and `L(or) = min over its non-excluded arms`, so a
    /// node's floor rises as its children's floors rise, and that rise
    /// reaches the parent's arm. `sweep_arms` then excludes on the DYNAMIC
    /// bound, which strictly dominates the initial static one: identical where the
    /// static bound is already tight, and decisive where it is loose (two
    /// subterms with equal size profiles, hence equal `lb_pair`, whose true
    /// anti-unifiers differ by a lot).
    ///
    /// Propagation is path-only, like the Q values: a stale `L` is a weaker
    /// bound, never a wrong one, so soundness does not depend on the walk
    /// reaching every parent. Requires `live_incumbent_pruning` (whose
    /// exclusion and closure accounting it reuses). Default `false`;
    /// `au_differential.rs::interval_bounds_mcgs_is_sound` gates the flag-on
    /// behavior.
    pub interval_bounds: bool,
}

/// What the hybrid trigger did over one run (`McgsConfig::hybrid_exact`).
/// Plain counters, not search state: they are diagnostics only, so they are
/// outside the semi-persistent arenas and a `restore` leaves them alone.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct HybridStats {
    /// Subproblems handed to the exact solver.
    pub calls: u64,
    /// Of those, the ones that completed within the optional node budget and
    /// therefore returned a contextual exactness certificate.
    pub proved: u64,
    /// Total wall time spent inside those calls.
    pub time: std::time::Duration,
}

impl Default for McgsConfig {
    fn default() -> Self {
        McgsConfig {
            playouts: 1000,
            cycle_mode: CycleMode::AncestorOnly,
            exploration_constant: std::f64::consts::SQRT_2,
            x_target: 0.8,
            and_selector: AndSelector::default(),
            dominance_pruning: false,
            closed_bit: false,
            hybrid_exact: false,
            hybrid_threshold: DEFAULT_HYBRID_THRESHOLD,
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

/// Default [`McgsConfig::hybrid_threshold`].
///
/// This historical compatibility value predates the pair-mode fixed-point
/// solver. It is not a current performance optimum; recalibration requires the
/// maintained Criterion protocol.
pub const DEFAULT_HYBRID_THRESHOLD: u64 = 4096;

/// Builder payload for one OR-statistics node. The arena flattens edge state
/// into typed pools when this value is pushed.
struct OrStatsData<AS> {
    /// U(n): the node's first rollout estimate, one permanent unit-weight sample.
    initial_value: f64,
    /// Q(n), recomputed from children on every backpropagation through this node.
    value: f64,
    /// min(best_size(l), best_size(r)): the shared normalization basis.
    min_size: f64,
    /// max(best_size(l), best_size(r)): the shared normalization scale.
    max_size: f64,
    /// Terminal: l == r, exact, or no surviving actions.
    terminal: bool,
    /// Per-action edge visits N(n,a).
    edge_visits: Vec<u64>,
    /// Realized AND statistics per action (None = unrealized).
    edge_and: Vec<Option<AS>>,
    /// Per-action admissible size lower bound
    /// (`McgsConfig::live_incumbent_pruning`), clamped to `u32::MAX`.
    /// All zeros when the flag is off: a zero bound never excludes.
    edge_bounds: Vec<u32>,
}

/// Builder payload for one AND-statistics node. Child arrays are flattened into
/// pools when pushed. Transport map entries are positions in this payload's
/// child list and are converted to absolute typed child-pool IDs by the arena.
struct AndStatsData<OS, O> {
    parent: OS,
    /// The parent OR node's action slot this AND realizes; lets the closure
    /// walk skip the double decrement when live-incumbent pruning already
    /// accounted the slot.
    parent_slot: usize,
    op: O,
    commutative: bool,
    value: f64,
    child_or_stats: Vec<OS>,
    /// Per-child count, at the *surface* width — the seam between the two paths
    /// that write it.
    ///
    /// A fixed action writes a structural multiplicity here ([`EGraphConfig::M`],
    /// copied out of an [`ActionPair`]); a transport action writes a flow cell,
    /// at the transport solver's own narrower capacity. `u64` holds both without
    /// a fallible conversion — [`MultiplicityLike::to_u64`] is total and lossless
    /// at every configured width — so neither path needs a cap of its own here.
    /// Picking either contributor's width instead would impose that width on the
    /// other: `Cfg::M` would need a narrowing check on flow at `Multiplicity16`,
    /// and the solver's width would silently drop multiplicities the e-graph
    /// represents fine at `Multiplicity64`.
    ///
    /// [`EGraphConfig::M`]: crate::config::EGraphConfig::M
    /// [`ActionPair`]: super::actions::ActionPair
    /// [`MultiplicityLike::to_u64`]: crate::multiplicity::MultiplicityLike::to_u64
    child_counts: Vec<u64>,
    child_visits: Vec<u64>,
    round_robin: u64,
    transport_rows: Vec<u32>,
    transport_cols: Vec<u32>,
    transport_cell_map: Vec<Option<usize>>,
}

/// Borrowed OR-statistics node assembled from aligned arena fields.
struct OrStatsRef<'a, AS> {
    initial_value: f64,
    value: f64,
    min_size: f64,
    max_size: f64,
    terminal: bool,
    edge_visits: &'a [u64],
    edge_and: &'a [Option<AS>],
    /// Per-action excluded bit (`McgsConfig::live_incumbent_pruning`).
    edge_excluded: &'a [bool],
}

/// Borrowed AND-statistics node assembled from aligned arena fields.
struct AndStatsRef<'a, OS, O, CS> {
    parent: OS,
    op: O,
    commutative: bool,
    value: f64,
    child_or_stats: &'a [OS],
    /// See [`AndStatsData::child_counts`] for why this is the surface width.
    child_counts: &'a [u64],
    child_visits: &'a [u64],
    round_robin: u64,
    transport_rows: &'a [u32],
    transport_cols: &'a [u32],
    transport_cell_map: &'a [Option<CS>],
}

/// Token for the OR-statistics arena. It contains only tokens issued by the
/// standard semi-persistent containers that own each aligned field.
#[derive(Clone, Copy, Debug)]
struct OrStatsToken {
    or_ids: VecToken,
    min_size: VecToken,
    max_size: VecToken,
    terminal: VecToken,
    edge_spans: VecToken,
    initial_value: VecToken,
    value: VecToken,
    edge_visits: VecToken,
    edge_and: VecToken,
    edge_bounds: VecToken,
    edge_excluded: VecToken,
    rolled: VecToken,
    edge_lb: VecToken,
    node_lb: VecToken,
    first_unrealized: VecToken,
    transport_descs: VecToken,
    closed: VecToken,
    open_edges: VecToken,
    parent_head: VecToken,
    parent_and: VecToken,
    parent_next: VecToken,
}

/// OR statistics stored in aligned semi-persistent arenas. Node structure is
/// append-only; mutable values and flattened edge state use VecP.
/// Every column is addressed by `A::OrStats`, so `A::Index` is the index word
/// throughout — the append-only columns now match the `VecP` ones instead of holding
/// `usize` frame lengths for positions that provably fit the config word.
struct OrStatsArena<A: AuIds, O: DenseId> {
    or_ids: AppendOnlyVec<A::Or, A::Index>,
    min_size: AppendOnlyVec<f64, A::Index>,
    max_size: AppendOnlyVec<f64, A::Index>,
    terminal: AppendOnlyVec<bool, A::Index>,
    edge_spans: AppendOnlyVec<super::Span<A::OrEdgeStat>, A::Index>,
    initial_value: VecP<f64, A::Index>,
    value: VecP<f64, A::Index>,
    edge_visits: VecP<u64, A::Index>,
    edge_and: VecP<Option<A::AndStats>, A::Index>,
    /// Per-slot admissible size lower bound, fixed at creation
    /// (`McgsConfig::live_incumbent_pruning`); zeros when the flag is off.
    edge_bounds: AppendOnlyVec<u32, A::Index>,
    /// Per-slot excluded bit: the arm's bound strictly exceeds the node's
    /// live incumbent, so the arm is proven non-optimal and counts as
    /// resolved. Set by `sweep_arms`, never cleared; a restore rewinds it
    /// with `open_edges`.
    edge_excluded: VecP<bool, A::Index>,
    /// Whether the node's initial rollout has run
    /// (`McgsConfig::static_child_seed`): a seeded-only node runs it on its
    /// first selection. Terminal and creation-closed nodes are born rolled
    /// (their value is final).
    rolled: VecP<bool, A::Index>,
    /// Per-slot DYNAMIC lower bound (`McgsConfig::interval_bounds`): starts
    /// at the slot's static `edge_bounds` value and rises as the arm's
    /// realized subtree reveals its floor. Monotone non-decreasing, so it
    /// stays a valid bound; a restore rewinds it with the rest.
    edge_lb: VecP<u32, A::Index>,
    /// Per-node floor `L` (`McgsConfig::interval_bounds`): the minimum over
    /// this node's non-excluded arms, which is what the PARENT's arm bound
    /// sums. Terminal nodes carry their exact value.
    node_lb: VecP<u32, A::Index>,
    /// Index of the node's first unhandled action: every slot below it is
    /// realized or excluded. Playout expansion is the
    /// only writer of `edge_and`, and it always realizes this index, so the
    /// realized slots form a prefix and the cursor advances monotonically.
    /// A restore rewinds it together with `edge_and` to the same mark, which
    /// keeps the prefix invariant.
    first_unrealized: VecP<A::Index, A::Index>,
    transport_descs: AppendOnlyVec<Vec<TransportActionDesc<O, A::Class>>, A::Index>,
    /// Closed bit (`McgsConfig::closed_bit`): the node's subgraph is fully
    /// resolved. Set at birth for terminal nodes and by the closure walk
    /// otherwise; never cleared, so a restore is what rewinds it.
    closed: VecP<bool, A::Index>,
    /// Action slots that are not known resolved: unrealized slots plus
    /// realized slots whose AND node is open. Starts at the action count (zero
    /// for a terminal node), and reaching zero is what closes the node —
    /// realizing a slot does not decrement it, closing the slot's AND does.
    open_edges: VecP<A::Index, A::Index>,
    /// Head of this node's reverse-edge list, an index into
    /// `parent_and`/`parent_next`.
    parent_head: VecP<Option<A::Index>, A::Index>,
    /// Reverse-edge pool: the AND node of one parent entry. One entry per
    /// child *position*, so an AND holding the same OR node twice appears
    /// twice and both of its open-child slots are decremented when that node
    /// closes. Written only under `closed_bit`.
    parent_and: AppendOnlyVec<A::AndStats, A::Index>,
    /// Reverse-edge pool: the next entry of the same node's list.
    parent_next: AppendOnlyVec<Option<A::Index>, A::Index>,
}

/// Preconstruct a typed span and validate its exclusive end and final typed
/// position before any owning arena is mutated.
fn checked_pool_span<I: DenseId>(start: usize, len: usize, pool: &str) -> super::Span<I> {
    let end = start
        .checked_add(len)
        .unwrap_or_else(|| panic!("{pool} span end overflows usize"));
    I::Index::try_from_usize(end)
        .unwrap_or_else(|| panic!("{pool} span end exceeds configured index width"));
    let span = super::Span::new(start, len);
    if len != 0 {
        // prod-parity: the last typed position must be a representable id. Verus's
        // `DenseId::from_usize` MASKS out-of-range input (so the type invariant
        // always holds) rather than panicking as production's did, so the
        // id-range check moves to `try_new`, which returns `None` past the id
        // bound (e.g. 128 for a 7-bit id, where `from_usize` would wrap to 0).
        I::try_new(end - 1)
            .unwrap_or_else(|| panic!("{pool} span end exceeds configured id width"));
    }
    span
}

impl<A: AuIds, O: DenseId> OrStatsArena<A, O> {
    fn new() -> Self {
        Self {
            or_ids: AppendOnlyVec::new(),
            min_size: AppendOnlyVec::new(),
            max_size: AppendOnlyVec::new(),
            terminal: AppendOnlyVec::new(),
            edge_spans: AppendOnlyVec::new(),
            initial_value: VecP::new(),
            value: VecP::new(),
            edge_visits: VecP::new(),
            edge_and: VecP::new(),
            edge_bounds: AppendOnlyVec::new(),
            edge_excluded: VecP::new(),
            rolled: VecP::new(),
            edge_lb: VecP::new(),
            node_lb: VecP::new(),
            first_unrealized: VecP::new(),
            transport_descs: AppendOnlyVec::new(),
            closed: VecP::new(),
            open_edges: VecP::new(),
            parent_head: VecP::new(),
            parent_and: AppendOnlyVec::new(),
            parent_next: AppendOnlyVec::new(),
        }
    }

    #[inline]
    fn index<I: DenseId<Index = A::Index>>(id: I) -> A::Index {
        A::Index::try_from_usize(id.to_usize()).expect("MCGS id exceeds configured index width")
    }

    /// Node count, in the configured index word: the next node lands at exactly
    /// this index, and every aligned column agrees with it.
    fn len(&self) -> A::Index {
        self.or_ids.len()
    }

    fn push(
        &mut self,
        or_id: A::Or,
        data: OrStatsData<A::AndStats>,
        transport_descs: Vec<TransportActionDesc<O, A::Class>>,
    ) -> A::OrStats {
        assert_eq!(data.edge_visits.len(), data.edge_and.len());
        assert_eq!(data.edge_visits.len(), data.edge_bounds.len());

        let node_len = self.len();
        assert_eq!(self.min_size.len(), node_len);
        assert_eq!(self.max_size.len(), node_len);
        assert_eq!(self.terminal.len(), node_len);
        assert_eq!(self.edge_spans.len(), node_len);
        assert_eq!(self.initial_value.len(), node_len);
        assert_eq!(self.value.len(), node_len);
        assert_eq!(self.rolled.len(), node_len);
        assert_eq!(self.node_lb.len(), node_len);
        assert_eq!(self.first_unrealized.len(), node_len);
        assert_eq!(self.transport_descs.len(), node_len);
        assert_eq!(self.closed.len(), node_len);
        assert_eq!(self.open_edges.len(), node_len);
        assert_eq!(self.parent_head.len(), node_len);

        let edge_start = self.edge_visits.len().as_usize();
        assert_eq!(self.edge_and.len().as_usize(), edge_start);
        assert_eq!(self.edge_bounds.len().as_usize(), edge_start);
        assert_eq!(self.edge_excluded.len().as_usize(), edge_start);
        // prod-parity: trap when the node id would exceed its width. Production's
        // `from_usize` panicked on overflow; verus's masks, so the check is
        // `try_new` (None past the id bound) before mutating any pool.
        let id = A::OrStats::try_new(node_len.as_usize())
            .unwrap_or_else(|| panic!("OR-stats node id exceeds configured id width"));
        let edge_span = checked_pool_span::<A::OrEdgeStat>(
            edge_start,
            data.edge_visits.len(),
            "OR edge-statistics pool",
        );
        // A terminal node is closed at birth and has nothing open; every other
        // node starts with every action slot open (`ensure_or_stats` makes a
        // node with no surviving action terminal, so this is nonzero there).
        let open_edges = if data.terminal {
            A::Index::try_from_usize(0).expect("zero fits every index word")
        } else {
            A::Index::try_from_usize(data.edge_visits.len())
                .expect("action count bounded by the validated edge span")
        };
        let closed = data.terminal;

        for visit in data.edge_visits {
            self.edge_visits
                .try_push(visit)
                .expect("AU arena sized by its index word");
        }
        for and_id in data.edge_and {
            self.edge_and
                .try_push(and_id)
                .expect("AU arena sized by its index word");
        }
        let mut floor = u32::MAX;
        for bound in data.edge_bounds {
            self.edge_bounds
                .try_push(bound)
                .expect("AU arena sized by its index word");
            self.edge_excluded
                .try_push(false)
                .expect("AU arena sized by its index word");
            self.edge_lb
                .try_push(bound)
                .expect("AU arena sized by its index word");
            floor = floor.min(bound);
        }
        self.or_ids
            .try_push(or_id)
            .expect("AU arena sized by its index word");
        self.min_size
            .try_push(data.min_size)
            .expect("AU arena sized by its index word");
        self.max_size
            .try_push(data.max_size)
            .expect("AU arena sized by its index word");
        self.terminal
            .try_push(data.terminal)
            .expect("AU arena sized by its index word");
        self.edge_spans
            .try_push(edge_span)
            .expect("AU arena sized by its index word");
        self.initial_value
            .try_push(data.initial_value)
            .expect("AU arena sized by its index word");
        self.value
            .try_push(data.value)
            .expect("AU arena sized by its index word");
        self.rolled
            .try_push(data.terminal)
            .expect("AU arena sized by its index word");
        // A terminal node's floor is its exact value; otherwise the minimum
        // static arm bound, which is what `L(or)` starts at.
        self.node_lb
            .try_push(if data.terminal {
                data.value.max(0.0) as u32
            } else if floor == u32::MAX {
                0
            } else {
                floor
            })
            .expect("AU arena sized by its index word");
        self.first_unrealized
            .try_push(A::Index::try_from_usize(0).expect("zero fits every index word"))
            .expect("AU arena sized by its index word");
        self.transport_descs
            .try_push(transport_descs)
            .expect("AU arena sized by its index word");
        self.closed
            .try_push(closed)
            .expect("AU arena sized by its index word");
        self.open_edges
            .try_push(open_edges)
            .expect("AU arena sized by its index word");
        self.parent_head
            .try_push(None)
            .expect("AU arena sized by its index word");
        id
    }

    #[inline]
    fn closed(&self, id: A::OrStats) -> bool {
        self.closed.get(Self::index(id))
    }

    /// Set the closed bit. Idempotent by construction: the closure walk only
    /// calls this on a node whose last open edge just closed, and a closed
    /// node's `open_edges` never leaves zero.
    fn set_closed(&mut self, id: A::OrStats) {
        self.closed.set(Self::index(id), true);
    }

    #[inline]
    fn open_edges(&self, id: A::OrStats) -> usize {
        self.open_edges.get(Self::index(id)).as_usize()
    }

    /// Account one action slot as resolved: the slot's AND node just closed.
    fn close_edge(&mut self, id: A::OrStats) {
        let node = Self::index(id);
        let open = self.open_edges.get(node).as_usize();
        debug_assert!(open > 0, "closing an edge of a node with none open");
        self.open_edges.set(
            node,
            A::Index::try_from_usize(open - 1).expect("decrement of a valid index"),
        );
    }

    /// Record `and_id` as a parent of `child`: one entry per child position,
    /// prepended to the child's reverse-edge list.
    fn push_parent(&mut self, child: A::OrStats, and_id: A::AndStats) {
        let node = Self::index(child);
        let entry = self.parent_and.len();
        let head = self.parent_head.get(node);
        self.parent_and
            .try_push(and_id)
            .expect("AU arena sized by its index word");
        self.parent_next
            .try_push(head)
            .expect("AU arena sized by its index word");
        self.parent_head.set(node, Some(entry));
    }

    #[inline]
    fn parent_head(&self, id: A::OrStats) -> Option<A::Index> {
        self.parent_head.get(Self::index(id))
    }

    /// One reverse-edge entry: its AND node and the next entry of the list.
    #[inline]
    fn parent_entry(&self, entry: A::Index) -> (A::AndStats, Option<A::Index>) {
        (*self.parent_and.get(entry), *self.parent_next.get(entry))
    }

    #[inline]
    fn or_id(&self, id: A::OrStats) -> A::Or {
        *self.or_ids.get(id.to_index())
    }

    #[inline]
    fn edge_span(&self, id: A::OrStats) -> super::Span<A::OrEdgeStat> {
        *self.edge_spans.get(id.to_index())
    }

    #[inline]
    fn edge_id(&self, id: A::OrStats, action: usize) -> A::OrEdgeStat {
        let span = self.edge_span(id);
        assert!(action < span.len_usize(), "OR action index out of bounds");
        crate::id::id_at(span.start_usize() + action)
    }

    fn get(&self, id: A::OrStats) -> OrStatsRef<'_, A::AndStats> {
        let node = Self::index(id);
        let span = self.edge_span(id);
        let range = span.start_usize()..span.end_usize();
        OrStatsRef {
            initial_value: self.initial_value.get(node),
            value: self.value.get(node),
            min_size: *self.min_size.get(id.to_index()),
            max_size: *self.max_size.get(id.to_index()),
            terminal: *self.terminal.get(id.to_index()),
            edge_visits: &self.edge_visits.as_slice().expect("VecP is contiguous")[range.clone()],
            edge_and: &self.edge_and.as_slice().expect("VecP is contiguous")[range.clone()],
            edge_excluded: &self.edge_excluded.as_slice().expect("VecP is contiguous")[range],
        }
    }

    #[inline]
    fn transport_descs(&self, id: A::OrStats) -> &[TransportActionDesc<O, A::Class>] {
        self.transport_descs.get(id.to_index())
    }

    fn set_initial_value(&mut self, id: A::OrStats, value: f64) {
        self.initial_value.set(Self::index(id), value);
    }

    fn set_value(&mut self, id: A::OrStats, value: f64) {
        self.value.set(Self::index(id), value);
    }

    fn bump_edge_visit(&mut self, id: A::OrStats, action: usize) {
        let edge = Self::index(self.edge_id(id, action));
        self.edge_visits.set(edge, self.edge_visits.get(edge) + 1);
    }

    fn set_edge_and(&mut self, id: A::OrStats, action: usize, value: Option<A::AndStats>) {
        let edge = Self::index(self.edge_id(id, action));
        self.edge_and.set(edge, value);
    }

    #[inline]
    fn edge_bound(&self, id: A::OrStats, action: usize) -> u32 {
        *self.edge_bounds.get(self.edge_id(id, action).to_index())
    }

    #[inline]
    fn edge_excluded(&self, id: A::OrStats, action: usize) -> bool {
        self.edge_excluded
            .get(Self::index(self.edge_id(id, action)))
    }

    fn set_edge_excluded(&mut self, id: A::OrStats, action: usize) {
        let edge = Self::index(self.edge_id(id, action));
        self.edge_excluded.set(edge, true);
    }

    #[inline]
    fn edge_and_slot(&self, id: A::OrStats, action: usize) -> Option<A::AndStats> {
        self.edge_and.get(Self::index(self.edge_id(id, action)))
    }

    #[inline]
    fn rolled(&self, id: A::OrStats) -> bool {
        self.rolled.get(Self::index(id))
    }

    #[inline]
    fn edge_lb(&self, id: A::OrStats, action: usize) -> u32 {
        self.edge_lb.get(Self::index(self.edge_id(id, action)))
    }

    fn set_edge_lb(&mut self, id: A::OrStats, action: usize, value: u32) {
        let edge = Self::index(self.edge_id(id, action));
        // Monotone: a bound never loosens, so a stale write cannot weaken
        // one that a deeper walk already tightened.
        if value > self.edge_lb.get(edge) {
            self.edge_lb.set(edge, value);
        }
    }

    #[inline]
    fn node_lb(&self, id: A::OrStats) -> u32 {
        self.node_lb.get(Self::index(id))
    }

    fn set_node_lb(&mut self, id: A::OrStats, value: u32) {
        let node = Self::index(id);
        if value > self.node_lb.get(node) {
            self.node_lb.set(node, value);
        }
    }

    fn set_rolled(&mut self, id: A::OrStats) {
        self.rolled.set(Self::index(id), true);
    }

    /// The node's first unrealized action index (== its edge count when every
    /// action is realized).
    #[inline]
    fn first_unrealized(&self, id: A::OrStats) -> usize {
        self.first_unrealized.get(Self::index(id)).as_usize()
    }

    /// Advance the cursor past a just-handled slot: realized by expansion, or
    /// excluded under live-incumbent pruning. Valid only from the expansion
    /// path, which handles exactly the cursor's slot.
    fn advance_first_unrealized(&mut self, id: A::OrStats) {
        let node = Self::index(id);
        let next = self.first_unrealized.get(node).as_usize() + 1;
        debug_assert!(next <= self.edge_span(id).len_usize());
        self.first_unrealized.set(
            node,
            A::Index::try_from_usize(next).expect("cursor bounded by the node's edge span"),
        );
    }

    fn mark(&mut self) -> OrStatsToken {
        OrStatsToken {
            or_ids: self
                .or_ids
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            min_size: self
                .min_size
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            max_size: self
                .max_size
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            terminal: self
                .terminal
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            edge_spans: self
                .edge_spans
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            initial_value: self
                .initial_value
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            value: self
                .value
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            edge_visits: self
                .edge_visits
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            edge_and: self
                .edge_and
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            edge_bounds: self
                .edge_bounds
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            edge_excluded: self
                .edge_excluded
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            rolled: self
                .rolled
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            edge_lb: self
                .edge_lb
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            node_lb: self
                .node_lb
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            first_unrealized: self
                .first_unrealized
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            transport_descs: self
                .transport_descs
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            closed: self
                .closed
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            open_edges: self
                .open_edges
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            parent_head: self
                .parent_head
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            parent_and: self
                .parent_and
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            parent_next: self
                .parent_next
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
        }
    }

    fn is_valid_token(&self, token: &OrStatsToken) -> bool {
        self.or_ids.is_valid_token(&token.or_ids)
            && self.min_size.is_valid_token(&token.min_size)
            && self.max_size.is_valid_token(&token.max_size)
            && self.terminal.is_valid_token(&token.terminal)
            && self.edge_spans.is_valid_token(&token.edge_spans)
            && self.initial_value.is_valid_token(&token.initial_value)
            && self.value.is_valid_token(&token.value)
            && self.edge_visits.is_valid_token(&token.edge_visits)
            && self.edge_and.is_valid_token(&token.edge_and)
            && self.edge_bounds.is_valid_token(&token.edge_bounds)
            && self.edge_excluded.is_valid_token(&token.edge_excluded)
            && self.rolled.is_valid_token(&token.rolled)
            && self.edge_lb.is_valid_token(&token.edge_lb)
            && self.node_lb.is_valid_token(&token.node_lb)
            && self
                .first_unrealized
                .is_valid_token(&token.first_unrealized)
            && self.transport_descs.is_valid_token(&token.transport_descs)
            && self.closed.is_valid_token(&token.closed)
            && self.open_edges.is_valid_token(&token.open_edges)
            && self.parent_head.is_valid_token(&token.parent_head)
            && self.parent_and.is_valid_token(&token.parent_and)
            && self.parent_next.is_valid_token(&token.parent_next)
    }

    fn restore(&mut self, token: OrStatsToken) {
        assert!(self.is_valid_token(&token), "OrStatsArena: invalid token");
        self.parent_next
            .try_restore(token.parent_next)
            .expect("restore: token minted by this container's own mark");
        self.parent_and
            .try_restore(token.parent_and)
            .expect("restore: token minted by this container's own mark");
        self.parent_head
            .try_restore(token.parent_head)
            .expect("restore: token minted by this container's own mark");
        self.open_edges
            .try_restore(token.open_edges)
            .expect("restore: token minted by this container's own mark");
        self.closed
            .try_restore(token.closed)
            .expect("restore: token minted by this container's own mark");
        self.transport_descs
            .try_restore(token.transport_descs)
            .expect("restore: token minted by this container's own mark");
        self.first_unrealized
            .try_restore(token.first_unrealized)
            .expect("restore: token minted by this container's own mark");
        self.node_lb
            .try_restore(token.node_lb)
            .expect("restore: token minted by this container's own mark");
        self.edge_lb
            .try_restore(token.edge_lb)
            .expect("restore: token minted by this container's own mark");
        self.rolled
            .try_restore(token.rolled)
            .expect("restore: token minted by this container's own mark");
        self.edge_excluded
            .try_restore(token.edge_excluded)
            .expect("restore: token minted by this container's own mark");
        self.edge_bounds
            .try_restore(token.edge_bounds)
            .expect("restore: token minted by this container's own mark");
        self.edge_and
            .try_restore(token.edge_and)
            .expect("restore: token minted by this container's own mark");
        self.edge_visits
            .try_restore(token.edge_visits)
            .expect("restore: token minted by this container's own mark");
        self.value
            .try_restore(token.value)
            .expect("restore: token minted by this container's own mark");
        self.initial_value
            .try_restore(token.initial_value)
            .expect("restore: token minted by this container's own mark");
        self.edge_spans
            .try_restore(token.edge_spans)
            .expect("restore: token minted by this container's own mark");
        self.terminal
            .try_restore(token.terminal)
            .expect("restore: token minted by this container's own mark");
        self.max_size
            .try_restore(token.max_size)
            .expect("restore: token minted by this container's own mark");
        self.min_size
            .try_restore(token.min_size)
            .expect("restore: token minted by this container's own mark");
        self.or_ids
            .try_restore(token.or_ids)
            .expect("restore: token minted by this container's own mark");
    }
}

/// Token for the AND-statistics arena. It contains only tokens issued by the
/// standard semi-persistent containers that own each aligned field.
#[derive(Clone, Copy, Debug)]
struct AndStatsToken {
    parent: VecToken,
    parent_slot: VecToken,
    lb: VecToken,
    op: VecToken,
    commutative: VecToken,
    child_spans: VecToken,
    child_or_stats: VecToken,
    value: VecToken,
    child_counts: VecToken,
    child_visits: VecToken,
    round_robin: VecToken,
    transport_rows: VecToken,
    transport_cols: VecToken,
    transport_cell_map: VecToken,
    closed: VecToken,
    open_children: VecToken,
}

/// AND statistics stored in aligned semi-persistent arenas. Child state is
/// flattened and addressed by `A::AndChildStat` spans and IDs.
/// Node columns are addressed by `A::AndStats` and the flattened child columns by
/// `A::AndChildStat`; both words are `A::Index`, so that is the index type.
struct AndStatsArena<A: AuIds, O: DenseId> {
    parent: AppendOnlyVec<A::OrStats, A::Index>,
    /// The parent's action slot each node realizes (see
    /// [`AndStatsData::parent_slot`]).
    parent_slot: AppendOnlyVec<A::Index, A::Index>,
    op: AppendOnlyVec<O, A::Index>,
    commutative: AppendOnlyVec<bool, A::Index>,
    child_spans: AppendOnlyVec<super::Span<A::AndChildStat>, A::Index>,
    child_or_stats: AppendOnlyVec<A::OrStats, A::Index>,
    value: VecP<f64, A::Index>,
    /// See [`AndStatsData::child_counts`] for why this is the surface width.
    child_counts: VecP<u64, A::Index>,
    child_visits: VecP<u64, A::Index>,
    round_robin: VecP<u64, A::Index>,
    transport_rows: AppendOnlyVec<Vec<u32>, A::Index>,
    transport_cols: AppendOnlyVec<Vec<u32>, A::Index>,
    transport_cell_map: AppendOnlyVec<Vec<Option<A::AndChildStat>>, A::Index>,
    /// Closed bit (`McgsConfig::closed_bit`): every child is closed, so this
    /// action's subgraph is fully resolved.
    closed: VecP<bool, A::Index>,
    /// Child *positions* whose OR node is still open. Set at creation from the
    /// children's bits, decremented as they close; reaching zero closes the
    /// AND node.
    open_children: VecP<A::Index, A::Index>,
    /// Dynamic floor `L` (`McgsConfig::interval_bounds`):
    /// `1 + Σ count · L(child)`, recomputed as children's floors rise.
    /// Monotone non-decreasing, so it is always a valid lower bound.
    lb: VecP<u32, A::Index>,
}

impl<A: AuIds, O: DenseId> AndStatsArena<A, O> {
    fn new() -> Self {
        Self {
            parent: AppendOnlyVec::new(),
            parent_slot: AppendOnlyVec::new(),
            op: AppendOnlyVec::new(),
            commutative: AppendOnlyVec::new(),
            child_spans: AppendOnlyVec::new(),
            child_or_stats: AppendOnlyVec::new(),
            value: VecP::new(),
            child_counts: VecP::new(),
            child_visits: VecP::new(),
            round_robin: VecP::new(),
            transport_rows: AppendOnlyVec::new(),
            transport_cols: AppendOnlyVec::new(),
            transport_cell_map: AppendOnlyVec::new(),
            closed: VecP::new(),
            open_children: VecP::new(),
            lb: VecP::new(),
        }
    }

    #[inline]
    fn index<I: DenseId<Index = A::Index>>(id: I) -> A::Index {
        A::Index::try_from_usize(id.to_usize()).expect("MCGS id exceeds configured index width")
    }

    /// Node count, in the configured index word; see the OR-stats counterpart.
    fn len(&self) -> A::Index {
        self.parent.len()
    }

    fn push(&mut self, data: AndStatsData<A::OrStats, O>) -> A::AndStats {
        assert_eq!(data.child_or_stats.len(), data.child_counts.len());
        assert_eq!(data.child_or_stats.len(), data.child_visits.len());

        let node_len = self.len();
        assert_eq!(self.parent_slot.len(), node_len);
        assert_eq!(self.op.len(), node_len);
        assert_eq!(self.commutative.len(), node_len);
        assert_eq!(self.child_spans.len(), node_len);
        assert_eq!(self.value.len(), node_len);
        assert_eq!(self.round_robin.len(), node_len);
        assert_eq!(self.transport_rows.len(), node_len);
        assert_eq!(self.transport_cols.len(), node_len);
        assert_eq!(self.transport_cell_map.len(), node_len);
        assert_eq!(self.closed.len(), node_len);
        assert_eq!(self.open_children.len(), node_len);
        assert_eq!(self.lb.len(), node_len);

        let child_start = self.child_or_stats.len().as_usize();
        assert_eq!(self.child_counts.len().as_usize(), child_start);
        assert_eq!(self.child_visits.len().as_usize(), child_start);
        let child_len = data.child_or_stats.len();
        // prod-parity: trap on node-id overflow (verus `from_usize` masks; use
        // `try_new`). See the OR-stats `push` for the rationale.
        let id = A::AndStats::try_new(node_len.as_usize())
            .unwrap_or_else(|| panic!("AND-stats node id exceeds configured id width"));
        let child_span = checked_pool_span::<A::AndChildStat>(
            child_start,
            child_len,
            "AND child-statistics pool",
        );
        let typed_cell_map: Vec<Option<A::AndChildStat>> = data
            .transport_cell_map
            .iter()
            .map(|&position| {
                position.map(|position| {
                    assert!(
                        position < child_len,
                        "transport child position out of bounds"
                    );
                    let absolute = child_start
                        .checked_add(position)
                        .expect("transport child position overflows usize");
                    crate::id::id_at(absolute)
                })
            })
            .collect();

        for child in data.child_or_stats {
            self.child_or_stats
                .try_push(child)
                .expect("AU arena sized by its index word");
        }
        for count in data.child_counts {
            self.child_counts
                .try_push(count)
                .expect("AU arena sized by its index word");
        }
        for visits in data.child_visits {
            self.child_visits
                .try_push(visits)
                .expect("AU arena sized by its index word");
        }
        self.parent
            .try_push(data.parent)
            .expect("AU arena sized by its index word");
        self.parent_slot
            .try_push(
                A::Index::try_from_usize(data.parent_slot)
                    .expect("action slot bounded by the validated edge span"),
            )
            .expect("AU arena sized by its index word");
        self.op
            .try_push(data.op)
            .expect("AU arena sized by its index word");
        self.commutative
            .try_push(data.commutative)
            .expect("AU arena sized by its index word");
        self.child_spans
            .try_push(child_span)
            .expect("AU arena sized by its index word");
        self.value
            .try_push(data.value)
            .expect("AU arena sized by its index word");
        self.round_robin
            .try_push(data.round_robin)
            .expect("AU arena sized by its index word");
        self.transport_rows
            .try_push(data.transport_rows)
            .expect("AU arena sized by its index word");
        self.transport_cols
            .try_push(data.transport_cols)
            .expect("AU arena sized by its index word");
        self.transport_cell_map
            .try_push(typed_cell_map)
            .expect("AU arena sized by its index word");
        self.closed
            .try_push(false)
            .expect("AU arena sized by its index word");
        // Every position starts open; `McgsState::push_and_stat` discounts the
        // children that are already closed, and the closure walk is what turns
        // a zero count into the closed bit.
        self.open_children
            .try_push(
                A::Index::try_from_usize(child_len)
                    .expect("child count bounded by the validated child span"),
            )
            .expect("AU arena sized by its index word");
        // The operator itself; children raise it as their own floors arrive.
        self.lb
            .try_push(1)
            .expect("AU arena sized by its index word");
        id
    }

    #[inline]
    fn closed(&self, id: A::AndStats) -> bool {
        self.closed.get(Self::index(id))
    }

    /// The parent OR node's action slot this node realizes.
    #[inline]
    fn parent_slot(&self, id: A::AndStats) -> usize {
        self.parent_slot.get(id.to_index()).as_usize()
    }

    #[inline]
    fn lb(&self, id: A::AndStats) -> u32 {
        self.lb.get(Self::index(id))
    }

    fn set_lb(&mut self, id: A::AndStats, value: u32) {
        let node = Self::index(id);
        if value > self.lb.get(node) {
            self.lb.set(node, value);
        }
    }

    fn set_closed(&mut self, id: A::AndStats) {
        self.closed.set(Self::index(id), true);
    }

    #[inline]
    fn open_children(&self, id: A::AndStats) -> usize {
        self.open_children.get(Self::index(id)).as_usize()
    }

    /// Account one child position as resolved: that child's OR node closed (or
    /// was already closed when this node was created).
    fn close_child(&mut self, id: A::AndStats) {
        let node = Self::index(id);
        let open = self.open_children.get(node).as_usize();
        debug_assert!(open > 0, "closing a child of a node with none open");
        self.open_children.set(
            node,
            A::Index::try_from_usize(open - 1).expect("decrement of a valid index"),
        );
    }

    #[inline]
    fn child_span(&self, id: A::AndStats) -> super::Span<A::AndChildStat> {
        *self.child_spans.get(id.to_index())
    }

    #[inline]
    fn child_id(&self, id: A::AndStats, position: usize) -> A::AndChildStat {
        let span = self.child_span(id);
        assert!(position < span.len_usize(), "AND child index out of bounds");
        crate::id::id_at(span.start_usize() + position)
    }

    #[inline]
    fn child_or(&self, child: A::AndChildStat) -> A::OrStats {
        *self.child_or_stats.get(child.to_index())
    }

    #[cfg(test)]
    fn child_visits(&self, id: A::AndStats) -> &[u64] {
        let span = self.child_span(id);
        &self.child_visits.as_slice().expect("VecP is contiguous")
            [span.start_usize()..span.end_usize()]
    }

    fn get(&self, id: A::AndStats) -> AndStatsRef<'_, A::OrStats, O, A::AndChildStat> {
        let node = Self::index(id);
        let span = self.child_span(id);
        let range = span.start_usize()..span.end_usize();
        AndStatsRef {
            parent: *self.parent.get(id.to_index()),
            op: *self.op.get(id.to_index()),
            commutative: *self.commutative.get(id.to_index()),
            value: self.value.get(node),
            child_or_stats: &self.child_or_stats.as_slice()[range.clone()],
            child_counts: &self.child_counts.as_slice().expect("VecP is contiguous")[range.clone()],
            child_visits: &self.child_visits.as_slice().expect("VecP is contiguous")[range],
            round_robin: self.round_robin.get(node),
            transport_rows: self.transport_rows.get(id.to_index()),
            transport_cols: self.transport_cols.get(id.to_index()),
            transport_cell_map: self.transport_cell_map.get(id.to_index()),
        }
    }

    fn set_value(&mut self, id: A::AndStats, value: f64) {
        self.value.set(Self::index(id), value);
    }

    fn set_child_count(&mut self, child: A::AndChildStat, value: u64) {
        self.child_counts.set(Self::index(child), value);
    }

    fn bump_child_visit(&mut self, child: A::AndChildStat) {
        let child = Self::index(child);
        self.child_visits
            .set(child, self.child_visits.get(child) + 1);
    }

    fn bump_round_robin(&mut self, id: A::AndStats) {
        let node = Self::index(id);
        self.round_robin.set(node, self.round_robin.get(node) + 1);
    }

    fn mark(&mut self) -> AndStatsToken {
        AndStatsToken {
            parent: self
                .parent
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            parent_slot: self
                .parent_slot
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            lb: self
                .lb
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            op: self
                .op
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            commutative: self
                .commutative
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            child_spans: self
                .child_spans
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            child_or_stats: self
                .child_or_stats
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            value: self
                .value
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            child_counts: self
                .child_counts
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            child_visits: self
                .child_visits
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            round_robin: self
                .round_robin
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            transport_rows: self
                .transport_rows
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            transport_cols: self
                .transport_cols
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            transport_cell_map: self
                .transport_cell_map
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            closed: self
                .closed
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            open_children: self
                .open_children
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
        }
    }

    fn is_valid_token(&self, token: &AndStatsToken) -> bool {
        self.parent.is_valid_token(&token.parent)
            && self.parent_slot.is_valid_token(&token.parent_slot)
            && self.lb.is_valid_token(&token.lb)
            && self.op.is_valid_token(&token.op)
            && self.commutative.is_valid_token(&token.commutative)
            && self.child_spans.is_valid_token(&token.child_spans)
            && self.child_or_stats.is_valid_token(&token.child_or_stats)
            && self.value.is_valid_token(&token.value)
            && self.child_counts.is_valid_token(&token.child_counts)
            && self.child_visits.is_valid_token(&token.child_visits)
            && self.round_robin.is_valid_token(&token.round_robin)
            && self.transport_rows.is_valid_token(&token.transport_rows)
            && self.transport_cols.is_valid_token(&token.transport_cols)
            && self
                .transport_cell_map
                .is_valid_token(&token.transport_cell_map)
            && self.closed.is_valid_token(&token.closed)
            && self.open_children.is_valid_token(&token.open_children)
    }

    fn restore(&mut self, token: AndStatsToken) {
        assert!(self.is_valid_token(&token), "AndStatsArena: invalid token");
        self.open_children
            .try_restore(token.open_children)
            .expect("restore: token minted by this container's own mark");
        self.closed
            .try_restore(token.closed)
            .expect("restore: token minted by this container's own mark");
        self.transport_cell_map
            .try_restore(token.transport_cell_map)
            .expect("restore: token minted by this container's own mark");
        self.transport_cols
            .try_restore(token.transport_cols)
            .expect("restore: token minted by this container's own mark");
        self.transport_rows
            .try_restore(token.transport_rows)
            .expect("restore: token minted by this container's own mark");
        self.round_robin
            .try_restore(token.round_robin)
            .expect("restore: token minted by this container's own mark");
        self.child_visits
            .try_restore(token.child_visits)
            .expect("restore: token minted by this container's own mark");
        self.child_counts
            .try_restore(token.child_counts)
            .expect("restore: token minted by this container's own mark");
        self.value
            .try_restore(token.value)
            .expect("restore: token minted by this container's own mark");
        self.child_or_stats
            .try_restore(token.child_or_stats)
            .expect("restore: token minted by this container's own mark");
        self.child_spans
            .try_restore(token.child_spans)
            .expect("restore: token minted by this container's own mark");
        self.commutative
            .try_restore(token.commutative)
            .expect("restore: token minted by this container's own mark");
        self.op
            .try_restore(token.op)
            .expect("restore: token minted by this container's own mark");
        self.lb
            .try_restore(token.lb)
            .expect("restore: token minted by this container's own mark");
        self.parent_slot
            .try_restore(token.parent_slot)
            .expect("restore: token minted by this container's own mark");
        self.parent
            .try_restore(token.parent)
            .expect("restore: token minted by this container's own mark");
    }
}

/// MCGS state composed entirely from standard semi-persistent containers.
pub(crate) struct McgsState<A: AuIds = AuIds31, O: DenseId = crate::id::OpId> {
    or_stats: OrStatsArena<A, O>,
    and_stats: AndStatsArena<A, O>,
    /// Session-level exact memo (`McgsConfig::session_exact_memo`):
    /// clean solves shared by every hybrid exact call in the session; rolls
    /// back with the state's token.
    exact_memo: super::exact_memo::ExactMemo<A::Term, A::Class, A::Index>,
    /// `A::Or` -> its statistics node. Keyed by an id whose `Index` is `A::Index`, so
    /// the hash index stores positions in that word rather than 8-byte `usize`.
    or_stats_map: SpMap<A::Or, A::OrStats, A::Index>,
    /// What the hybrid trigger did (`McgsConfig::hybrid_exact`). Diagnostics,
    /// not search state: nothing reads them back, so they sit outside the
    /// semi-persistent arenas and `mark`/`restore` do not touch them.
    hybrid: HybridStats,
}

/// Token for restoring `McgsState`. It bundles only arena and map tokens.
#[derive(Clone, Copy, Debug)]
pub(crate) struct McgsToken {
    or_stats: OrStatsToken,
    and_stats: AndStatsToken,
    or_stats_map: MapToken,
    exact_memo: super::exact_memo::ExactMemoToken,
}

impl<A: AuIds, O: DenseId> McgsState<A, O> {
    pub(crate) fn new() -> Self {
        Self {
            or_stats: OrStatsArena::new(),
            and_stats: AndStatsArena::new(),
            or_stats_map: SpMap::new(),
            exact_memo: super::exact_memo::ExactMemo::new(),
            hybrid: HybridStats::default(),
        }
    }

    /// What the hybrid trigger did, cumulative over every run on this state.
    pub(crate) fn hybrid_stats(&self) -> HybridStats {
        self.hybrid
    }

    /// Shared contextual-Exact memo used by side-mode warm Exact and hybrid
    /// calls. Pair-context solves deliberately do not consume it until the
    /// memo's support proof records ordered-pair correlations.
    pub(crate) fn exact_memo_mut(
        &mut self,
    ) -> &mut super::exact_memo::ExactMemo<A::Term, A::Class, A::Index> {
        &mut self.exact_memo
    }

    pub(crate) fn mark(&mut self) -> McgsToken {
        McgsToken {
            or_stats: self.or_stats.mark(),
            and_stats: self.and_stats.mark(),
            or_stats_map: self
                .or_stats_map
                .try_mark(ShrinkPolicy::Never)
                .expect("mark: depth bounded by the search driver"),
            exact_memo: self.exact_memo.mark(),
        }
    }

    pub(crate) fn is_valid_token(&self, token: &McgsToken) -> bool {
        self.or_stats.is_valid_token(&token.or_stats)
            && self.and_stats.is_valid_token(&token.and_stats)
            && self.or_stats_map.is_valid_token(&token.or_stats_map)
            && self.exact_memo.is_valid_token(&token.exact_memo)
    }

    pub(crate) fn restore(&mut self, token: McgsToken) {
        assert!(
            self.is_valid_token(&token),
            "McgsState: token is invalid (foreign or abandoned)"
        );
        self.exact_memo.restore(token.exact_memo);
        self.or_stats_map
            .try_restore(token.or_stats_map)
            .expect("restore: token minted by this container's own mark");
        self.and_stats.restore(token.and_stats);
        self.or_stats.restore(token.or_stats);
    }

    #[inline]
    fn or_stat(&self, id: A::OrStats) -> OrStatsRef<'_, A::AndStats> {
        self.or_stats.get(id)
    }

    #[inline]
    fn and_stat(&self, id: A::AndStats) -> AndStatsRef<'_, A::OrStats, O, A::AndChildStat> {
        self.and_stats.get(id)
    }

    #[inline]
    fn or_id(&self, id: A::OrStats) -> A::Or {
        self.or_stats.or_id(id)
    }

    fn push_or_stat(
        &mut self,
        or_id: A::Or,
        data: OrStatsData<A::AndStats>,
        descriptors: Vec<TransportActionDesc<O, A::Class>>,
    ) -> A::OrStats {
        let id = self.or_stats.push(or_id, data, descriptors);
        self.or_stats_map
            .try_insert(or_id, id)
            .expect("AU arena sized by its index word");
        id
    }

    /// Push one AND-statistics node. With `track_closed` (the `closed_bit`
    /// flag), also register the reverse edge from every child position back to
    /// this node and discount the children that are already closed, so the
    /// node's open-child count is exact the moment it exists.
    fn push_and_stat(
        &mut self,
        data: AndStatsData<A::OrStats, O>,
        track_closed: bool,
    ) -> A::AndStats {
        let id = self.and_stats.push(data);
        if track_closed {
            // Read the children back from the arena one position at a time:
            // holding a slice would borrow the AND arena across the
            // `close_child` writes, and cloning the child vector would put an
            // allocation back on the expansion path removed one allocation.
            for pos in 0..self.and_stats.child_span(id).len_usize() {
                let child = self.and_stats.child_or(self.and_stats.child_id(id, pos));
                self.or_stats.push_parent(child, id);
                if self.or_stats.closed(child) {
                    self.and_stats.close_child(id);
                }
            }
        }
        id
    }

    #[inline]
    fn or_closed(&self, id: A::OrStats) -> bool {
        self.or_stats.closed(id)
    }

    #[inline]
    fn and_closed(&self, id: A::AndStats) -> bool {
        self.and_stats.closed(id)
    }

    fn set_or_initial_value(&mut self, id: A::OrStats, value: f64) {
        self.or_stats.set_initial_value(id, value);
    }

    fn set_or_value(&mut self, id: A::OrStats, value: f64) {
        self.or_stats.set_value(id, value);
    }

    fn bump_or_edge_visit(&mut self, id: A::OrStats, action: usize) {
        self.or_stats.bump_edge_visit(id, action);
    }

    fn set_or_edge_and(&mut self, id: A::OrStats, action: usize, value: Option<A::AndStats>) {
        self.or_stats.set_edge_and(id, action, value);
    }

    fn or_first_unrealized(&self, id: A::OrStats) -> usize {
        self.or_stats.first_unrealized(id)
    }

    fn advance_or_first_unrealized(&mut self, id: A::OrStats) {
        self.or_stats.advance_first_unrealized(id);
    }

    fn set_and_value(&mut self, id: A::AndStats, value: f64) {
        self.and_stats.set_value(id, value);
    }

    fn set_and_child_count(&mut self, child: A::AndChildStat, value: u64) {
        self.and_stats.set_child_count(child, value);
    }

    fn bump_and_child_visit(&mut self, child: A::AndChildStat) {
        self.and_stats.bump_child_visit(child);
    }

    fn bump_and_round_robin(&mut self, id: A::AndStats) {
        self.and_stats.bump_round_robin(id);
    }
}

/// Run MCGS from a root class pair, returning the best anti-unifier found.
///
/// Errors with `AuError::NoFiniteRepresentative` if either root (or any class
/// reachable from one) has no admissible finite member (§4.1).
pub fn run_mcgs<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l_root: ClassOf<Cfg>,
    r_root: ClassOf<Cfg>,
    config: &McgsConfig,
) -> Result<
    (
        <Cfg::Au as AuIds>::Term,
        TermPool<Cfg::O, Cfg::V, Cfg::Au>,
        super::session::Completion,
        HybridStats,
    ),
    super::AuError,
>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut space: SearchSpace<Cfg::Au> = SearchSpace::new(config.cycle_mode);
    let mut pool = TermPool::new();
    // MCGS skips AC/ACI matrix materialization; those operators use transport
    // AND-nodes instead (zero matrix enumeration, same as exact).
    let mut action_cache: ActionCache<Cfg::O, Cfg::Au, Cfg::M> =
        ActionCache::without_ac_actions(usize::MAX);
    let mut results: BestResults<Cfg::Au> = BestResults::new();
    let mut state: McgsState<Cfg::Au, Cfg::O> = McgsState::new();
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
    Ok((best, pool, completion, state.hybrid_stats()))
}

/// Session-based MCGS: runs on caller-owned layers so a `SearchSession` can
/// mark/restore the entire search state (space, pool, results, cache, stats)
/// across invocations.
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_mcgs_in<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    action_cache: &mut ActionCache<Cfg::O, Cfg::Au, Cfg::M>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    l_root: ClassOf<Cfg>,
    r_root: ClassOf<Cfg>,
    config: &McgsConfig,
) -> Result<(<Cfg::Au as AuIds>::Term, super::session::Completion), super::AuError>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    snap.validate_finite_from(l_root)?;
    snap.validate_finite_from(r_root)?;
    assert!(
        !config.live_incumbent_pruning || config.closed_bit,
        "live_incumbent_pruning requires closed_bit: exclusion accounting \
         lives in the closure machinery"
    );
    assert!(
        !config.rollout_hybrid || config.hybrid_exact,
        "rollout_hybrid requires hybrid_exact: it is the same trigger, fired \
         from the rollout path"
    );
    assert!(
        !config.session_exact_memo || config.hybrid_exact,
        "session_exact_memo requires hybrid_exact: only hybrid calls read or \
         write the memo"
    );
    assert!(
        !config.interval_bounds || config.live_incumbent_pruning,
        "interval_bounds requires live_incumbent_pruning: the intervals feed \
         its exclusion test and reuse its closure accounting"
    );

    let (empty_l, empty_r) = space.empty_contexts();
    let l_best = snap.best_size(l_root);
    let r_best = snap.best_size(r_root);
    let (root_or, _) =
        space.get_or_insert_or_node(l_root, r_root, empty_l, empty_r, l_best, r_best);

    // Eagerly publish the shared terminal generalize action as a projection-valid
    // incumbent. The mandatory structural rollout below may immediately improve it.
    let seed = evaluate_generalize_action(snap, pool, l_root, r_root);
    results.ensure_capacity(root_or);
    results.offer(root_or, seed, pool.quality(seed));

    let root_idx = ensure_or_stats(
        snap,
        space,
        pool,
        action_cache,
        results,
        state,
        root_or,
        config,
    );

    let root_settled =
        state.or_stat(root_idx).terminal || (config.closed_bit && state.or_closed(root_idx));
    if !root_settled {
        // First estimate U(root) from the initial rollout; its term is also a
        // valid result and is offered (§3.3.2).
        let rollout = initial_rollout(
            snap,
            space,
            pool,
            action_cache,
            results,
            state,
            root_or,
            config,
        );
        results.offer(root_or, rollout, pool.quality(rollout));
        let sz = pool.size(rollout) as f64;
        state.set_or_initial_value(root_idx, sz);
        state.set_or_value(root_idx, sz);
        state.or_stats.set_rolled(root_idx);

        for _ in 0..config.playouts {
            // Nothing is left to realize once the root closes, so the
            // remaining budget would buy only playouts that change nothing;
            // `close_completed_dag` below is what turns the closed graph into
            // the final answer.
            if config.closed_bit && state.or_closed(root_idx) {
                break;
            }
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

    // With the closed bit the certificate is the root's bit: it is set exactly
    // when every reachable action is realized and every reachable node closed,
    // which is what `is_structurally_complete` walks the graph to decide. The
    // walk stays as the debug oracle for the equivalence.
    let complete = if config.closed_bit {
        let closed = state.or_closed(root_idx);
        debug_assert_eq!(
            closed,
            is_structurally_complete(state, root_idx),
            "the root's closed bit disagrees with the structural certificate"
        );
        closed
    } else {
        is_structurally_complete(state, root_idx)
    };
    let completion = if complete {
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
fn or_postorder<A: AuIds, O: DenseId>(
    state: &McgsState<A, O>,
    root_idx: A::OrStats,
) -> Vec<A::OrStats> {
    // One node's flattened child OR list (every expanded AND-node's children,
    // in edge then child order). Computed once per frame, at push time: a
    // fully expanded node with e edges of arity k has e*k children and its
    // frame stays on the stack for e*k cursor steps, so recollecting the list
    // at every step is quadratic in the fan-out. On the anytime pilot's ac
    // m64c16 root (4096 transport edges x 289 cells) that recollection copies
    // ~1.4e12 ids inside `close_completed_dag`, a multi-minute stall at the
    // first budget that
    // completes expansion (playouts = members^2 = 4096); computed once, the
    // same closure finishes in under a second. Pinned by
    // `or_postorder_is_linear_in_the_expanded_fan_out`.
    let children_of = |or_idx: A::OrStats| -> Vec<A::OrStats> {
        state
            .or_stat(or_idx)
            .edge_and
            .iter()
            .flatten()
            .flat_map(|&a| state.and_stat(a).child_or_stats.iter().copied())
            .collect()
    };

    let mut postorder: Vec<A::OrStats> = Vec::new();
    let mut mark: Vec<u8> = vec![0; state.or_stats.len().as_usize()]; // 0 unseen, 1 active, 2 done
    // Frame: (or id, children computed once, child cursor).
    let mut stack: Vec<(A::OrStats, Vec<A::OrStats>, usize)> =
        vec![(root_idx, children_of(root_idx), 0)];
    mark[root_idx.to_usize()] = 1;
    loop {
        let next = {
            let Some((_, children, cursor)) = stack.last_mut() else {
                break;
            };
            if *cursor < children.len() {
                let child = children[*cursor];
                *cursor += 1;
                Some(child)
            } else {
                None
            }
        };
        match next {
            // Unseen child: descend. Active (1) children are back edges and
            // done (2) children are shared; neither is revisited.
            Some(child) => {
                if mark[child.to_usize()] == 0 {
                    mark[child.to_usize()] = 1;
                    let child_children = children_of(child);
                    stack.push((child, child_children, 0));
                }
            }
            None => {
                let (done, _, _) = stack.pop().expect("postorder stack cannot be empty");
                mark[done.to_usize()] = 2;
                postorder.push(done);
            }
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
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    root_idx: <Cfg::Au as AuIds>::OrStats,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    for &or_idx in &or_postorder(state, root_idx) {
        let edges: Vec<<Cfg::Au as AuIds>::AndStats> = state
            .or_stat(or_idx)
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
fn close_values<A: AuIds, O: DenseId>(state: &mut McgsState<A, O>, root_idx: A::OrStats) {
    for &or_idx in &or_postorder(state, root_idx) {
        let edges: Vec<A::AndStats> = state
            .or_stat(or_idx)
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
///
/// Iterative (explicit frame stack) with the tri-state visited protocol of the
/// recursive definition: 0 = unseen, 1 = active (on the current path; a re-entry
/// is a cycle and conservatively rejects), 2 = memoized complete. The first
/// `false` anywhere (unrealized edge, or active-cycle hit) short-circuits the
/// whole certificate, exactly like the recursive `all(..)` chains.
fn is_structurally_complete<A: AuIds, O: DenseId>(
    state: &McgsState<A, O>,
    or_idx: A::OrStats,
) -> bool {
    let mut visited: Vec<u8> = vec![0; state.or_stats.len().as_usize()];
    // Frame: an OR node whose flattened child OR list (every expanded
    // AND-node's children, in edge then child order) is being verified.
    let mut stack: Vec<(A::OrStats, Vec<A::OrStats>, usize)> = Vec::new();
    let mut pending = Some(or_idx);
    loop {
        if let Some(current) = pending.take() {
            match visited[current.to_usize()] {
                2 => {}            // memoized: already verified complete
                1 => return false, // active: cycle, conservatively reject
                _ => {
                    visited[current.to_usize()] = 1; // mark active
                    let stats = state.or_stat(current);
                    if stats.terminal {
                        visited[current.to_usize()] = 2;
                    } else {
                        // Every legal action must have been expanded or
                        // excluded (live-incumbent pruning: an excluded arm
                        // is proven non-optimal, so the certificate does not
                        // need its subgraph).
                        if stats
                            .edge_and
                            .iter()
                            .enumerate()
                            .any(|(a, e)| e.is_none() && !stats.edge_excluded[a])
                        {
                            return false;
                        }
                        // Every non-excluded expanded AND-node's children
                        // must be complete.
                        let children: Vec<A::OrStats> = stats
                            .edge_and
                            .iter()
                            .enumerate()
                            .filter(|&(a, _)| !stats.edge_excluded[a])
                            .filter_map(|(_, e)| *e)
                            .flat_map(|a| state.and_stat(a).child_or_stats.iter().copied())
                            .collect();
                        stack.push((current, children, 0));
                    }
                }
            }
        }
        loop {
            let Some((_, children, cursor)) = stack.last_mut() else {
                return true;
            };
            if *cursor < children.len() {
                let child = children[*cursor];
                *cursor += 1;
                pending = Some(child);
                break;
            }
            let (done, _, _) = stack.pop().expect("completion stack cannot be empty");
            visited[done.to_usize()] = 2; // memoize
        }
    }
}

/// Close `and_idx` if its last open child just closed, and report the OR node
/// that closes with it, if any.
///
/// The order inside is what makes a closed node's stored result exact: the
/// node's value is recomputed and its composition offered to its parent OR
/// *before* that parent's open-edge count can reach zero, so when an OR node's
/// bit is set, its incumbent already accounts for every one of its actions'
/// final compositions (each child's own result being final by induction).
fn try_close_and<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    and_idx: <Cfg::Au as AuIds>::AndStats,
    config: &McgsConfig,
) -> Option<<Cfg::Au as AuIds>::OrStats>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if state.and_closed(and_idx) || state.and_stats.open_children(and_idx) != 0 {
        return None;
    }
    state.and_stats.set_closed(and_idx);
    recompute_and_value(state, and_idx);
    if config.interval_bounds {
        // The action is resolved, so its children's floors are final and its
        // own floor is now exact: publish it before the parent decides.
        refresh_and_interval(state, and_idx);
    }
    compose_and_offer(snap, pool, results, state, and_idx);

    let parent = state.and_stat(and_idx).parent;
    let slot = state.and_stats.parent_slot(and_idx);
    if state.or_closed(parent) {
        // Reachable only under live-incumbent pruning: the parent closed
        // through exclusions while this action's subgraph was still open,
        // which needs this very arm to have been excluded (an open,
        // non-excluded arm keeps its parent's open-edge count positive).
        debug_assert!(
            config.live_incumbent_pruning && state.or_stats.edge_excluded(parent, slot),
            "an OR node closed before one of its actions did"
        );
        return None;
    }
    if config.live_incumbent_pruning && state.or_stats.edge_excluded(parent, slot) {
        // The slot was accounted when the arm was excluded; do not decrement
        // again. The composition above may still have tightened the parent's
        // incumbent, so sweep before deciding whether the parent closes.
        sweep_arms(results, state, parent, config.interval_bounds);
    } else {
        state.or_stats.close_edge(parent);
        if config.live_incumbent_pruning {
            // The composition above may have tightened the parent's
            // incumbent; excluded arms count as resolved right away.
            sweep_arms(results, state, parent, config.interval_bounds);
        }
    }
    if state.or_stats.open_edges(parent) == 0 {
        state.or_stats.set_closed(parent);
        recompute_or_value(state, parent);
        // Write the proof through to the results table, where it outlives this
        // run's statistics: closure asserts exactly what `mark_exact` means —
        // the stored result is the optimum of this node's action space under
        // this cycle mode (the same-state exact-subproblem argument) — and
        // `ensure_or_stats` makes a node with the flag terminal at creation, so
        // a later run on the same session inherits the proof instead of
        // re-realizing the subgraph. The flag is write-once and rolls back with
        // the table's own token, so mark/restore needs nothing here.
        results.mark_exact(state.or_id(parent));
        return Some(parent);
    }
    None
}

/// The closure walk proper: drain `pending` (OR nodes that just closed),
/// handing each closure to every parent AND through the reverse-edge lists.
/// `settle_closure` seeds it from a realized action; live-incumbent pruning
/// seeds it from sweep-closed nodes as well.
fn propagate_or_closures<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    mut pending: Vec<<Cfg::Au as AuIds>::OrStats>,
    config: &McgsConfig,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    while let Some(or_idx) = pending.pop() {
        let mut entry = state.or_stats.parent_head(or_idx);
        while let Some(current) = entry {
            let (and_idx, next) = state.or_stats.parent_entry(current);
            entry = next;
            state.and_stats.close_child(and_idx);
            if let Some(parent) = try_close_and(snap, pool, results, state, and_idx, config) {
                pending.push(parent);
            }
        }
    }
}

/// One feasible AC/ACI transport action at an OR node: a representation pair
/// with its cycle-blocked cell mask. Only pairs admitting a feasible flow
/// (zero-cost transport with blocked cells Forbidden) become actions; a pair
/// with legal cells can still be Hall-infeasible (a blocked row with positive
/// supply), and such pairs must not consume an action slot.
pub(crate) struct TransportActionDesc<O, C> {
    op: O,
    pub(crate) left: ac_repr::Monomial<C>,
    pub(crate) right: ac_repr::Monomial<C>,
    /// Flat row-major r*c mask: true = cell is not cycle-blocked.
    pub(crate) legal_cells: Vec<bool>,
    /// `left`/`right` multiplicities already narrowed to the transport solver's
    /// width. Narrowing happens once, in the feasibility gate below: a pair
    /// whose multiplicities the solver cannot represent never becomes a
    /// descriptor, so every consumer of these vectors is free of a fallible
    /// conversion and cannot disagree with the gate about what was solved.
    row_supply: Vec<u32>,
    col_demand: Vec<u32>,
}

/// Enumerate the feasible transport actions for `(l, r)` at `or_id`. Single
/// source of truth for action counting, expansion indexing, and rollout.
pub(crate) fn transport_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &SearchSpace<Cfg::Au>,
    or_id: <Cfg::Au as AuIds>::Or,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
) -> Vec<TransportActionDesc<Cfg::O, ClassOf<Cfg>>>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut out = Vec::new();
    for op in ac_repr::common_ac_ops(snap, l, r) {
        // MCGS ignores the padding annotation: its playout loop has no
        // memo-key rank requirement, so padded identities need no context
        // extension here (the exact solver is the consumer that does).
        for (lm, rm, _pad_identity) in ac_repr::representation_pairs(snap, l, r, op) {
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
            let supply: Vec<u64> = lm.iter().map(|(_, k)| *k).collect();
            let demand: Vec<u64> = rm.iter().map(|(_, k)| *k).collect();
            // A pair whose multiplicities the solver cannot represent is
            // reported infeasible, the same signal an unsolvable pair gives: it
            // consumes no action slot.
            let Some(problem) = TransportProblem::narrowed(&supply, &demand, cost) else {
                continue;
            };
            if solve_transport(&problem).is_some() {
                out.push(TransportActionDesc {
                    op,
                    left: lm,
                    right: rm,
                    legal_cells,
                    // Moved out of the solved problem, so the descriptor carries
                    // the very vectors the feasibility check ran on.
                    row_supply: problem.row_supply,
                    col_demand: problem.col_demand,
                });
            }
        }
    }
    out
}

/// Dominance pruning: true when the
/// structural action's projection lower bound — 1 for the operator plus
/// `count * lb_pair(pair)` per child pair — strictly exceeds the node's
/// generalize value `gen_size`. The generalize value is the exact value of an
/// always-available alternative, so a dominated action loses under every
/// completion and can never be optimal at the node. Size-only and strict: an
/// equal size can still win on variant mass. `u64` saturating accumulation
/// keeps the total a lower bound, and a saturated total still strictly
/// exceeds every `u32` generalize value, which discards the action — sound,
/// because the true value is at least the exact sum (the same argument as
/// `exact::action_size_bound`).
fn structural_action_dominated<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    action: &Action<Cfg::O, Cfg::Au, Cfg::M>,
    gen_size: u32,
) -> bool
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    structural_action_bound(snap, action) > u64::from(gen_size)
}

/// The structural action's admissible size lower bound: 1 for the operator
/// plus `count * lb_pair(pair)` per child pair, saturating (the saturated
/// value stays a lower bound; see [`structural_action_dominated`]). Shared by
/// the creation-time dominance check and live-incumbent pruning's cached bound.
fn structural_action_bound<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    action: &Action<Cfg::O, Cfg::Au, Cfg::M>,
) -> u64
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut bound: u64 = 1;
    for pair in &action.pairs {
        bound = bound.saturating_add(
            u64::from(lb_pair(snap, pair.left, pair.right).0).saturating_mul(pair.count.to_u64()),
        );
    }
    bound
}

/// Interval maintenance (`McgsConfig::interval_bounds`): recompute
/// one AND node's floor from its children's floors, write it into the
/// parent's slot bound, and lift the parent's own floor.
///
/// `L(and) = 1 + Σ count · L(child)` for a fixed action; for a transport
/// action the same sum over the cells the current flow selects, which is a
/// valid floor because a flow's cost dominates the sum of its cells' floors.
/// Every write is monotone (`set_*` keeps the maximum), so a bound never
/// loosens and a stale walk only weakens pruning, never breaks it.
fn refresh_and_interval<A: AuIds, O: DenseId>(state: &mut McgsState<A, O>, and_idx: A::AndStats) {
    let (parent, slot) = {
        let and = state.and_stat(and_idx);
        let mut lb: u64 = 1;
        for (i, &child) in and.child_or_stats.iter().enumerate() {
            lb = lb.saturating_add(
                u64::from(state.or_stats.node_lb(child)).saturating_mul(and.child_counts[i]),
            );
        }
        let lb = u32::try_from(lb).unwrap_or(u32::MAX);
        (and.parent, lb)
    };
    state.and_stats.set_lb(and_idx, slot);
    // Read back the monotone maximum rather than this pass's value: an
    // earlier refresh (or the closure walk) may already have proved more.
    let lb = state.and_stats.lb(and_idx);
    let slot = state.and_stats.parent_slot(and_idx);
    state.or_stats.set_edge_lb(parent, slot, lb);

    // The node's own floor is the minimum over arms that are still live:
    // an excluded arm is proven non-optimal, so it must not hold the floor
    // down, and an unrealized arm contributes its static creation bound.
    let n = state.or_stats.edge_span(parent).len_usize();
    let mut floor = u32::MAX;
    for a in 0..n {
        if state.or_stats.edge_excluded(parent, a) {
            continue;
        }
        floor = floor.min(state.or_stats.edge_lb(parent, a));
    }
    if floor != u32::MAX {
        state.or_stats.set_node_lb(parent, floor);
    }
}

/// Live-incumbent arm pruning (`McgsConfig::live_incumbent_pruning`): exclude
/// every arm whose cached admissible bound strictly exceeds the current
/// incumbent and account each newly excluded slot as resolved. The caller
/// closes the node through the normal closure path after checking
/// `open_edges`.
fn sweep_arms<A: AuIds, O: DenseId>(
    results: &BestResults<A>,
    state: &mut McgsState<A, O>,
    or_idx: A::OrStats,
    intervals: bool,
) {
    debug_assert!(!state.or_closed(or_idx), "sweeping a closed node");
    let or_id = state.or_id(or_idx);
    let best = results.best_size(or_id);
    let n = state.or_stats.edge_span(or_idx).len_usize();
    for a in 0..n {
        if state.or_stats.edge_excluded(or_idx, a) {
            continue;
        }
        // With intervals the arm's DYNAMIC floor decides; it starts at the
        // static creation bound and only rises, so this test matches the
        // live-incumbent test where nothing has tightened and is strictly
        // stronger where it has.
        let bound = if intervals {
            state.or_stats.edge_lb(or_idx, a)
        } else {
            state.or_stats.edge_bound(or_idx, a)
        };
        if bound <= best {
            continue;
        }
        if let Some(and_idx) = state.or_stats.edge_and_slot(or_idx, a)
            && state.and_closed(and_idx)
        {
            continue;
        }
        state.or_stats.set_edge_excluded(or_idx, a);
        state.or_stats.close_edge(or_idx);
    }
}

/// The hybrid trigger: if this node's
/// subproblem is at or below `config.hybrid_threshold` reachable class pairs,
/// delegate it to contextual Exact and record completion when earned.
///
/// The exact run is entered at this node's own state: the same `(l, r)`, the
/// same side or pair context, and the same cycle mode. A completed call therefore
/// carries the implementation's exactness assertion for *this* node, which is
/// what `mark_exact` records (see the module documentation). The term is offered
/// unconditionally, because term validity does not
/// depend on contexts, and only a completed run is marked: node-budget
/// exhaustion yields a feasible incumbent with no proof attached.
///
/// The two thresholds are admission estimates, not work bounds. Only
/// `config.hybrid_node_budget` hard-bounds node entries in one call.
#[allow(clippy::too_many_arguments)]
fn solve_hybrid<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    or_id: <Cfg::Au as AuIds>::Or,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
    num_actions: usize,
    config: &McgsConfig,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    // Two-part admission: the rectangle and entry action count are
    // complementary workload estimates, not hard bounds.
    if reachable_pairs(snap, l, r) > config.hybrid_threshold
        || num_actions as u64 > config.hybrid_action_threshold
    {
        return;
    }
    let context = space.cycle_context(or_id);

    let start = std::time::Instant::now();
    let run = super::exact::run_exact_at(
        snap,
        pool,
        l,
        r,
        &context,
        space.cycle_mode,
        None,
        // Projection pruning and context subsumption make a subproblem call
        // cheap, and both are tested to
        // leave the optimum unchanged (au_differential.rs).
        true,
        true,
        config.session_exact_memo.then_some(&mut state.exact_memo),
        config.hybrid_node_budget,
        None,
    );
    state.hybrid.calls += 1;
    state.hybrid.time += start.elapsed();

    results.offer(or_id, run.term, pool.quality(run.term));
    if run.complete {
        state.hybrid.proved += 1;
        results.mark_exact(or_id);
    }
}

/// Look up or create the statistics struct for an OR node. Fresh structs know
/// their action count (cycle-filtered; additionally dominance-filtered when
/// `config.dominance_pruning` is set, see [`structural_action_dominated`]),
/// terminal flag, and normalization sizes; values start at the node's stored
/// best-result size (terminal) or infinity (awaiting a rollout estimate).
///
/// With dominance pruning on, a node whose every action is dropped has
/// `num_actions == 0` and closes through the existing terminal condition
/// below, at its stored best result — at worst the generalize value, whose
/// term every creation site offers before calling here (the root seed in
/// `run_mcgs_in`, `child_seed` in `expand_action`, and the rollout offers) —
/// which is then exact, because every alternative was proven non-optimal.
///
/// With `config.hybrid_exact` on, a node whose subproblem is small enough is
/// solved outright by [`solve_hybrid`] and reaches the same terminal condition
/// through `results.is_exact`.
#[allow(clippy::too_many_arguments)]
fn ensure_or_stats<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    action_cache: &mut ActionCache<Cfg::O, Cfg::Au, Cfg::M>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    or_id: <Cfg::Au as AuIds>::Or,
    config: &McgsConfig,
) -> <Cfg::Au as AuIds>::OrStats
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if let Some(log_idx) = state.or_stats_map.id_of(&or_id) {
        return *state.or_stats_map.get_val(log_idx);
    }

    let dominance = config.dominance_pruning;
    let l = *space.or_arena.left.get(or_id.to_index());
    let r = *space.or_arena.right.get(or_id.to_index());
    let l_best = *space.or_arena.left_best_size.get(or_id.to_index()) as f64;
    let r_best = *space.or_arena.right_best_size.get(or_id.to_index()) as f64;

    let live_prune = config.live_incumbent_pruning;
    let mut edge_bounds: Vec<u32> = Vec::new();
    let (num_actions, descs) = if l == r {
        (0, Vec::new())
    } else {
        let gen_size = static_generalize_quality(snap, l, r).0;
        generate_actions(snap, action_cache, l, r);
        let actions = action_cache.get(l, r).unwrap();
        let mut count = 0;
        for action in actions {
            let blocked = action
                .pairs
                .iter()
                .any(|p| space.is_cycle_blocked(or_id, p.left, p.right));
            if blocked {
                continue;
            }
            if dominance || live_prune {
                let bound = structural_action_bound(snap, action);
                if dominance && bound > u64::from(gen_size) {
                    continue;
                }
                count += 1;
                if live_prune {
                    edge_bounds.push(u32::try_from(bound).unwrap_or(u32::MAX));
                }
            } else {
                count += 1;
            }
        }
        // One edge per feasible AC/ACI transport action (flow-verified).
        // Descriptors are computed once here and cached on the stats entry;
        // expansion reads the cache instead of re-solving feasibility.
        let mut descs = transport_actions(snap, space, or_id, l, r);
        if dominance {
            // Same dominance screen for transport actions, on the shared
            // lb-cost flow bound. `None` (infeasible) cannot occur here —
            // every descriptor passed the zero-cost feasibility gate on the
            // same mask and supplies — but dropping it would be sound too.
            descs.retain(|desc| {
                let n_cols = desc.right.len();
                match transport_pair_lb(snap, &desc.left, &desc.right, |i, j| {
                    desc.legal_cells[i * n_cols + j]
                }) {
                    None => false,
                    Some(bound) => bound <= u128::from(gen_size),
                }
            });
        }
        if live_prune {
            // The flow bound per surviving descriptor, on the same mask the
            // real solve uses; `None` cannot occur (every descriptor passed
            // the zero-cost feasibility gate), and a saturated bound clamps
            // to `u32::MAX`, which only ever excludes.
            for desc in &descs {
                let n_cols = desc.right.len();
                let bound = transport_pair_lb(snap, &desc.left, &desc.right, |i, j| {
                    desc.legal_cells[i * n_cols + j]
                })
                .unwrap_or(u128::MAX);
                edge_bounds.push(u32::try_from(bound).unwrap_or(u32::MAX));
            }
        }
        count += descs.len();
        (count, descs)
    };
    if !live_prune {
        edge_bounds = vec![0; num_actions];
    }
    debug_assert_eq!(edge_bounds.len(), num_actions);

    // Hybrid exact (hybrid exact solving): a subproblem small enough to prove outright
    // is proved here rather than enumerated by playouts. Running before the
    // terminal test is what makes the proof land: `results.is_exact` is
    // already a terminal condition, so a proved node needs no separate flag.
    if config.hybrid_exact && l != r && num_actions > 0 && !results.is_exact(or_id) {
        solve_hybrid(
            snap,
            space,
            pool,
            results,
            state,
            or_id,
            l,
            r,
            num_actions,
            config,
        );
    }

    let terminal = l == r || num_actions == 0 || results.is_exact(or_id);
    // Terminal nodes take their stored best result as their permanent value.
    let value = if terminal {
        results.best_size(or_id) as f64
    } else {
        f64::INFINITY
    };

    let idx = state.push_or_stat(
        or_id,
        OrStatsData {
            initial_value: value,
            value,
            min_size: l_best.min(r_best),
            max_size: l_best.max(r_best),
            terminal,
            edge_visits: vec![0; num_actions],
            edge_and: vec![None; num_actions],
            edge_bounds,
        },
        descs,
    );
    // Creation-time sweep: arms the live incumbent already beats are
    // excluded before the first playout touches the node; a node whose every
    // arm dies here closes at its stored best result, which is then exact by
    // the same argument as the all-dominated case.
    if live_prune && !terminal {
        sweep_arms(results, state, idx, config.interval_bounds);
        if state.or_stats.open_edges(idx) == 0 {
            let sz = results.best_size(or_id) as f64;
            state.or_stats.set_closed(idx);
            state.set_or_initial_value(idx, sz);
            state.set_or_value(idx, sz);
            state.or_stats.set_rolled(idx);
            state.or_stats.set_node_lb(idx, sz as u32);
            results.mark_exact(or_id);
        }
    }
    idx
}

/// One playout (§3.3): descend by UCT at OR nodes and the configured AND
/// selector (§3.3.5), expand the first
/// unrealized action met, rollout fresh children, then backpropagate along the
/// traversed path (children before parents), recomputing values idempotently
/// and offering composed results.
#[allow(clippy::too_many_arguments)]
fn playout<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    action_cache: &mut ActionCache<Cfg::O, Cfg::Au, Cfg::M>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    root_idx: <Cfg::Au as AuIds>::OrStats,
    config: &McgsConfig,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    // The traversed path: AND stats ids, root-side first.
    let mut path: Vec<<Cfg::Au as AuIds>::AndStats> = Vec::new();
    let mut current = root_idx;
    // The action this playout realized, if any. Under `closed_bit` there is
    // always one: selection enters only open nodes and picks only open
    // children, and an open node either has an unrealized slot or an open
    // action leading to an open node, so the descent cannot dead-end. A
    // playout that expands nothing means a closure that was not propagated.
    let mut realized: Option<<Cfg::Au as AuIds>::AndStats> = None;

    loop {
        debug_assert!(
            !config.closed_bit || !state.or_closed(current),
            "playout descended into a closed node"
        );
        if state.or_stat(current).terminal {
            break;
        }

        // Deferred rollout (static child seeding): a seeded-only node runs its initial
        // rollout on first selection, exactly the estimate it would have
        // carried from birth without the flag.
        if config.static_child_seed && !state.or_stats.rolled(current) {
            state.or_stats.set_rolled(current);
            let current_or = state.or_id(current);
            let rollout = initial_rollout(
                snap,
                space,
                pool,
                action_cache,
                results,
                state,
                current_or,
                config,
            );
            results.ensure_capacity(current_or);
            results.offer(current_or, rollout, pool.quality(rollout));
            let sz = pool.size(rollout) as f64;
            state.set_or_initial_value(current, sz);
            state.set_or_value(current, sz);
        }

        // First unhandled action, in ascending action order (UCT expansion
        // §3.3.4). Handled slots (realized, or excluded under live-incumbent
        // pruning) form a prefix: expansion is the only realizer and it fills
        // in index order, and the loop below walks the cursor past excluded
        // slots, so the per-node cursor replaces the linear scan.
        let mut cursor = state.or_first_unrealized(current);
        if config.live_incumbent_pruning {
            let n_slots = state.or_stats.edge_span(current).len_usize();
            while cursor < n_slots && state.or_stats.edge_excluded(current, cursor) {
                // An excluded slot is resolved without being realized; the
                // cursor treats it as handled and moves on.
                state.advance_or_first_unrealized(current);
                cursor += 1;
            }
        }
        let unrealized = {
            let stats = state.or_stat(current);
            debug_assert_eq!(
                stats
                    .edge_and
                    .iter()
                    .enumerate()
                    .position(|(a, e)| e.is_none() && !stats.edge_excluded[a]),
                (cursor < stats.edge_and.len()).then_some(cursor),
                "first-unrealized cursor diverged from the edge scan"
            );
            (cursor < stats.edge_and.len()).then_some(cursor)
        };

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
                config,
            );
            state.set_or_edge_and(current, action_idx, Some(and_idx));
            state.advance_or_first_unrealized(current);
            path.push(and_idx);
            realized = Some(and_idx);

            // Rollout: first estimate for fresh children (§3.3.2). With
            // static child seeding (static child seeding), the estimate is the child's
            // stored best size instead (at worst the generalize seed
            // `expand_action` just offered) and the full rollout is deferred
            // to the child's first selection below.
            for pos in 0..state.and_stat(and_idx).child_or_stats.len() {
                let child_idx = state.and_stat(and_idx).child_or_stats[pos];
                if state.or_stat(child_idx).value.is_infinite() {
                    let child_or = state.or_id(child_idx);
                    if config.static_child_seed {
                        let sz = results.best_size(child_or) as f64;
                        state.set_or_initial_value(child_idx, sz);
                        state.set_or_value(child_idx, sz);
                    } else {
                        let rollout = initial_rollout(
                            snap,
                            space,
                            pool,
                            action_cache,
                            results,
                            state,
                            child_or,
                            config,
                        );
                        results.ensure_capacity(child_or);
                        results.offer(child_or, rollout, pool.quality(rollout));
                        let sz = pool.size(rollout) as f64;
                        state.set_or_initial_value(child_idx, sz);
                        state.set_or_value(child_idx, sz);
                        state.or_stats.set_rolled(child_idx);
                    }
                }
            }
            break;
        }

        // Fully expanded: score realized actions by UCT (§3.3.4), first max wins.
        let action_idx = select_uct(state, current, config);
        state.bump_or_edge_visit(current, action_idx);
        let and_idx = state.or_stat(current).edge_and[action_idx].unwrap();
        path.push(and_idx);

        // AND allocation: configured selector (§3.3.5), with its own edge
        // visit. The round-robin counter is part of the overlay state and is
        // maintained regardless of the selector in use.
        let pos = select_and_child(state, and_idx, config);
        let child = state.and_stats.child_id(and_idx, pos);
        state.bump_and_round_robin(and_idx);
        state.bump_and_child_visit(child);
        current = state.and_stats.child_or(child);
    }

    // Backpropagation (§3.3.3): deepest AND first, then rootward. Each AND
    // recomputes Q from its children, composes their best results into a
    // candidate, and offers it to its parent OR; the parent recomputes Q.
    // Under live-incumbent pruning, each composition may have tightened the
    // parent's incumbent, so the parent's arms are swept right here: this is
    // what kills every decoy on the path in the same playout that finds the
    // winner. A sweep that resolves the last open edge closes the parent.
    let mut swept_closed: Vec<<Cfg::Au as AuIds>::OrStats> = Vec::new();
    for &and_idx in path.iter().rev() {
        recompute_and_value(state, and_idx);
        if config.interval_bounds {
            // Path-only propagation, like the Q values: the floors this
            // playout discovered travel up the path it took. An off-path
            // parent keeps a staler (weaker) bound, never a wrong one.
            refresh_and_interval(state, and_idx);
        }
        compose_and_offer(snap, pool, results, state, and_idx);
        let parent = state.and_stat(and_idx).parent;
        recompute_or_value(state, parent);
        if config.live_incumbent_pruning && !state.or_closed(parent) {
            sweep_arms(results, state, parent, config.interval_bounds);
            if state.or_stats.open_edges(parent) == 0 {
                state.or_stats.set_closed(parent);
                recompute_or_value(state, parent);
                let sz = results.best_size(state.or_id(parent));
                state.or_stats.set_node_lb(parent, sz);
                results.mark_exact(state.or_id(parent));
                swept_closed.push(parent);
            }
        }
    }

    // Closure (§ the module doc's closed bit): the realized action and the
    // sweep-closed nodes are the only things that can have resolved a
    // subgraph this playout, and the walk takes the news as far up as it
    // goes.
    if config.closed_bit {
        debug_assert!(
            realized.is_some(),
            "a playout realized no action while the root was open; a closure \
             was not propagated to every parent"
        );
        let mut pending = swept_closed;
        if let Some(and_idx) = realized {
            pending.extend(try_close_and(snap, pool, results, state, and_idx, config));
        }
        propagate_or_closures(snap, pool, results, state, pending, config);
    }
}

/// UCT score (§3.3.4):
/// `score(a) = reward(Q(and_a)) + C * sqrt(sum_N) / (1 + N(n,a))`
/// evaluated in ascending action order; the first maximum wins.
///
/// All actions are normalized against the parent OR node's own (min_size, max_size)
/// (§2.5.1 property A); per-action bases can invert the size preference.
///
/// **Closed skip (`McgsConfig::closed_bit`).** An action whose AND node is
/// closed is scored by nobody: its subgraph is fully resolved, so a visit
/// there realizes nothing and changes no value. Its value still enters the
/// node's Q through `recompute_or_value` — the skip removes the arm from the
/// argmax, not from the estimate. The caller only reaches this function at an
/// open node, which by definition still has an open action.
fn select_uct<A: AuIds, O: DenseId>(
    state: &McgsState<A, O>,
    or_idx: A::OrStats,
    config: &McgsConfig,
) -> usize {
    let stats = state.or_stat(or_idx);
    let total: u64 = stats.edge_visits.iter().sum();
    let sqrt_total = (total as f64).sqrt();

    let mut best_score = f64::NEG_INFINITY;
    let mut best_action: Option<usize> = None;
    // The scored-set fallback, unchanged from "action 0" when nothing is
    // skipped: the first action that was actually scored.
    let mut first_open: Option<usize> = None;

    for (a, edge) in stats.edge_and.iter().enumerate() {
        let Some(and_idx) = *edge else {
            // Only an excluded slot can be unrealized once the expansion
            // cursor is exhausted (live-incumbent pruning).
            debug_assert!(
                config.live_incumbent_pruning && stats.edge_excluded[a],
                "select_uct requires a fully expanded node"
            );
            continue;
        };
        if config.closed_bit && state.and_closed(and_idx) {
            continue;
        }
        if config.live_incumbent_pruning && stats.edge_excluded[a] {
            // Proven non-optimal against the live incumbent: out of the
            // argmax, like a closed arm (its Q still enters the node's mean).
            continue;
        }
        first_open.get_or_insert(a);
        let and = state.and_stat(and_idx);
        let r = super::reward::reward(and.value, stats.min_size, stats.max_size, config.x_target);
        let exploration =
            config.exploration_constant * sqrt_total / (1.0 + stats.edge_visits[a] as f64);
        let score = r + exploration;
        if score > best_score {
            best_score = score;
            best_action = Some(a);
        }
    }
    debug_assert!(
        first_open.is_some() || !config.closed_bit,
        "every action of an open node is closed; a closure was not propagated"
    );
    best_action.or(first_open).unwrap_or(0)
}

/// AND-node effort allocation (§3.3.5): pick the child position that receives
/// the next unit of refinement effort, per the configured selector:
///
/// ```text
/// round_robin:  i = counter mod arity;  counter += 1
/// uct_and:      argmax_i (1 − normalize(Q(child_i))) + C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))
/// lct_and:      argmin_i (1 − normalize(Q(child_i))) − C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))
/// ```
///
/// Each child's Q is normalized against that child OR node's own
/// `(min_size, max_size)` basis (§2.5.1 property A: per-node basis). Scores
/// are evaluated in ascending child order with strict improvement, so ties
/// resolve to the smallest (scored) child index.
///
/// **Terminal-skip gate (delivered refinement, see
/// doc/future/au-associative-operators.md §5).** The value-guided selectors
/// skip children whose OR node is terminal. A terminal child can never change
/// the completion certificate and its Q is exact and immutable, so visiting
/// it refines nothing. The bare formulas do NOT starve such children
/// naturally: on a deep spine the nonterminal child's reward converges to
/// `1 − λ/best_size`, a near-tie with the terminal sibling's reward of 1, and
/// the exploration term then forces near-equal allocation (the bonus-balance
/// steady state is N_terminal ≈ N_spine), reproducing round-robin's 2^-depth
/// flux decay — pinned by `lct_and_without_terminal_skip_splits_flux_on_near_ties`.
/// Skipping terminals is admissible under §2.5.1 F because fairness exists to
/// converge child estimates, and a terminal child's estimate is already exact.
/// When every child is terminal the choice is inert (descent stops at any
/// terminal child and backpropagation is path-based); the smallest index is
/// returned.
///
/// **Closed skip (`McgsConfig::closed_bit`).** With the flag on, every
/// selector — round robin included — passes over children whose OR node is
/// closed, by the same argument one step further: a closed child's subgraph is
/// fully realized, so no visit below it can change a value, a stored result,
/// or the certificate. Terminal children are closed at birth, so the flag-on
/// skip is a superset of the terminal-skip gate.
fn select_and_child<A: AuIds, O: DenseId>(
    state: &McgsState<A, O>,
    and_idx: A::AndStats,
    config: &McgsConfig,
) -> usize {
    match config.and_selector {
        AndSelector::RoundRobin => {
            let and = state.and_stat(and_idx);
            let arity = and.child_or_stats.len();
            debug_assert!(arity > 0, "AND selection requires at least one child");
            let start = (and.round_robin as usize) % arity;
            if !config.closed_bit {
                return start;
            }
            // Closed skip, as on the value-guided selectors: rotate on to the
            // first open child. The rotation order is unchanged; only resolved
            // children are passed over.
            (0..arity)
                .map(|step| (start + step) % arity)
                .find(|&i| !state.or_closed(and.child_or_stats[i]))
                .unwrap_or(start)
        }
        AndSelector::UctAnd => select_and_child_value_guided(state, and_idx, config, 1.0, true),
        AndSelector::LctAnd => select_and_child_value_guided(state, and_idx, config, -1.0, true),
    }
}

/// Value-guided scoring core shared by `uct_and` (`sign = +1`, argmax) and
/// `lct_and` (`sign = −1`, argmin as argmax of the negated reward). The
/// exploration bonus is added in both cases:
/// `sign · reward(child) + C · sqrt(Σ_j N(n,j)) / (1 + N(n,i))`.
/// `skip_terminal` is the terminal-skip gate documented on
/// [`select_and_child`]; production always passes `true`, tests exercise
/// `false` to pin why the gate is required.
fn select_and_child_value_guided<A: AuIds, O: DenseId>(
    state: &McgsState<A, O>,
    and_idx: A::AndStats,
    config: &McgsConfig,
    sign: f64,
    skip_terminal: bool,
) -> usize {
    let and = state.and_stat(and_idx);
    debug_assert!(
        !and.child_or_stats.is_empty(),
        "AND selection requires at least one child"
    );
    let total: u64 = and.child_visits.iter().sum();
    let sqrt_total = (total as f64).sqrt();

    let mut best_score = f64::NEG_INFINITY;
    let mut best_child = None;
    for (i, &child_idx) in and.child_or_stats.iter().enumerate() {
        let child = state.or_stat(child_idx);
        if skip_terminal && child.terminal {
            continue;
        }
        // Closed skip (`McgsConfig::closed_bit`): the same argument as the
        // terminal skip, on the larger set. A closed child's subgraph is
        // resolved, so refining it changes nothing; terminal children are
        // closed too, so this subsumes the gate above when the flag is on.
        if config.closed_bit && state.or_closed(child_idx) {
            continue;
        }
        let r = super::reward::reward(child.value, child.min_size, child.max_size, config.x_target);
        let exploration =
            config.exploration_constant * sqrt_total / (1.0 + and.child_visits[i] as f64);
        let score = sign * r + exploration;
        if score > best_score {
            best_score = score;
            best_child = Some(i);
        }
    }
    // Every child terminal: the choice is inert (see the gate documentation).
    debug_assert!(
        best_child.is_some() || !config.closed_bit,
        "every child of an open AND node is closed; a closure was not propagated"
    );
    best_child.unwrap_or(0)
}

/// AND value equation (§3.3): for fixed-action AND-nodes,
/// `Q(n) = 1 + Σ_i count_i · Q(child_i)`. For transport-AND-nodes,
/// `Q(n) = 1 + min_X Σ_ij x_ij · Q(cell_ij)` where X is the transport argmin.
fn recompute_and_value<A: AuIds, O: DenseId>(state: &mut McgsState<A, O>, and_idx: A::AndStats) {
    let is_transport = !state.and_stat(and_idx).transport_rows.is_empty();
    if is_transport {
        recompute_transport_and_value(state, and_idx);
    } else {
        let and = state.and_stat(and_idx);
        let mut q = 1.0;
        for (i, &child) in and.child_or_stats.iter().enumerate() {
            // Counts above 2^53 round here. `q` is a search-ordering heuristic, not a
            // reported quantity — the exact count stays in `child_counts` and is what
            // the composed term is built from.
            q += and.child_counts[i] as f64 * state.or_stat(child).value;
        }
        state.set_and_value(and_idx, q);
    }
}

/// Fixed-point denominator for quantizing f64 cell Q values to integer
/// transport costs: costs enter the solver as `round(q * 2^20)`. Rounding to
/// this grid perturbs each arc cost by at most 2^-21; a flow of total supply
/// S therefore has an objective within S * 2^-20 of the unquantized one,
/// below the noise floor of the search (Q is a selection heuristic, and
/// nothing downstream consumes its low bits). The integer solve carries the
/// exact-arithmetic termination argument that f64 costs lack.
const Q_COST_SCALE: f64 = (1u64 << 20) as f64;

/// Transport-AND value recomputation: solve min-cost flow over current cell Qs,
/// update child_counts to the argmin flow, and set Q accordingly.
fn recompute_transport_and_value<A: AuIds, O: DenseId>(
    state: &mut McgsState<A, O>,
    and_idx: A::AndStats,
) {
    let rows = state.and_stat(and_idx).transport_rows.to_vec();
    let cols = state.and_stat(and_idx).transport_cols.to_vec();
    let n_rows = rows.len();
    let n_cols = cols.len();

    // Build the integer cost matrix from current child Q values via the typed
    // cell map, quantized at Q_COST_SCALE. Non-finite Qs are Forbidden.
    let cell_map = state.and_stat(and_idx).transport_cell_map.to_vec();
    let mut cost: Vec<Vec<Option<i128>>> = vec![vec![None; n_cols]; n_rows];
    for flat in 0..(n_rows * n_cols) {
        if let Some(child) = cell_map[flat] {
            let q = state.or_stat(state.and_stats.child_or(child)).value;
            if q.is_finite() {
                let scaled = (q * Q_COST_SCALE).round();
                // The solver's checked i128 adds need headroom for path sums;
                // 2^96 leaves 31 bits of it. Q values are node counts scaled
                // by 2^20, so a breach means a corrupted Q, not a large input.
                debug_assert!(
                    scaled.abs() < 2f64.powi(96),
                    "quantized transport cost magnitude exceeds i128 headroom"
                );
                cost[flat / n_cols][flat % n_cols] = Some(scaled as i128);
            }
        }
    }

    match solve_transport_quantized(&rows, &cols, &cost) {
        Some(flow) => {
            // Zero out child counts, then fill them from the selected flow.
            for position in 0..state.and_stat(and_idx).child_counts.len() {
                if state.and_stat(and_idx).child_counts[position] != 0 {
                    let child = state.and_stats.child_id(and_idx, position);
                    state.set_and_child_count(child, 0);
                }
            }
            // Q recomputes from the unquantized child values: quantization
            // decides the argmin flow only, never the reported value.
            let mut q = 1.0;
            for flat in 0..(n_rows * n_cols) {
                let i = flat / n_cols;
                let j = flat % n_cols;
                let x = flow[i][j];
                if x > 0
                    && let Some(child) = cell_map[flat]
                {
                    // Widening a flow cell to the surface width `child_counts` keeps.
                    state.set_and_child_count(child, u64::from(x));
                    q += f64::from(x) * state.or_stat(state.and_stats.child_or(child)).value;
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
fn recompute_or_value<A: AuIds, O: DenseId>(state: &mut McgsState<A, O>, or_idx: A::OrStats) {
    let stats = &state.or_stat(or_idx);
    if stats.terminal {
        return;
    }
    let mut sum = stats.initial_value;
    let mut total: u64 = 0;
    for (a, edge) in stats.edge_and.iter().enumerate() {
        if let Some(and_idx) = *edge {
            let n = stats.edge_visits[a];
            sum += n as f64 * state.and_stat(and_idx).value;
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
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    results: &mut BestResults<Cfg::Au>,
    state: &McgsState<Cfg::Au, Cfg::O>,
    and_idx: <Cfg::Au as AuIds>::AndStats,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let and = state.and_stat(and_idx);
    let is_transport = !and.transport_rows.is_empty();

    let children: Vec<(<Cfg::Au as AuIds>::Term, u64)> = if is_transport {
        // Solve transport over lexicographic best-result qualities for composition.
        let n_rows = and.transport_rows.len();
        let n_cols = and.transport_cols.len();
        let cell_map = &and.transport_cell_map;
        let mut cost = vec![vec![Cell::Forbidden; n_cols]; n_rows];
        let mut terms: Vec<Option<<Cfg::Au as AuIds>::Term>> = vec![None; n_rows * n_cols];
        for flat in 0..(n_rows * n_cols) {
            if let Some(child) = cell_map[flat] {
                let child_or = state.or_id(state.and_stats.child_or(child));
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
            row_supply: and.transport_rows.to_vec(),
            col_demand: and.transport_cols.to_vec(),
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
                    out.push((*t, u64::from(x)));
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
            let child_or = state.or_id(child_idx);
            match results.best_term(child_or) {
                Some(t) => out.push((t, and.child_counts[i])),
                None => return,
            }
        }
        out
    };

    let op = and.op;
    let candidate = pool.intern_action_result(TermOp::EGraph(op), &children, and.commutative);
    let parent_or = state.or_id(and.parent);
    let _ = snap;
    results.offer(parent_or, candidate, pool.quality(candidate));
}

/// Realize one edge: allocate the AND statistics struct and all child OR nodes.
/// `action_idx` indexes first over non-AC cached actions, then over AC/ACI
/// representation pairs (transport-AND-nodes). `config.dominance_pruning` must
/// equal the flag `ensure_or_stats` sized this node's edge arrays with: the
/// surviving-action subsequence is recomputed here from the same deterministic
/// predicates (cycle blocking, then dominance against the static generalize
/// value), so indices agree and edges stay hole-free.
#[allow(clippy::too_many_arguments)]
fn expand_action<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    action_cache: &mut ActionCache<Cfg::O, Cfg::Au, Cfg::M>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    or_idx: <Cfg::Au as AuIds>::OrStats,
    action_idx: usize,
    config: &McgsConfig,
) -> <Cfg::Au as AuIds>::AndStats
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let dominance = config.dominance_pruning;
    let or_id = state.or_id(or_idx);
    let l = *space.or_arena.left.get(or_id.to_index());
    let r = *space.or_arena.right.get(or_id.to_index());

    generate_actions(snap, action_cache, l, r);

    // Count non-AC surviving actions and clone only the descriptor this
    // expansion realizes; the cached vector itself is read in place. The
    // count still walks every cached action because `action_idx` indexes the
    // surviving subsequence and the transport range starts after it.
    let gen_size = static_generalize_quality(snap, l, r).0;
    let (non_ac_count, selected) = {
        let actions = action_cache.get(l, r).unwrap();
        let mut count = 0usize;
        let mut selected = None;
        for action in actions {
            let blocked = action
                .pairs
                .iter()
                .any(|p| space.is_cycle_blocked(or_id, p.left, p.right));
            if !blocked && !(dominance && structural_action_dominated(snap, action, gen_size)) {
                if count == action_idx {
                    selected = Some(action.clone());
                }
                count += 1;
            }
        }
        (count, selected)
    };

    if action_idx < non_ac_count {
        // Non-AC action: fixed-weight AND-node.
        let action = selected.expect("surviving action at index below the surviving count");
        let action = &action;

        let mut child_or_stats = Vec::with_capacity(action.pairs.len());
        let mut child_counts: Vec<u64> = Vec::with_capacity(action.pairs.len());
        for pair in &action.pairs {
            let (child_ctx_l, child_ctx_r) = space.derive_child_contexts(
                or_id,
                pair.left,
                pair.right,
                |c| snap.reachability().is_reachable(pair.left, c),
                |c| snap.reachability().is_reachable(pair.right, c),
            );
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
            let child_idx = ensure_or_stats(
                snap,
                space,
                pool,
                action_cache,
                results,
                state,
                child_or,
                config,
            );
            child_or_stats.push(child_idx);
            // Widening a structural multiplicity to the surface width `child_counts`
            // keeps; see `AndStatsData::child_counts`.
            child_counts.push(pair.count.to_u64());
        }
        let arity = child_or_stats.len();
        state.push_and_stat(
            AndStatsData {
                parent: or_idx,
                parent_slot: action_idx,
                op: action.op,
                commutative: snap.op_is_commutative(action.op),
                value: f64::INFINITY,
                child_or_stats,
                child_counts,
                child_visits: vec![0; arity],
                round_robin: 0,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
            config.closed_bit,
        )
    } else {
        // AC/ACI transport-AND-node: one per feasible transport action.
        // Descriptors come from the per-OR cache built at stats creation.
        let transport_idx = action_idx - non_ac_count;
        let desc = &state.or_stats.transport_descs(or_idx)[transport_idx];
        let (op, lm, rm) = (desc.op, desc.left.clone(), desc.right.clone());
        let legal_cells = desc.legal_cells.clone();
        // Already at the transport solver's width; narrowed once in the gate.
        let (row_supply, col_demand) = (desc.row_supply.clone(), desc.col_demand.clone());
        let (lm, rm) = (&lm, &rm);
        let n_rows = lm.len();
        let n_cols = rm.len();

        // Create children for legal cells; blocked cells map to None and are
        // Forbidden in the transport combiner.
        let mut cell_map: Vec<Option<usize>> = Vec::with_capacity(n_rows * n_cols);
        let mut filtered_children: Vec<<Cfg::Au as AuIds>::OrStats> = Vec::new();
        for (i, (lc, _)) in lm.iter().enumerate() {
            for (j, (rc, _)) in rm.iter().enumerate() {
                if !legal_cells[i * n_cols + j] {
                    cell_map.push(None);
                    continue;
                }
                let (child_ctx_l, child_ctx_r) = space.derive_child_contexts(
                    or_id,
                    *lc,
                    *rc,
                    |c| snap.reachability().is_reachable(*lc, c),
                    |c| snap.reachability().is_reachable(*rc, c),
                );
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
                let child_idx = ensure_or_stats(
                    snap,
                    space,
                    pool,
                    action_cache,
                    results,
                    state,
                    child_or,
                    config,
                );
                cell_map.push(Some(filtered_children.len()));
                filtered_children.push(child_idx);
            }
        }

        let arity = filtered_children.len();
        state.push_and_stat(
            AndStatsData {
                parent: or_idx,
                parent_slot: action_idx,
                op,
                commutative: true,
                value: f64::INFINITY,
                child_or_stats: filtered_children,
                child_counts: vec![0; arity],
                child_visits: vec![0; arity],
                round_robin: 0,
                transport_rows: row_supply,
                transport_cols: col_demand,
                transport_cell_map: cell_map,
            },
            config.closed_bit,
        )
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

#[inline]
fn wide_quality((size, variant_mass): (u32, u32)) -> (u128, u128) {
    (u128::from(size), u128::from(variant_mass))
}

/// Action-aware initialization (§A.4): compare the eager generalize action with
/// a deterministic concrete upper-bound estimate for every cycle-surviving
/// structural and transport action. Then recursively follow only the selected
/// action. This is complete at the operator-choice level without becoming an
/// exhaustive exact recursion over every action subtree.
///
/// Iterative frame machine (explicit stack): each frame holds the selection
/// outcome for its node — a structural action's pair list or a transport
/// action's positive-flow cells, in the recursive evaluation order
/// (left-to-right pairs / row-major cells) — plus a child cursor and the
/// collected child terms. Child OR nodes are created (contexts derived,
/// `get_or_insert_or_node`) at descent time, exactly when the recursion would,
/// so search-space side effects and term-pool interning order are identical.
/// Generalize selections and `l == r` terminals complete without a frame.
fn initial_rollout<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    space: &mut SearchSpace<Cfg::Au>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    action_cache: &mut ActionCache<Cfg::O, Cfg::Au, Cfg::M>,
    results: &mut BestResults<Cfg::Au>,
    state: &mut McgsState<Cfg::Au, Cfg::O>,
    or_id: <Cfg::Au as AuIds>::Or,
    config: &McgsConfig,
) -> <Cfg::Au as AuIds>::Term
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    struct Frame<Cfg: EGraphConfig> {
        or_id: <Cfg::Au as AuIds>::Or,
        l: ClassOf<Cfg>,
        r: ClassOf<Cfg>,
        op: Cfg::O,
        /// Transport frames compose commutatively and fall back to the
        /// generalize action when no cell carries flow.
        transport: bool,
        /// Child pairs in evaluation order: `(left, right, count)`.
        items: Vec<(ClassOf<Cfg>, ClassOf<Cfg>, u64)>,
        cursor: usize,
        child_terms: Vec<(<Cfg::Au as AuIds>::Term, u64)>,
    }

    let mut stack: Vec<Frame<Cfg>> = Vec::new();
    let mut pending = or_id;
    loop {
        // ── Enter: evaluate the selection for `pending` ──
        let current = pending;
        let l = *space.or_arena.left.get(current.to_index());
        let r = *space.or_arena.right.get(current.to_index());

        let mut done: Option<<Cfg::Au as AuIds>::Term> = None;
        if l == r {
            done = Some(build_best_term(snap, pool, l));
        } else if config.rollout_hybrid && results.is_exact(current) {
            // A frame solved by an earlier rollout or hybrid call: reuse its
            // certified term as the completed suffix.
            done = results.best_term(current);
        }
        if done.is_none() && l != r {
            generate_actions(snap, action_cache, l, r);
            // Rollout hybridization with two-part admission: the trigger fires
            // after enumeration so the node's own action count is known. The
            // rectangle and entry action count are complementary workload
            // estimates, not hard bounds. The frame's own state (same pair,
            // same cycle contexts, same cycle mode) is delegated and its term
            // becomes the completed suffix; a completed run is
            // marked exact, so when expansion later reaches this node it is
            // terminal at creation (and, under `closed_bit`, born closed).
            if config.rollout_hybrid && reachable_pairs(snap, l, r) <= config.hybrid_threshold {
                let non_ac = action_cache
                    .get(l, r)
                    .unwrap()
                    .iter()
                    .filter(|action| {
                        !action
                            .pairs
                            .iter()
                            .any(|p| space.is_cycle_blocked(current, p.left, p.right))
                    })
                    .count();
                let transport_count = transport_actions(snap, space, current, l, r).len();
                if (non_ac + transport_count) as u64 <= config.hybrid_action_threshold {
                    results.ensure_capacity(current);
                    let context = space.cycle_context(current);
                    let start = std::time::Instant::now();
                    let run = super::exact::run_exact_at(
                        snap,
                        pool,
                        l,
                        r,
                        &context,
                        space.cycle_mode,
                        None,
                        true,
                        true,
                        config.session_exact_memo.then_some(&mut state.exact_memo),
                        config.hybrid_node_budget,
                        None,
                    );
                    state.hybrid.calls += 1;
                    state.hybrid.time += start.elapsed();
                    results.offer(current, run.term, pool.quality(run.term));
                    if run.complete {
                        state.hybrid.proved += 1;
                        results.mark_exact(current);
                    }
                    // The term is the completed suffix either way: term
                    // validity does not depend on the proof, only
                    // `mark_exact` does.
                    done = Some(run.term);
                }
            }
        }
        if done.is_none() && l != r {
            // Borrowed in place: nothing below this point in the iteration
            // touches the cache, and the borrow ends before the next node's
            // `generate_actions`.
        } else if config.rollout_hybrid && reachable_pairs(snap, l, r) <= config.hybrid_threshold {
            // Rollout hybridization, fired on the rollout path. The frame's
            // own state (same pair, same cycle contexts, same cycle mode) is
            // delegated and its term becomes the completed suffix; a
            // completed run is marked exact, so when expansion later reaches
            // this node it is terminal at creation (and, under `closed_bit`,
            // born closed).
            results.ensure_capacity(current);
            if results.is_exact(current) {
                done = results.best_term(current);
            }
            if done.is_none() {
                let context = space.cycle_context(current);
                let start = std::time::Instant::now();
                let run = super::exact::run_exact_at(
                    snap,
                    pool,
                    l,
                    r,
                    &context,
                    space.cycle_mode,
                    None,
                    true,
                    true,
                    config.session_exact_memo.then_some(&mut state.exact_memo),
                    config.hybrid_node_budget,
                    None,
                );
                state.hybrid.calls += 1;
                state.hybrid.time += start.elapsed();
                results.offer(current, run.term, pool.quality(run.term));
                if run.complete {
                    state.hybrid.proved += 1;
                    results.mark_exact(current);
                }
                // The term is the completed suffix either way: term validity
                // does not depend on the proof, only `mark_exact` does.
                done = Some(run.term);
            }
        }
        if done.is_none() && l != r {
            generate_actions(snap, action_cache, l, r);
            // Borrowed in place: nothing below this point in the iteration
            // touches the cache, and the borrow ends before the next node's
            // `generate_actions`.
            let actions = action_cache.get(l, r).unwrap();
            let transport = transport_actions(snap, space, current, l, r);

            // Eager generalization is an explicit action and wins ties, so the
            // initializer can never return a result worse than this valid incumbent.
            let mut choice = InitialRolloutChoice::Generalize;
            let mut best_estimate = wide_quality(static_generalize_quality(snap, l, r));

            for (action_idx, action) in actions.iter().enumerate() {
                if action
                    .pairs
                    .iter()
                    .any(|p| space.is_cycle_blocked(current, p.left, p.right))
                {
                    continue;
                }

                let mut estimate = (1u128, 0u128);
                for pair in &action.pairs {
                    let child =
                        wide_quality(static_generalize_quality(snap, pair.left, pair.right));
                    estimate.0 = estimate
                        .0
                        .checked_add(child.0 * u128::from(pair.count.to_u64()))
                        .expect("structural rollout size estimate overflow");
                    estimate.1 = estimate
                        .1
                        .checked_add(child.1 * u128::from(pair.count.to_u64()))
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
                    // Narrowed once in the feasibility gate that produced `desc`.
                    row_supply: desc.row_supply.clone(),
                    col_demand: desc.col_demand.clone(),
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
                InitialRolloutChoice::Generalize => {
                    done = Some(evaluate_generalize_action(snap, pool, l, r));
                }
                InitialRolloutChoice::Structural(action_idx) => {
                    let action = &actions[action_idx];
                    let items: Vec<(ClassOf<Cfg>, ClassOf<Cfg>, u64)> = action
                        .pairs
                        .iter()
                        .map(|pair| (pair.left, pair.right, pair.count.to_u64()))
                        .collect();
                    let capacity = items.len();
                    stack.push(Frame {
                        or_id: current,
                        l,
                        r,
                        op: action.op,
                        transport: false,
                        items,
                        cursor: 0,
                        child_terms: Vec::with_capacity(capacity),
                    });
                }
                InitialRolloutChoice::Transport { descriptor, flow } => {
                    let desc = transport
                        .into_iter()
                        .nth(descriptor)
                        .expect("selected transport descriptor disappeared");
                    let n_cols = desc.right.len();
                    // Positive-flow cells in row-major order: the recursive
                    // evaluation order of the selected static flow.
                    let mut items: Vec<(ClassOf<Cfg>, ClassOf<Cfg>, u64)> = Vec::new();
                    for (i, (lc, _)) in desc.left.iter().enumerate() {
                        for (j, (rc, _)) in desc.right.iter().enumerate() {
                            let count = flow[i][j];
                            if count == 0 {
                                continue;
                            }
                            debug_assert!(desc.legal_cells[i * n_cols + j]);
                            items.push((*lc, *rc, u64::from(count)));
                        }
                    }
                    stack.push(Frame {
                        or_id: current,
                        l,
                        r,
                        op: desc.op,
                        transport: true,
                        items,
                        cursor: 0,
                        child_terms: Vec::new(),
                    });
                }
            }
        }

        // ── Advance: deliver completed terms upward, descend or compose ──
        loop {
            if let Some(term) = done.take() {
                let Some(parent) = stack.last_mut() else {
                    return term;
                };
                let (_, _, count) = parent.items[parent.cursor];
                parent.child_terms.push((term, count));
                parent.cursor += 1;
            }
            let top = stack
                .last_mut()
                .expect("initial rollout stack cannot be empty");
            if top.cursor < top.items.len() {
                // Create the child OR node now, exactly when the recursion would.
                let (cl, cr, _) = top.items[top.cursor];
                let (child_ctx_l, child_ctx_r) = space.derive_child_contexts(
                    top.or_id,
                    cl,
                    cr,
                    |c| snap.reachability().is_reachable(cl, c),
                    |c| snap.reachability().is_reachable(cr, c),
                );
                let (child_or, _) = space.get_or_insert_or_node(
                    cl,
                    cr,
                    child_ctx_l,
                    child_ctx_r,
                    snap.best_size(cl),
                    snap.best_size(cr),
                );
                pending = child_or;
                break; // descend
            }
            let frame = stack.pop().expect("initial rollout stack cannot be empty");
            done = Some(if frame.transport {
                if frame.child_terms.is_empty() {
                    evaluate_generalize_action(snap, pool, frame.l, frame.r)
                } else {
                    pool.intern_action_result(TermOp::EGraph(frame.op), &frame.child_terms, true)
                }
            } else {
                pool.intern_action_result(
                    TermOp::EGraph(frame.op),
                    &frame.child_terms,
                    snap.op_is_commutative(frame.op),
                )
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::au::exact::eager_with_memo;
    use crate::au::space::OrId;
    use crate::au::{AndChildStatId, AndStatsId, OrEdgeStatId, OrStatsId};
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

    crate::containers::define_id7! { struct TinyId / TinyStoredId, "tiny"; }
    crate::containers::define_id7! { struct TinyOrStats / TinyStoredOrStats, "tos"; }
    crate::containers::define_id7! { struct TinyAndStats / TinyStoredAndStats, "tas"; }
    crate::containers::define_id7! { struct TinyOrEdge / TinyStoredOrEdge, "toe"; }
    crate::containers::define_id7! { struct TinyAndChild / TinyStoredAndChild, "tac"; }

    struct TinyAu;
    impl AuIds for TinyAu {
        type Index = u8;
        type Class = TinyId;
        type Scc = TinyId;
        type Or = TinyId;
        type Action = TinyId;
        type Context = TinyId;
        type Term = TinyId;
        type OrStats = TinyOrStats;
        type AndStats = TinyAndStats;
        type SnapshotMember = TinyId;
        type ContextElem = TinyId;
        type TermChild = TinyId;
        type ReachBlock = TinyId;
        type OrEdgeStat = TinyOrEdge;
        type AndChildStat = TinyAndChild;
    }

    fn tiny_or_data(edges: usize) -> OrStatsData<TinyAndStats> {
        OrStatsData {
            initial_value: 1.0,
            value: 1.0,
            min_size: 1.0,
            max_size: 1.0,
            terminal: edges == 0,
            edge_visits: vec![0; edges],
            edge_and: vec![None; edges],
            edge_bounds: vec![0; edges],
        }
    }

    fn tiny_and_data(
        children: usize,
        transport_cell_map: Vec<Option<usize>>,
    ) -> AndStatsData<TinyOrStats, TinyId> {
        AndStatsData {
            parent: TinyOrStats::from_usize(0),
            parent_slot: 0,
            op: TinyId::from_usize(0),
            commutative: false,
            value: 1.0,
            child_or_stats: vec![TinyOrStats::from_usize(0); children],
            child_counts: vec![1; children],
            child_visits: vec![0; children],
            round_robin: 0,
            transport_rows: Vec::new(),
            transport_cols: Vec::new(),
            transport_cell_map,
        }
    }

    fn tiny_or_lengths(arena: &OrStatsArena<TinyAu, TinyId>) -> [usize; 15] {
        [
            arena.or_ids.len().as_usize(),
            arena.min_size.len().as_usize(),
            arena.max_size.len().as_usize(),
            arena.terminal.len().as_usize(),
            arena.edge_spans.len().as_usize(),
            arena.initial_value.len().as_usize(),
            arena.value.len().as_usize(),
            arena.edge_visits.len().as_usize(),
            arena.edge_and.len().as_usize(),
            arena.transport_descs.len().as_usize(),
            arena.closed.len().as_usize(),
            arena.open_edges.len().as_usize(),
            arena.parent_head.len().as_usize(),
            arena.parent_and.len().as_usize(),
            arena.parent_next.len().as_usize(),
        ]
    }

    fn tiny_and_lengths(arena: &AndStatsArena<TinyAu, TinyId>) -> [usize; 14] {
        [
            arena.parent.len().as_usize(),
            arena.op.len().as_usize(),
            arena.commutative.len().as_usize(),
            arena.child_spans.len().as_usize(),
            arena.child_or_stats.len().as_usize(),
            arena.value.len().as_usize(),
            arena.child_counts.len().as_usize(),
            arena.child_visits.len().as_usize(),
            arena.round_robin.len().as_usize(),
            arena.transport_rows.len().as_usize(),
            arena.transport_cols.len().as_usize(),
            arena.transport_cell_map.len().as_usize(),
            arena.closed.len().as_usize(),
            arena.open_children.len().as_usize(),
        ]
    }

    #[test]
    fn or_stats_capacity_panics_leave_all_pools_aligned() {
        let mut edge_full: OrStatsArena<TinyAu, TinyId> = OrStatsArena::new();
        edge_full.push(TinyId::from_usize(0), tiny_or_data(128), Vec::new());
        let before = tiny_or_lengths(&edge_full);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            edge_full.push(TinyId::from_usize(1), tiny_or_data(1), Vec::new());
        }));
        assert!(outcome.is_err());
        assert_eq!(tiny_or_lengths(&edge_full), before);

        let mut node_full: OrStatsArena<TinyAu, TinyId> = OrStatsArena::new();
        for i in 0..128 {
            node_full.push(TinyId::from_usize(i), tiny_or_data(0), Vec::new());
        }
        let before = tiny_or_lengths(&node_full);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            node_full.push(TinyId::from_usize(0), tiny_or_data(0), Vec::new());
        }));
        assert!(outcome.is_err());
        assert_eq!(tiny_or_lengths(&node_full), before);
    }

    #[test]
    fn and_stats_preflight_panics_leave_all_pools_aligned() {
        let mut child_full: AndStatsArena<TinyAu, TinyId> = AndStatsArena::new();
        child_full.push(tiny_and_data(128, vec![Some(127)]));
        let before = tiny_and_lengths(&child_full);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            child_full.push(tiny_and_data(1, vec![Some(0)]));
        }));
        assert!(outcome.is_err());
        assert_eq!(tiny_and_lengths(&child_full), before);

        let mut invalid_map: AndStatsArena<TinyAu, TinyId> = AndStatsArena::new();
        let before = tiny_and_lengths(&invalid_map);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            invalid_map.push(tiny_and_data(1, vec![Some(1)]));
        }));
        assert!(outcome.is_err());
        assert_eq!(tiny_and_lengths(&invalid_map), before);
    }

    fn os(i: usize) -> OrStatsId {
        OrStatsId::from_usize(i)
    }
    fn asid(i: usize) -> AndStatsId {
        AndStatsId::from_usize(i)
    }
    fn cs(i: usize) -> AndChildStatId {
        AndChildStatId::from_usize(i)
    }
    fn push_or(state: &mut McgsState, data: OrStatsData<AndStatsId>) -> OrStatsId {
        let or_id = OrId::from_usize(state.or_stats.len().as_usize());
        state.push_or_stat(or_id, data, Vec::new())
    }
    fn push_and(
        state: &mut McgsState,
        data: AndStatsData<OrStatsId, crate::id::OpId>,
    ) -> AndStatsId {
        // Synthetic fixtures track the closed bookkeeping: the counters and
        // reverse edges are pushed, so a fixture can drive the closure walk.
        state.push_and_stat(data, true)
    }

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
        let (mcgs_term, mcgs_pool, completion, _) = run_mcgs(&snap, lc, rc, &config).unwrap();
        assert_eq!(mcgs_pool.size(mcgs_term), exact_size);
        // This tiny graph should be fully certified within 500 playouts.
        assert_eq!(completion, super::super::session::Completion::Exact);
    }

    /// The §3.4.4 greedy counterexample: the greedy diagonal costs 10, the
    /// crossed matching costs 9. The initial rollout finds 10; only result
    /// composition through backpropagation can reach 9. This is the regression
    /// gate for "MCGS cannot improve beyond its initial rollout".
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
        let (mcgs_term, mcgs_pool, _, _) = run_mcgs(&snap, lc, rc, &config).unwrap();
        assert_eq!(
            mcgs_pool.size(mcgs_term),
            exact_size,
            "MCGS must improve past its initial rollout (size 10) to the optimum (9)"
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
        let (term, pool, _, _) = run_mcgs(&snap, ac, ac, &config).unwrap();
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
        let (term, pool, _, _) = run_mcgs(&snap, ac, bc, &config).unwrap();
        assert!(pool.size(term) < 100);
    }

    /// Transport value recomputation must minimize the actual floating-point
    /// child Q estimates. Truncating every Q to u32 makes all four costs tie in
    /// this instance, selects the diagonal, and reports 1 + 1.9 + 1.9 = 4.8;
    /// the true crossed optimum is 1 + 1.1 + 1.1 = 3.2.
    #[test]
    fn transport_and_value_uses_fractional_q_ordering() {
        fn child_stats(value: f64) -> OrStatsData<crate::au::AndStatsId> {
            OrStatsData {
                initial_value: value,
                value,
                min_size: 1.0,
                max_size: 2.0,
                terminal: true,
                edge_visits: Vec::new(),
                edge_and: Vec::new(),
                edge_bounds: Vec::new(),
            }
        }

        let mut state: McgsState = McgsState::new();
        // Row-major Q matrix: diagonal 1.9 + 1.9, crossed 1.1 + 1.1.
        for value in [1.9, 1.1, 1.1, 1.9] {
            push_or(&mut state, child_stats(value));
        }
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                parent_slot: 0,
                op: crate::id::OpId::from_usize(0),
                commutative: true,
                value: f64::INFINITY,
                child_or_stats: vec![os(0), os(1), os(2), os(3)],
                child_counts: vec![0; 4],
                child_visits: vec![0; 4],
                round_robin: 0,
                transport_rows: vec![1, 1],
                transport_cols: vec![1, 1],
                transport_cell_map: vec![Some(0), Some(1), Some(2), Some(3)],
            },
        );

        recompute_transport_and_value(&mut state, asid(0));
        let and = state.and_stat(asid(0));
        assert!(
            (and.value - 3.2).abs() < 1e-12,
            "transport must select the crossed fractional-Q optimum; got {}",
            and.value
        );
        assert_eq!(and.child_counts, &[0, 1, 1, 0]);
        let child_span: crate::au::Span<AndChildStatId> = state.and_stats.child_span(asid(0));
        assert_eq!(child_span, crate::au::Span::new(0, 4));
        assert_eq!(
            and.transport_cell_map,
            &[Some(cs(0)), Some(cs(1)), Some(cs(2)), Some(cs(3))]
        );
    }

    #[test]
    fn structural_completion_rejects_unresolved_cycle() {
        let mut state: McgsState = McgsState::new();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 3.0,
                value: 3.0,
                min_size: 1.0,
                max_size: 1.0,
                terminal: false,
                edge_visits: vec![1],
                edge_and: vec![Some(asid(0))],
                edge_bounds: vec![0; 1],
            },
        );
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                parent_slot: 0,
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: 3.0,
                child_or_stats: vec![os(0)],
                child_counts: vec![1],
                child_visits: vec![1],
                round_robin: 1,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );

        assert!(
            !is_structurally_complete(&state, os(0)),
            "an unresolved cycle is not a finite structural optimality certificate"
        );
    }

    #[test]
    fn mcgs_restore_clears_dangling_edges() {
        let mut state: McgsState = McgsState::new();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 3.0,
                value: 3.0,
                min_size: 1.0,
                max_size: 2.0,
                terminal: false,
                edge_visits: vec![0],
                edge_and: vec![None],
                edge_bounds: vec![0; 1],
            },
        );
        let token = state.mark();

        // Simulate expansion: create an AND-node and link it.
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                parent_slot: 0,
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: 3.0,
                child_or_stats: Vec::new(),
                child_counts: Vec::new(),
                child_visits: Vec::new(),
                round_robin: 0,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );
        state.set_or_edge_and(os(0), 0, Some(asid(0)));
        state.bump_or_edge_visit(os(0), 0);

        state.restore(token);
        assert_eq!(state.and_stats.len(), 0);
        let edges: crate::au::Span<OrEdgeStatId> = state.or_stats.edge_span(os(0));
        assert_eq!(edges, crate::au::Span::new(0, 1));
        assert_eq!(state.or_stat(os(0)).edge_and, &[None]);
        assert_eq!(state.or_stat(os(0)).edge_visits, &[0]);
    }

    /// Live-incumbent pruning: an exclusion set after a mark rewinds with the mark, together
    /// with the open-edge accounting it drove; the per-slot bound survives
    /// (append-only, node predates the mark).
    #[test]
    fn mcgs_restore_rewinds_exclusions() {
        let mut state: McgsState = McgsState::new();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 3.0,
                value: 3.0,
                min_size: 1.0,
                max_size: 2.0,
                terminal: false,
                edge_visits: vec![0, 0],
                edge_and: vec![None, None],
                edge_bounds: vec![7, 9],
            },
        );
        let token = state.mark();

        state.or_stats.set_edge_excluded(os(0), 1);
        state.or_stats.close_edge(os(0));
        assert!(state.or_stats.edge_excluded(os(0), 1));
        assert_eq!(state.or_stats.open_edges(os(0)), 1);

        state.restore(token);
        assert!(!state.or_stats.edge_excluded(os(0), 0));
        assert!(!state.or_stats.edge_excluded(os(0), 1));
        assert_eq!(state.or_stats.open_edges(os(0)), 2);
        assert_eq!(state.or_stats.edge_bound(os(0), 0), 7);
        assert_eq!(state.or_stats.edge_bound(os(0), 1), 9);
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
        let (_, _, completion, _) = run_mcgs(&snap, lc, rc, &config).unwrap();
        assert_eq!(
            completion,
            super::super::session::Completion::Exact,
            "shared DAG should certify Exact (200 playouts on a 3-node graph)"
        );
    }

    #[test]
    fn transport_and_value_preserves_sub_mill_ordering() {
        fn child_stats(value: f64) -> OrStatsData<crate::au::AndStatsId> {
            OrStatsData {
                initial_value: value,
                value,
                min_size: 1.0,
                max_size: 2.0,
                terminal: true,
                edge_visits: Vec::new(),
                edge_and: Vec::new(),
                edge_bounds: Vec::new(),
            }
        }

        let mut state: McgsState = McgsState::new();
        for value in [1.0004, 1.0001, 1.0001, 1.0004] {
            push_or(&mut state, child_stats(value));
        }
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                parent_slot: 0,
                op: crate::id::OpId::from_usize(0),
                commutative: true,
                value: f64::INFINITY,
                child_or_stats: vec![os(0), os(1), os(2), os(3)],
                child_counts: vec![0; 4],
                child_visits: vec![0; 4],
                round_robin: 0,
                transport_rows: vec![1, 1],
                transport_cols: vec![1, 1],
                transport_cell_map: vec![Some(0), Some(1), Some(2), Some(3)],
            },
        );

        recompute_transport_and_value(&mut state, asid(0));
        let and = state.and_stat(asid(0));
        assert!(
            (and.value - 3.0002).abs() < 1e-12,
            "transport must preserve the crossed sub-mill optimum; got {}",
            and.value
        );
        assert_eq!(and.child_counts, &[0, 1, 1, 0]);
    }

    #[test]
    fn mcgs_restore_undoes_all_surviving_statistics() {
        let mut state: McgsState = McgsState::new();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 3.0,
                value: 3.0,
                min_size: 1.0,
                max_size: 2.0,
                terminal: false,
                edge_visits: vec![1],
                edge_and: vec![Some(asid(0))],
                edge_bounds: vec![0; 1],
            },
        );
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                parent_slot: 0,
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: 3.0,
                child_or_stats: vec![os(0)],
                child_counts: vec![1],
                child_visits: vec![1],
                round_robin: 1,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );
        let token = state.mark();

        state.set_or_initial_value(os(0), 2.0);
        state.set_or_value(os(0), 2.0);
        state.bump_or_edge_visit(os(0), 0);
        state.set_or_edge_and(os(0), 0, None);
        state.set_and_value(asid(0), 2.0);
        state.set_and_child_count(cs(0), 7);
        state.bump_and_child_visit(cs(0));
        state.bump_and_round_robin(asid(0));
        // The closed bookkeeping is overlay state like the rest: bits, open
        // counters, and reverse-edge entries all have to rewind.
        state.and_stats.close_child(asid(0));
        state.and_stats.set_closed(asid(0));
        state.or_stats.close_edge(os(0));
        state.or_stats.set_closed(os(0));
        state.or_stats.push_parent(os(0), asid(0));

        state.restore(token);
        let or = state.or_stat(os(0));
        assert_eq!(state.or_id(os(0)), OrId::from_usize(0));
        assert_eq!(or.initial_value, 3.0);
        assert_eq!(or.value, 3.0);
        assert_eq!(or.min_size, 1.0);
        assert_eq!(or.max_size, 2.0);
        assert!(!or.terminal);
        assert_eq!(or.edge_visits, &[1]);
        assert_eq!(or.edge_and, &[Some(asid(0))]);
        let and = state.and_stat(asid(0));
        assert_eq!(and.parent, os(0));
        assert_eq!(and.op, crate::id::OpId::from_usize(0));
        assert!(!and.commutative);
        assert_eq!(and.value, 3.0);
        assert_eq!(and.child_or_stats, &[os(0)]);
        assert_eq!(and.child_counts, &[1]);
        assert_eq!(state.and_stats.child_visits(asid(0)), &[1]);
        assert_eq!(and.round_robin, 1);
        assert!(and.transport_rows.is_empty());
        assert!(and.transport_cols.is_empty());
        assert!(and.transport_cell_map.is_empty());
        assert!(!state.or_closed(os(0)));
        assert!(!state.and_closed(asid(0)));
        assert_eq!(state.or_stats.open_edges(os(0)), 1);
        assert_eq!(state.and_stats.open_children(asid(0)), 1);
        // The one entry `push_and` registered survives; the one pushed after
        // the mark does not.
        assert_eq!(state.or_stats.parent_and.len().as_usize(), 1);
        assert!(state.or_stats.parent_head(os(0)).is_some());
    }

    #[test]
    fn completion_closes_values_through_every_shared_parent() {
        fn or_stats(
            value: f64,
            terminal: bool,
            edge: Option<usize>,
        ) -> OrStatsData<crate::au::AndStatsId> {
            OrStatsData {
                initial_value: value,
                value,
                min_size: 1.0,
                max_size: 20.0,
                terminal,
                edge_visits: edge.map_or_else(Vec::new, |_| vec![1]),
                edge_and: edge.map_or_else(Vec::new, |idx| vec![Some(asid(idx))]),
                edge_bounds: edge.map_or_else(Vec::new, |_| vec![0]),
            }
        }
        fn and_stats(
            parent: usize,
            value: f64,
            children: Vec<usize>,
        ) -> AndStatsData<crate::au::OrStatsId, crate::id::OpId> {
            let arity = children.len();
            AndStatsData {
                parent: os(parent),
                parent_slot: 0,
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value,
                child_or_stats: children.into_iter().map(os).collect(),
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
        let mut state: McgsState = McgsState::new();
        for data in [
            or_stats(20.0, false, Some(0)),
            or_stats(10.0, false, Some(1)),
            or_stats(10.0, false, Some(2)),
            or_stats(10.0, false, Some(3)),
            or_stats(1.0, true, None),
        ] {
            push_or(&mut state, data);
        }
        for data in [
            and_stats(0, 21.0, vec![1, 2]),
            and_stats(1, 11.0, vec![3]),
            and_stats(2, 11.0, vec![3]),
            and_stats(3, 2.0, vec![4]),
        ] {
            push_and(&mut state, data);
        }

        // Simulate backpropagation only along root -> left -> shared -> leaf.
        recompute_and_value(&mut state, asid(3));
        recompute_or_value(&mut state, os(3));
        recompute_and_value(&mut state, asid(1));
        recompute_or_value(&mut state, os(1));
        recompute_and_value(&mut state, asid(0));
        recompute_or_value(&mut state, os(0));
        assert!(is_structurally_complete(&state, os(0)));

        // The children-first closure pass (run before certifying Exact)
        // propagates the final child values through EVERY incoming parent.
        close_values(&mut state, os(0));
        let closed_root = state.or_stat(os(0)).value;

        // Reference: manually push through the other incoming parent too;
        // no further improvement should be possible after the closure.
        recompute_and_value(&mut state, asid(2));
        recompute_or_value(&mut state, os(2));
        recompute_and_value(&mut state, asid(0));
        recompute_or_value(&mut state, os(0));
        assert_eq!(
            closed_root,
            state.or_stat(os(0)).value,
            "Exact certification must close values/results through every incoming parent"
        );
    }

    /// `or_postorder` on a single OR node with a wide expanded fan (E edges of
    /// arity K): each node exactly once, children before the parent, and the
    /// traversal is linear in the E*K fan-out. The linearity half is a
    /// release-only timing canary because a traversal that recollects the
    /// parent's full flattened child list on every cursor step is quadratic
    /// in E*K, which stalls `close_completed_dag` for minutes on the anytime
    /// pilot's ac m64c16 root (4096 edges x 289 cells) at the first budget
    /// that completes expansion. At E=1024, K=64 that
    /// recollection copies ~4e9 ids (seconds under release codegen); the
    /// per-frame collection finishes in milliseconds.
    #[test]
    fn or_postorder_is_linear_in_the_expanded_fan_out() {
        const E: usize = 1024;
        const K: usize = 64;
        let mut state: McgsState = McgsState::new();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 10.0,
                value: 10.0,
                min_size: 1.0,
                max_size: 20.0,
                terminal: false,
                edge_visits: vec![1; E],
                edge_and: (0..E).map(|e| Some(asid(e))).collect(),
                edge_bounds: vec![0; E],
            },
        );
        for _ in 0..E * K {
            push_or(
                &mut state,
                OrStatsData {
                    initial_value: 1.0,
                    value: 1.0,
                    min_size: 1.0,
                    max_size: 20.0,
                    terminal: true,
                    edge_visits: Vec::new(),
                    edge_and: Vec::new(),
                    edge_bounds: Vec::new(),
                },
            );
        }
        for e in 0..E {
            push_and(
                &mut state,
                AndStatsData {
                    parent: os(0),
                    parent_slot: 0,
                    op: crate::id::OpId::from_usize(0),
                    commutative: false,
                    value: 1.0 + K as f64,
                    child_or_stats: (0..K).map(|k| os(1 + e * K + k)).collect(),
                    child_counts: vec![1; K],
                    child_visits: vec![1; K],
                    round_robin: 0,
                    transport_rows: Vec::new(),
                    transport_cols: Vec::new(),
                    transport_cell_map: Vec::new(),
                },
            );
        }

        let start = std::time::Instant::now();
        let postorder = or_postorder(&state, os(0));
        let elapsed = start.elapsed();

        assert_eq!(postorder.len(), 1 + E * K, "each node exactly once");
        assert_eq!(*postorder.last().unwrap(), os(0), "children before parent");
        let mut seen = vec![false; 1 + E * K];
        for &or_idx in &postorder {
            assert!(!seen[or_idx.to_usize()], "no node repeats");
            seen[or_idx.to_usize()] = true;
        }
        // Timing canary, calibrated for release codegen only (same policy as
        // in_node_search_is_binary_not_linear): unoptimized or instrumented
        // builds pay real call boundaries everywhere and the margin shrinks.
        if !cfg!(debug_assertions) {
            assert!(
                elapsed < std::time::Duration::from_secs(2),
                "or_postorder took {elapsed:?} on a {E}x{K} fan; the traversal \
                 must stay linear in the expanded fan-out"
            );
        }
    }

    #[test]
    fn mcgs_visit_counters_cover_the_supported_playout_budget() {
        let stats: OrStatsData<AndStatsId> = OrStatsData {
            initial_value: 1.0,
            value: 1.0,
            min_size: 1.0,
            max_size: 1.0,
            terminal: false,
            edge_visits: vec![0],
            edge_and: vec![None],
            edge_bounds: vec![0; 1],
        };
        assert_eq!(
            core::mem::size_of_val(&stats.edge_visits[0]),
            core::mem::size_of::<u64>(),
            "visit counters must represent every supported u64 playout budget"
        );
    }

    #[test]
    fn mcgs_rejects_foreign_token_before_mutation() {
        let mut source: McgsState = McgsState::new();
        let foreign = source.mark();

        let mut target: McgsState = McgsState::new();
        push_or(
            &mut target,
            OrStatsData {
                initial_value: 4.0,
                value: 4.0,
                min_size: 1.0,
                max_size: 2.0,
                terminal: true,
                edge_visits: Vec::new(),
                edge_and: Vec::new(),
                edge_bounds: Vec::new(),
            },
        );
        assert!(!target.is_valid_token(&foreign));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            target.restore(foreign);
        }));
        assert!(outcome.is_err());
        assert_eq!(target.or_stats.len(), 1);
        assert_eq!(target.or_stat(os(0)).value, 4.0);
    }

    #[test]
    fn mcgs_invalidates_abandoned_future_token() {
        let mut state: McgsState = McgsState::new();
        let outer = state.mark();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 1.0,
                value: 1.0,
                min_size: 1.0,
                max_size: 1.0,
                terminal: true,
                edge_visits: Vec::new(),
                edge_and: Vec::new(),
                edge_bounds: Vec::new(),
            },
        );
        let abandoned = state.mark();
        state.set_or_value(os(0), 2.0);
        state.restore(outer);
        assert!(!state.is_valid_token(&abandoned));
    }

    /// Synthetic 2-child AND fixture for AND-selector tests: both children
    /// are nonterminal. Child 0 is strong (Q at its basis, reward near 1);
    /// child 1 is weak (large Q against a small basis, reward near 0, the
    /// high-uncertainty child). The AND node at index 0 has both as children.
    fn two_child_and_fixture() -> McgsState {
        let mut state: McgsState = McgsState::new();
        // Child 0: nonterminal, strong estimate (reward near 1).
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 2.1,
                value: 2.1,
                min_size: 2.0,
                max_size: 2.0,
                terminal: false,
                edge_visits: vec![0],
                edge_and: vec![None],
                edge_bounds: vec![0; 1],
            },
        );
        // Child 1: nonterminal, weak estimate (reward near 0).
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 50.0,
                value: 50.0,
                min_size: 1.0,
                max_size: 2.0,
                terminal: false,
                edge_visits: vec![0],
                edge_and: vec![None],
                edge_bounds: vec![0; 1],
            },
        );
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                parent_slot: 0,
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: f64::INFINITY,
                child_or_stats: vec![os(0), os(1)],
                child_counts: vec![1, 1],
                child_visits: vec![0, 0],
                round_robin: 0,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );
        state
    }

    /// Drive `select_and_child` for `n` rounds, maintaining both counters the
    /// way `playout` does, and return the per-child visit totals.
    fn drive_and_selector(state: &mut McgsState, selector: AndSelector, n: usize) -> Vec<u64> {
        let config = McgsConfig {
            and_selector: selector,
            ..Default::default()
        };
        for _ in 0..n {
            let pos = select_and_child(state, asid(0), &config);
            let child = state.and_stats.child_id(asid(0), pos);
            state.bump_and_round_robin(asid(0));
            state.bump_and_child_visit(child);
        }
        state.and_stats.child_visits(asid(0)).to_vec()
    }

    /// LctAnd routes visits toward the less-visited / higher-uncertainty
    /// child: the weak nonterminal (reward near 0) receives the dominant
    /// share of flux, while its strong sibling (reward near 1) keeps only its
    /// O(√N) exploration visits (§2.5.1 E/F: the diverging exploration term
    /// still revisits it — with C = √2 that is ≈ C·√N visits, ~28 of 400).
    #[test]
    fn lct_and_routes_visits_to_the_uncertain_child() {
        let mut state = two_child_and_fixture();
        let visits = drive_and_selector(&mut state, AndSelector::LctAnd, 400);
        assert!(
            visits[1] >= 350,
            "LctAnd must route the dominant share of effort to the weak child; got {visits:?}"
        );
        assert!(
            (1..=50).contains(&visits[0]),
            "the strong child must keep only its O(sqrt N) exploration visits; got {visits:?}"
        );
    }

    /// UctAnd refines the most promising child: the strong child (reward
    /// near 1) wins over the weak sibling, with the exploration term still
    /// paying O(√N) visits to the weak child.
    #[test]
    fn uct_and_routes_visits_to_the_promising_child() {
        let mut state = two_child_and_fixture();
        let visits = drive_and_selector(&mut state, AndSelector::UctAnd, 400);
        assert!(
            visits[0] >= 350,
            "UctAnd must route the dominant share of effort to the strong child; got {visits:?}"
        );
        assert!(
            (1..=50).contains(&visits[1]),
            "the neglected child must keep only its O(sqrt N) exploration visits; got {visits:?}"
        );
    }

    /// Necessity proof for the terminal-skip gate: on a near-tie — a terminal
    /// child (reward exactly 1) beside a nonterminal whose converged reward is
    /// close to 1, the deep-spine steady state — the bare lct_and formula
    /// splits flux roughly evenly (bonus-balance equalizes visits), which is
    /// exactly the round-robin 2^-depth decay the value-guided selector must
    /// fix. With the gate, the nonterminal child receives every visit.
    #[test]
    fn lct_and_without_terminal_skip_splits_flux_on_near_ties() {
        fn near_tie_fixture() -> McgsState {
            let mut state: McgsState = McgsState::new();
            // Child 0: terminal (l = r), reward exactly 1.
            push_or(
                &mut state,
                OrStatsData {
                    initial_value: 1.0,
                    value: 1.0,
                    min_size: 1.0,
                    max_size: 1.0,
                    terminal: true,
                    edge_visits: Vec::new(),
                    edge_and: Vec::new(),
                    edge_bounds: Vec::new(),
                },
            );
            // Child 1: nonterminal spine child whose Q has converged to just
            // past its basis: reward = 1 - ncr is close to (but below) 1.
            push_or(
                &mut state,
                OrStatsData {
                    initial_value: 40.2,
                    value: 40.2,
                    min_size: 40.0,
                    max_size: 40.0,
                    terminal: false,
                    edge_visits: vec![0],
                    edge_and: vec![None],
                    edge_bounds: vec![0; 1],
                },
            );
            push_and(
                &mut state,
                AndStatsData {
                    parent: os(0),
                    parent_slot: 0,
                    op: crate::id::OpId::from_usize(0),
                    commutative: false,
                    value: f64::INFINITY,
                    child_or_stats: vec![os(0), os(1)],
                    child_counts: vec![1, 1],
                    child_visits: vec![0, 0],
                    round_robin: 0,
                    transport_rows: Vec::new(),
                    transport_cols: Vec::new(),
                    transport_cell_map: Vec::new(),
                },
            );
            state
        }

        let config = McgsConfig::default();
        assert_eq!(config.and_selector, AndSelector::LctAnd);

        // Ungated formula: near-equal split (the defect).
        let mut state = near_tie_fixture();
        for _ in 0..400 {
            let pos = select_and_child_value_guided(&state, asid(0), &config, -1.0, false);
            let child = state.and_stats.child_id(asid(0), pos);
            state.bump_and_round_robin(asid(0));
            state.bump_and_child_visit(child);
        }
        let ungated = state.and_stats.child_visits(asid(0)).to_vec();
        assert!(
            ungated[0] >= 150 && ungated[1] >= 150,
            "without the gate, near-ties must show the flux split that motivates it; \
             got {ungated:?} (if this fails, the gate may no longer be necessary — \
             re-evaluate it before weakening this pin)"
        );

        // Production selector (gated): the terminal child is skipped entirely.
        let mut state = near_tie_fixture();
        let visits = drive_and_selector(&mut state, AndSelector::LctAnd, 400);
        assert_eq!(
            visits,
            vec![0, 400],
            "with the gate, the nonterminal child receives every visit"
        );
    }

    /// When every child of an AND node is terminal the value-guided selectors
    /// return the smallest index (the choice is inert: descent stops at any
    /// terminal child).
    #[test]
    fn value_guided_selector_is_inert_when_all_children_are_terminal() {
        let mut state: McgsState = McgsState::new();
        for value in [1.0, 2.0] {
            push_or(
                &mut state,
                OrStatsData {
                    initial_value: value,
                    value,
                    min_size: 1.0,
                    max_size: 1.0,
                    terminal: true,
                    edge_visits: Vec::new(),
                    edge_and: Vec::new(),
                    edge_bounds: Vec::new(),
                },
            );
        }
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                parent_slot: 0,
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: f64::INFINITY,
                child_or_stats: vec![os(0), os(1)],
                child_counts: vec![1, 1],
                child_visits: vec![0, 0],
                round_robin: 0,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );
        for selector in [AndSelector::LctAnd, AndSelector::UctAnd] {
            let config = McgsConfig {
                and_selector: selector,
                ..Default::default()
            };
            assert_eq!(select_and_child(&state, asid(0), &config), 0);
        }
    }

    /// RoundRobin rotates strictly, splitting visits equally regardless of
    /// values, and advances the shared round-robin counter.
    #[test]
    fn round_robin_rotates_regardless_of_values() {
        let mut state = two_child_and_fixture();
        let config = McgsConfig {
            and_selector: AndSelector::RoundRobin,
            ..Default::default()
        };
        // Strict alternation 0, 1, 0, 1, ...
        for k in 0..10 {
            let pos = select_and_child(&state, asid(0), &config);
            assert_eq!(pos, k % 2, "round-robin must rotate in order");
            let child = state.and_stats.child_id(asid(0), pos);
            state.bump_and_round_robin(asid(0));
            state.bump_and_child_visit(child);
        }
        assert_eq!(state.and_stats.child_visits(asid(0)), &[5, 5]);
        assert_eq!(state.and_stat(asid(0)).round_robin, 10);
    }

    /// The round-robin counter is overlay state and advances under every
    /// selector (playout bumps it unconditionally), so switching selectors
    /// mid-session cannot desynchronize pinned overlay expectations.
    #[test]
    fn round_robin_counter_advances_under_value_guided_selectors() {
        for selector in [AndSelector::LctAnd, AndSelector::UctAnd] {
            let mut state = two_child_and_fixture();
            drive_and_selector(&mut state, selector, 7);
            assert_eq!(
                state.and_stat(asid(0)).round_robin,
                7,
                "{selector:?}: the round-robin counter must be maintained regardless of selector"
            );
        }
    }

    /// AND-selector ties resolve to the smallest child index: two identical
    /// children give identical scores, and the first strict maximum wins.
    #[test]
    fn and_selector_ties_resolve_to_smallest_index() {
        let mut state: McgsState = McgsState::new();
        for _ in 0..2 {
            push_or(
                &mut state,
                OrStatsData {
                    initial_value: 5.0,
                    value: 5.0,
                    min_size: 1.0,
                    max_size: 2.0,
                    terminal: false,
                    edge_visits: vec![0],
                    edge_and: vec![None],
                    edge_bounds: vec![0; 1],
                },
            );
        }
        push_and(
            &mut state,
            AndStatsData {
                parent: os(0),
                parent_slot: 0,
                op: crate::id::OpId::from_usize(0),
                commutative: false,
                value: f64::INFINITY,
                child_or_stats: vec![os(0), os(1)],
                child_counts: vec![1, 1],
                child_visits: vec![0, 0],
                round_robin: 0,
                transport_rows: Vec::new(),
                transport_cols: Vec::new(),
                transport_cell_map: Vec::new(),
            },
        );
        for selector in [AndSelector::LctAnd, AndSelector::UctAnd] {
            let config = McgsConfig {
                and_selector: selector,
                ..Default::default()
            };
            assert_eq!(
                select_and_child(&state, asid(0), &config),
                0,
                "{selector:?}: ties must resolve to the smallest child index"
            );
        }
    }

    /// End-to-end oracle equality under every AND selector: on a small
    /// instance each selector certifies Exact and matches the exact solver.
    #[test]
    fn mcgs_matches_exact_under_every_and_selector() {
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

        for selector in [
            AndSelector::RoundRobin,
            AndSelector::UctAnd,
            AndSelector::LctAnd,
        ] {
            let config = McgsConfig {
                playouts: 500,
                cycle_mode: CycleMode::AncestorOnly,
                and_selector: selector,
                ..Default::default()
            };
            let (mcgs_term, mcgs_pool, completion, _) = run_mcgs(&snap, lc, rc, &config).unwrap();
            assert_eq!(
                mcgs_pool.size(mcgs_term),
                exact_size,
                "{selector:?}: MCGS must match the exact optimum"
            );
            assert_eq!(
                completion,
                super::super::session::Completion::Exact,
                "{selector:?}: this tiny graph must certify within 500 playouts"
            );
        }
    }

    /// The closed bit under every AND selector, including round robin, whose
    /// rotation gets its own skip. The certificate must still be the exact
    /// optimum, and it must arrive no later than the flag-off run's — here the
    /// graph closes in a handful of playouts either way, so the budget is set
    /// to the flag-off knee rather than to 500. In a debug build this also
    /// exercises the oracle assert in `run_mcgs_in`: the root's bit has to
    /// agree with `is_structurally_complete` on every one of these runs.
    #[test]
    fn closed_bit_certifies_under_every_and_selector() {
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

        for selector in [
            AndSelector::RoundRobin,
            AndSelector::UctAnd,
            AndSelector::LctAnd,
        ] {
            // The smallest ladder budget that certifies without the flag.
            let knee = (0..)
                .map(|k| 1u64 << k)
                .take(12)
                .find(|&playouts| {
                    let config = McgsConfig {
                        playouts,
                        and_selector: selector,
                        ..Default::default()
                    };
                    let (_, _, completion, _) = run_mcgs(&snap, lc, rc, &config).unwrap();
                    completion == super::super::session::Completion::Exact
                })
                .expect("the flag-off run certifies this graph inside the ladder");

            let config = McgsConfig {
                playouts: knee,
                and_selector: selector,
                closed_bit: true,
                ..Default::default()
            };
            let (term, pool, completion, _) = run_mcgs(&snap, lc, rc, &config).unwrap();
            assert_eq!(
                pool.size(term),
                exact_size,
                "{selector:?}: the closed bit must not cost quality"
            );
            assert_eq!(
                completion,
                super::super::session::Completion::Exact,
                "{selector:?}: the closed bit must not certify later than the flag-off run \
                 (knee {knee})"
            );
        }
    }

    /// Fixture for the closed bit's write-through tests: `f(a,b)` vs `f(a,c)`,
    /// which certifies in a few hundred playouts.
    fn write_through_fixture() -> (
        EGraph31<NiraLitVal, false, false>,
        crate::id::ENodeId,
        crate::id::ENodeId,
    ) {
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
        (eg, fab, fac)
    }

    /// The closure proof outlives the statistics that produced it. A run with
    /// the flag on marks every closed node exact in the results table; a
    /// second run on the same session layers with a *fresh* statistics overlay
    /// finds the root terminal at creation and certifies without spending a
    /// playout. Without the flag there is no proof to inherit, and the same
    /// zero-budget run cannot certify.
    #[test]
    fn closed_bit_write_through_certifies_the_next_run() {
        let (eg, fab, fac) = write_through_fixture();
        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(fab).unwrap();
        let rc = snap.class_of(fac).unwrap();

        for closed_bit in [true, false] {
            let mut space = SearchSpace::new(CycleMode::AncestorOnly);
            let mut pool = TermPool::new();
            let mut cache = ActionCache::without_ac_actions(usize::MAX);
            let mut results = BestResults::new();
            let mut first = McgsState::new();
            let config = McgsConfig {
                playouts: 500,
                closed_bit,
                ..Default::default()
            };
            let (term, completion) = run_mcgs_in(
                &snap,
                &mut space,
                &mut pool,
                &mut cache,
                &mut results,
                &mut first,
                lc,
                rc,
                &config,
            )
            .unwrap();
            assert_eq!(completion, super::super::session::Completion::Exact);

            let mut second = McgsState::new();
            let (reused, completion) = run_mcgs_in(
                &snap,
                &mut space,
                &mut pool,
                &mut cache,
                &mut results,
                &mut second,
                lc,
                rc,
                &McgsConfig {
                    playouts: 0,
                    ..config.clone()
                },
            )
            .unwrap();
            if closed_bit {
                assert_eq!(
                    completion,
                    super::super::session::Completion::Exact,
                    "the marked-exact root must certify at zero playouts"
                );
                assert_eq!(pool.quality(reused), pool.quality(term));
            } else {
                assert_eq!(
                    completion,
                    super::super::session::Completion::BudgetExhausted { playouts_used: 0 },
                    "without the write-through there is no proof to inherit"
                );
            }
        }
    }

    /// The proof is overlay state like everything else: restoring the session
    /// layers past the run that produced it takes the exact flag with it.
    #[test]
    fn closed_bit_write_through_rolls_back() {
        let (eg, fab, fac) = write_through_fixture();
        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(fab).unwrap();
        let rc = snap.class_of(fac).unwrap();

        let mut space = SearchSpace::new(CycleMode::AncestorOnly);
        let mut pool = TermPool::new();
        let mut cache = ActionCache::without_ac_actions(usize::MAX);
        let mut results = BestResults::new();
        let mut state = McgsState::new();

        let space_token = space.mark();
        let pool_token = pool.mark();
        let results_token = results.mark();
        let cache_token = cache.mark();
        let state_token = state.mark();

        let config = McgsConfig {
            playouts: 500,
            closed_bit: true,
            ..Default::default()
        };
        let (_, completion) = run_mcgs_in(
            &snap,
            &mut space,
            &mut pool,
            &mut cache,
            &mut results,
            &mut state,
            lc,
            rc,
            &config,
        )
        .unwrap();
        assert_eq!(completion, super::super::session::Completion::Exact);

        let empty = space.contexts.empty();
        let (root_or, _) = space.get_or_insert_or_node(
            lc,
            rc,
            empty,
            empty,
            snap.best_size(lc),
            snap.best_size(rc),
        );
        assert!(
            results.is_exact(root_or),
            "the closed root must be marked exact"
        );

        state.restore(state_token);
        cache.restore(cache_token);
        results.restore(results_token);
        pool.restore(pool_token);
        space.restore(space_token);
        assert!(
            !results.is_exact(root_or),
            "the restore must take the closure proof with it"
        );

        // And the search is genuinely back to square one: a zero-budget run
        // certifies nothing.
        let mut fresh = McgsState::new();
        let (_, completion) = run_mcgs_in(
            &snap,
            &mut space,
            &mut pool,
            &mut cache,
            &mut results,
            &mut fresh,
            lc,
            rc,
            &McgsConfig {
                playouts: 0,
                ..config.clone()
            },
        )
        .unwrap();
        assert_eq!(
            completion,
            super::super::session::Completion::BudgetExhausted { playouts_used: 0 }
        );
    }

    /// Shared subproblem: `f(a,a)` vs `f(b,b)` reaches AU(a,b) through two
    /// child positions of the same action, so its closure has to be accounted
    /// once per position. The root closes and the run stops early.
    #[test]
    fn closed_bit_certifies_a_shared_child() {
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

        let (plain, _, plain_completion) = {
            let config = McgsConfig {
                playouts: 200,
                ..Default::default()
            };
            let (term, pool, completion, _) = run_mcgs(&snap, lc, rc, &config).unwrap();
            (pool.size(term), pool, completion)
        };
        let config = McgsConfig {
            playouts: 200,
            closed_bit: true,
            ..Default::default()
        };
        let (term, pool, completion, _) = run_mcgs(&snap, lc, rc, &config).unwrap();
        assert_eq!(plain_completion, super::super::session::Completion::Exact);
        assert_eq!(completion, super::super::session::Completion::Exact);
        assert_eq!(pool.size(term), plain);
    }

    #[test]
    fn mcgs_unmarked_mutations_do_not_accumulate_history() {
        let mut state: McgsState = McgsState::new();
        push_or(
            &mut state,
            OrStatsData {
                initial_value: 1.0,
                value: 1.0,
                min_size: 1.0,
                max_size: 1.0,
                terminal: false,
                edge_visits: Vec::new(),
                edge_and: Vec::new(),
                edge_bounds: Vec::new(),
            },
        );

        for value in 2..=1_001 {
            state.set_or_value(os(0), value as f64);
        }
        assert_eq!(
            state.or_stats.value.diff_log_len(),
            0,
            "without a live mark, VecP must not accumulate restore history"
        );
    }

    /// Run `body` on a separate thread and fail the test if it does not
    /// finish within `timeout`. A watchdog is the only way a hang surfaces as
    /// a test failure instead of a stuck CI job: the D1 defect class (f64
    /// transport costs feeding SPFA) spun forever inside a library call.
    fn assert_terminates(
        timeout: std::time::Duration,
        name: &str,
        body: impl FnOnce() + Send + 'static,
    ) {
        let (tx, rx) = std::sync::mpsc::channel();
        let handle = std::thread::spawn(move || {
            body();
            let _ = tx.send(());
        });
        match rx.recv_timeout(timeout) {
            Ok(()) => handle.join().expect("watchdog body panicked"),
            Err(_) => panic!("{name} did not terminate within {timeout:?}"),
        }
    }

    /// D1 regression: the five-node graph whose transport-AND Q costs made
    /// the former f64 SPFA relax a negative residual cycle forever. The
    /// quantized integer solve must return; the exact solver answers the same
    /// pair in under a millisecond, so 60 seconds is generous for 3000
    /// playouts.
    #[test]
    fn uct_terminates_on_shared_subterm_unit_mset_graph() {
        assert_terminates(
            std::time::Duration::from_secs(60),
            "anti_unify(n4, n8) under UCT with 3000 playouts",
            || {
                let mut eg = EGraph31::<NiraLitVal, false, false>::new();
                let int = eg.intern_sort("Int");
                let k0_op = eg.register_op0("k0", int);
                let k1_op = eg.register_op0("k1", int);
                let k2_op = eg.register_op0("k2", int);
                let k3_op = eg.register_op0("k3", int);
                let u_op = eg.register_op1("u", int, int);
                let f_op = eg.register_op2("f", int, int, int);
                let plus_op = eg.register_mset("plus", int, int);
                let and_op = eg.register_set("and", int, int);

                let k0 = eg.add(k0_op, &[]);
                let k1 = eg.add(k1_op, &[]);
                let k2 = eg.add(k2_op, &[]);
                let k3 = eg.add(k3_op, &[]);
                eg.set_unit_node(plus_op, k0);
                eg.set_unit_node(and_op, k1);

                let n4 = eg.add(u_op, &[k2]);
                let n5 = eg.add(f_op, &[n4, k0]);
                let n6 = eg.add(and_op, &[n5, k3]);
                let n7 = eg.add(plus_op, &[n6, n6]);
                let n8 = eg.add(plus_op, &[n7, k3]);
                eg.rebuild();

                let snap = AuSnapshot::new(&eg).unwrap();
                let lc = snap.class_of(n4).unwrap();
                let rc = snap.class_of(n8).unwrap();

                let config = McgsConfig {
                    playouts: 3000,
                    cycle_mode: CycleMode::AncestorOnly,
                    ..Default::default()
                };
                let (term, pool, _, _) = run_mcgs(&snap, lc, rc, &config).unwrap();
                assert!(pool.size(term) >= 1);
            },
        );
    }

    /// UCT terminates over the randomized graph
    /// distribution (leaves, u/1, f/2, mset and set operators with units,
    /// random merges) at reduced case count. Only termination is asserted;
    /// result quality is covered by the differential tests.
    #[test]
    fn uct_terminates_on_random_unit_mset_set_graphs() {
        assert_terminates(
            std::time::Duration::from_secs(120),
            "randomized UCT termination sweep",
            || {
                let mut seed: u64 = 0x9E3779B97F4A7C15;
                let mut next = move || {
                    seed ^= seed << 13;
                    seed ^= seed >> 7;
                    seed ^= seed << 17;
                    seed
                };
                for _case in 0..30 {
                    let mut eg = EGraph31::<NiraLitVal, false, false>::new();
                    let int = eg.intern_sort("Int");
                    let leaf_ops = [
                        eg.register_op0("k0", int),
                        eg.register_op0("k1", int),
                        eg.register_op0("k2", int),
                        eg.register_op0("k3", int),
                    ];
                    let u_op = eg.register_op1("u", int, int);
                    let f_op = eg.register_op2("f", int, int, int);
                    let plus_op = eg.register_mset("plus", int, int);
                    let and_op = eg.register_set("and", int, int);

                    let mut nodes: Vec<_> = leaf_ops.iter().map(|&op| eg.add(op, &[])).collect();
                    eg.set_unit_node(plus_op, nodes[0]);
                    eg.set_unit_node(and_op, nodes[1]);

                    let extra = 4 + (next() % 5) as usize;
                    for _ in 0..extra {
                        let a = nodes[(next() as usize) % nodes.len()];
                        let b = nodes[(next() as usize) % nodes.len()];
                        let node = match next() % 4 {
                            0 => eg.add(u_op, &[a]),
                            1 => eg.add(f_op, &[a, b]),
                            2 => eg.add(plus_op, &[a, b]),
                            _ => eg.add(and_op, &[a, b]),
                        };
                        nodes.push(node);
                    }
                    for _ in 0..(next() % 3) {
                        let a = nodes[(next() as usize) % nodes.len()];
                        let b = nodes[(next() as usize) % nodes.len()];
                        eg.merge(a, b);
                    }
                    eg.rebuild();

                    let Ok(snap) = AuSnapshot::new(&eg) else {
                        continue;
                    };
                    let l = nodes[(next() as usize) % nodes.len()];
                    let r = nodes[(next() as usize) % nodes.len()];
                    let (Some(lc), Some(rc)) = (snap.class_of(l), snap.class_of(r)) else {
                        continue;
                    };
                    let config = McgsConfig {
                        playouts: 200,
                        cycle_mode: CycleMode::AncestorOnly,
                        ..Default::default()
                    };
                    // Termination is the property; an Err (for example a class
                    // without a finite representative) also terminates.
                    let _ = run_mcgs(&snap, lc, rc, &config);
                }
            },
        );
    }
}
