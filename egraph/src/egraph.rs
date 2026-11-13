// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The semi-persistent e-graph: add, merge, find, rebuild, mark, restore.

use crate::canon::{MSetCanon, VarCanon};
use crate::classes::EClasses;
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::containers::IndexLike;
use crate::containers::ShrinkPolicy;
use crate::containers::error::ContainerError;
use crate::literal::{LitVal, LitValStore};
use crate::multiplicity::{MultOverflow, MultiplicityLike};
use crate::node_store::{Added, NodeStore};
use crate::registry::{AxiomRegistry, OpKind, OpRegistry, RuleRegistry, SortRegistry};
use crate::typed_routing::NodeRef;
use crate::union_find::{Justification, ProofBuf};

#[cfg(debug_assertions)]
pub mod cc_mirror;

/// How a completion op's monomial counts are bounded during normalization (design "three
/// independent axes"): unbounded ℕ (MSet plain AC), clamped to {0,1} by dedup (Set idempotent =
/// ACI), or reduced mod `order` (nilpotent, e.g. XOR at order 2 — stored MSet, the clamp is the
/// algebra axis, not the storage axis). Selects the normalize/reduct
/// reduction in `cc_round`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CompletionClamp {
    Multiset,
    Idempotent,
    Nilpotent { order: u8 },
}

#[derive(Clone, Copy, Debug)]
pub struct EGraphToken {
    /// One `GroupToken` names the whole synchronized member set's version; the
    /// e-graph's `History` is the single validity authority (doc 10). The
    /// per-member token structs live in the e-graph's internal depth-indexed
    /// stacks, not here.
    group: crate::containers::history::GroupToken,
    /// The completion outcome at mark time. `mark()` rebuilds first, so this value
    /// describes exactly the state being snapshotted; `restore` puts it back so a caller
    /// can never observe an outcome from a discarded scope.
    completion_outcome: Option<CompletionOutcome>,
    /// The proof-mode tables' lengths at mark time (see `rule_marks`).
    rule_len: ProofLens,
}

/// The lengths of the append-only proof-mode tables at a mark.
#[derive(Clone, Copy, Debug, Default)]
struct ProofLens {
    rule_starts: usize,
    rule_premises: usize,
    creation_log: usize,
    build_starts: usize,
    build_premises: usize,
    merge_premise_pairs: usize,
    merge_premise_log: usize,
}

/// Live-node threshold under which mark/restore stay sequential (see
/// [`EGraph::fanout_enabled`]): below it the scope dispatch costs more than the
/// members' mark/restore work.
pub const PAR_NODE_MIN: usize = 1 << 14;

/// Fan-out observability: total spawned member closures and a bitset of the
/// rayon worker indices they ran on. The differential test reads these to
/// assert the parallel path actually spawned rather than degenerating to the
/// caller's thread; a saturating bitset (indices past 63 fold into bit 63)
/// still distinguishes one worker from several.
static FANOUT_SPAWNS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static FANOUT_WORKERS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

pub(crate) fn fanout_witness() {
    use std::sync::atomic::Ordering;
    FANOUT_SPAWNS.fetch_add(1, Ordering::Relaxed);
    let idx = rayon::current_thread_index().unwrap_or(0).min(63);
    FANOUT_WORKERS.fetch_or(1u64 << idx, Ordering::Relaxed);
}

/// Read and reset the fan-out witness: `(spawned closures, distinct workers)`.
pub fn take_fanout_witness() -> (usize, u32) {
    use std::sync::atomic::Ordering;
    let spawns = FANOUT_SPAWNS.swap(0, Ordering::Relaxed);
    let workers = FANOUT_WORKERS.swap(0, Ordering::Relaxed).count_ones();
    (spawns, workers)
}

/// Mark/restore wall-clock accounting, on only under `SEMPER_PROF` so the
/// live path pays nothing beyond one static bool read. Drives the profile
/// that decides whether corpus-level parallel gains are reachable: if
/// mark+restore is a small fraction of solve time, a neutral corpus wall is
/// the expected outcome, not a defect.
static PROF_ON: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| std::env::var_os("SEMPER_PROF").is_some());
static MARK_NS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static MARK_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static RESTORE_NS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static RESTORE_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn prof_record(
    ns: &std::sync::atomic::AtomicU64,
    calls: &std::sync::atomic::AtomicU64,
    t: std::time::Instant,
) {
    use std::sync::atomic::Ordering;
    ns.fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
    calls.fetch_add(1, Ordering::Relaxed);
}

/// Read and reset the profile: `(mark ns, mark calls, restore ns, restore calls)`.
/// All zeros unless `SEMPER_PROF` is set.
pub fn take_markrestore_profile() -> (u64, u64, u64, u64) {
    use std::sync::atomic::Ordering;
    (
        MARK_NS.swap(0, Ordering::Relaxed),
        MARK_CALLS.swap(0, Ordering::Relaxed),
        RESTORE_NS.swap(0, Ordering::Relaxed),
        RESTORE_CALLS.swap(0, Ordering::Relaxed),
    )
}

/// Per-member restore accounting (SEMPER_RESTORE_PROF): which member inside
/// one `restore` the time goes to. Sequential path only (the fan-out
/// interleaves members, so per-member walls would not add up).
static RESTORE_PROF_ON: std::sync::LazyLock<bool> =
    std::sync::LazyLock::new(|| std::env::var_os("SEMPER_RESTORE_PROF").is_some());
pub const RESTORE_PROF_MEMBERS: [&str; 8] = [
    "classes", "nodes", "sorts", "ops", "rules", "axioms", "lits", "maps",
];
static RESTORE_MEMBER_NS: [std::sync::atomic::AtomicU64; 8] = [
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
    std::sync::atomic::AtomicU64::new(0),
];

fn restore_prof_record(member: usize, t: std::time::Instant) {
    RESTORE_MEMBER_NS[member].fetch_add(
        t.elapsed().as_nanos() as u64,
        std::sync::atomic::Ordering::Relaxed,
    );
}

/// Read and reset the per-member restore nanoseconds, indexed as
/// [`RESTORE_PROF_MEMBERS`]. All zeros unless `SEMPER_RESTORE_PROF` is set.
pub fn take_restore_member_profile() -> [u64; 8] {
    let mut out = [0u64; 8];
    for (i, c) in RESTORE_MEMBER_NS.iter().enumerate() {
        out[i] = c.swap(0, std::sync::atomic::Ordering::Relaxed);
    }
    out
}

pub struct EGraph<
    Cfg: EGraphConfig,
    L: LitVal,
    const TRACK: bool = true,
    const PROOFS: bool = false,
> where
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    sorts: SortRegistry<Cfg::S, TRACK>,
    ops: OpRegistry<Cfg::O, Cfg::S, TRACK>,
    rules: RuleRegistry<TRACK>,
    axioms: AxiomRegistry<Cfg::G, TRACK>,
    lits: LitValStore<L, Cfg::V, TRACK>,
    classes: EClasses<Cfg::G, Cfg::ClassKey, Cfg::UL, Cfg::UN, TRACK, PROOFS, Cfg::Policy>,
    nodes: NodeStore<Cfg::G, Cfg::O, Cfg::V, Cfg::C, Cfg::Ids, TRACK, PROOFS, Cfg::Policy>,
    /// The ONE genealogy for the whole synchronized member set (doc 10): a
    /// group token's validity and the branch cuts are recorded here once,
    /// instead of once per member vector. Sole authority for restore validity.
    history: crate::containers::history::History,
    worklist: Vec<(Cfg::UL, Cfg::G)>,
    collisions: Vec<(Cfg::G, Cfg::G)>,
    /// Degenerate-arity merges `recanonize_parent` found (a node whose
    /// normal form is one child's class, or the unit): merged beside the
    /// hash-cons collisions, but justified as `Normalize`, because their
    /// premises are the node's children and the operator's laws, not a second
    /// node's children.
    normalizations: Vec<(Cfg::G, Cfg::G)>,
    /// Set by the saturation loops between a round's index build and its
    /// end: creation evidence then leaves its merges on the worklist instead
    /// of closing congruence at once (see `merge_creation_collisions`).
    round_open: bool,
    /// EUF-derived merges captured for Nelson-Oppen equality export, recorded
    /// only when `record_merges` is set. Each entry is a `(survivor, absorbed)`
    /// class-root pair as of merge time, teed from the single `merge_in_classes`
    /// chokepoint so direct, congruence, and completion merges are all caught.
    /// The caller drains it with `take_merged_log` before every decision-level
    /// advance, so it holds at most one level's merges and needs no
    /// semi-persistent backtracking: `restore` clears it.
    merged_log: Vec<(Cfg::G, Cfg::G)>,
    /// Rule instances (`PROOFS` only): instance `i` owns the premise pairs
    /// `rule_premises[rule_starts[i]..rule_starts[i + 1]]` (the last one runs
    /// to the end), each a pair of nodes the instance needs equal. Append-only
    /// between marks: a mark records both lengths in `rule_marks`, and
    /// restore truncates to them, so an instance of a discarded scope never
    /// survives it.
    rule_starts: Vec<usize>,
    rule_premises: Vec<(Cfg::G, Cfg::G)>,
    /// Instance `i` could not pair some pattern position with a child of the
    /// matched node (a flattened view, a collected sequence): its premise list
    /// is incomplete, and `rewrite_premises` reports it as unknown.
    rule_partial: Vec<bool>,
    /// The instance premise notes append to, while a rule's actions run.
    rule_open: Option<u32>,
    /// One `ProofLens` per open scope.
    rule_marks: Vec<ProofLens>,
    /// Proof mode: the node `add_with_creation_evidence` built for a client
    /// term `(op, given children)` that it could not hash-cons (a fresh node
    /// over non-root children, or a flagged duplicate of a node with history).
    /// Such a node is not reachable through the hash-cons table, so without
    /// this map every later build of the same term made another one: a rule
    /// whose right-hand side re-fires each round grew its class by one copy
    /// per round, and AC matching enumerated every combination of copies
    /// (`ac_lazy_alternation.egg` exceeded 2 GB with `--proofs`).
    creation_memo: std::collections::HashMap<(Cfg::O, Vec<(Cfg::G, usize)>), Cfg::G>,
    /// Insertion order of `creation_memo`, so restore can drop a scope's entries.
    creation_log: Vec<(Cfg::O, Vec<(Cfg::G, usize)>)>,
    /// Proof mode: the splice witnesses of `Build` steps. Build `i` owns
    /// `build_premises[build_starts[i]..build_starts[i + 1]]`, each a
    /// `(child, spliced node)` pair recorded by the flatten helpers. A table of
    /// its own, because a right-hand side builds terms while its rule instance
    /// is still open in `rule_premises`.
    build_starts: Vec<usize>,
    build_premises: Vec<(Cfg::G, Cfg::G)>,
    /// Build `i` collapsed under the operator's laws to a class (one child's, or
    /// the unit's) rather than storing a node: the step relates the client's
    /// term to that class, not to the children of the node that represents it.
    build_collapsed: Vec<bool>,
    /// Set by the n-ary build paths when normalization returns a class instead
    /// of a node (`Normal::Single`, `Normal::Unit`).
    last_build_collapsed: bool,
    /// Set while a proof-mode n-ary build runs, so the flatten helpers record
    /// their splices in `flatten_witness`.
    record_flatten: bool,
    flatten_witness: Vec<(Cfg::G, Cfg::G)>,
    /// Set while a build must not make evidence nodes: the canonical build inside
    /// an evidence build, and completion's own monomials, which are not client
    /// terms.
    no_evidence: bool,
    /// Set for one merge: the class root that must survive it. A `Build` merge
    /// keeps the canonical node's root, so an evidence node never becomes the
    /// representative that later builds store as a child.
    force_survivor: Option<Cfg::G>,
    /// Proof mode: the premises of the steps whose children `explain_deep`
    /// pairs by class (unordered congruence, `Normalize`, `Build`), computed
    /// from the classes just before the merge and keyed by the merged pair.
    /// Pairing by the classes at explanation time would also pair children
    /// that became equal only through this step or a later one, and the
    /// explanation would cite a conclusion as its own premise.
    merge_premise_index: std::collections::HashMap<(usize, usize), (usize, usize)>,
    merge_premise_pairs: Vec<(Cfg::G, Cfg::G)>,
    merge_premise_log: Vec<(usize, usize)>,
    /// Proof mode: the premises the next merge records instead of computing grouped
    /// ones, set by a completion step that knows the rules it used.
    pending_premises: Option<Vec<(Cfg::G, Cfg::G)>>,
    /// Gate for `merged_log`. Off by default, so EUF-only runs record nothing;
    /// the adapter enables it via `set_record_merges`.
    record_merges: bool,
    /// Reusable scratch for a node's child ids as bare `G` (the canonical-children buffer for
    /// every representation except MSet). Paired with `mset_buf`, which holds the MSet variant.
    g_buf: Vec<Cfg::G>,
    /// Reusable scratch for MSet children, child type `C` = `(G, mult)` (the multiset
    /// representation needs the multiplicity that bare `G` in `g_buf` cannot carry).
    mset_buf: Vec<Cfg::C>,
    /// `add`'s child list as `(class, multiplicity)` pairs, the form
    /// `crate::nary_canon::normalize` reads.
    pair_buf: Vec<(Cfg::G, Cfg::M)>,
    /// Semi-naive touched log: node ids created or recanonicalized since the
    /// last `clear_touched`. Round-local scratch (cleared on `restore`);
    /// drives the per-round delta index. Not part of persistent state.
    touched: Vec<Cfg::G>,
    /// When set, every class merge also records the absorbed side's member
    /// nodes in `touched` (see `merge_in_classes`). Only semi-naive saturation
    /// consumes it; off everywhere else so merges pay no ring walk.
    track_merge_members: bool,
    /// Whether the index build honours `FLAG_UNMATCHABLE` (see
    /// [`set_matching_shield`](Self::set_matching_shield)). Runtime switch, not
    /// semi-persistent: a relevancy client toggles it per matching round.
    matching_shield: bool,
    /// Survivor policy for class merges (see [`UnionBy`]).
    union_by: UnionBy,
    /// Set by a completion round that met a multiplicity past the configured width;
    /// `rebuild` then stops completion with [`CompletionOutcome::AbortedOverflow`].
    cc_overflow: bool,
    /// A multiplicity past the configured width met during `rebuild` (recanonization or
    /// completion): the node it belongs to is not representable, so the caller reports
    /// it ([`take_width_error`](EGraph::take_width_error)) and stops.
    width_error: Option<MultOverflow>,
    /// Right-hand-side actions skipped since the last `take_no_value` because their term
    /// had no value (`apply::NO_VALUE`).
    no_value: usize,
    /// Set by [`EGraph::node_monomial_into`], a `&self` read, when coalescing a node's
    /// children after merges passes the width (two counted children of one node in classes
    /// a union joined). Folded into `width_error` by the next check: atomic so a shared
    /// read can record it and the e-graph stays `Sync`.
    monomial_overflow: std::sync::atomic::AtomicBool,
    /// Counts the events that change how a build spells an AC term: a class holding a
    /// completion monomial turns `atomic` (the build stops splicing it), a merge changes
    /// a class's minimal monomial for an op (the build splices a different monomial), or
    /// a rebuild applies a law to a stored n-ary node beyond `find` (a unit drop, a count
    /// clamp, a degenerate arity: `VarCanon::law_applied`), after which a right-hand side
    /// built through that node's class has another value while the node that holds the
    /// match is untouched (`proofs/lean/SemperProofs/Fidelity/Recanon.lean`,
    /// `denN_persist_fails`). None of these events enters the semi-naive delta; the semi-naive
    /// loop reads this counter instead and, in plain mode, re-matches in full the rules
    /// whose right-hand side builds an AC term (design §9.2, "A build-time choice the delta
    /// cannot see"). Monotone, and not rolled back by `restore`: a spurious increase only
    /// costs a full match.
    spelling_epoch: u64,
    /// Goal pair for goal-directed completion (the lazy-check transaction):
    /// the completion loop polls it between passes and inside a round's apply
    /// loops, and stops with [`CompletionOutcome::GoalMet`] as soon as the
    /// two classes join. `None` everywhere else.
    cc_goal: Option<(Cfg::G, Cfg::G)>,
    /// Node count at the start of the current completion run, for the
    /// in-round budget check (`cc_should_stop`): a single blown-up round is
    /// stopped mid-apply instead of only between rounds. Inside a lazy decision
    /// it is the decision's own start (`decision_start`), so the budget is
    /// cumulative over the decision.
    cc_start_nodes: usize,
    /// Node count when the current lazy decision opened
    /// ([`open_decision_budget`](Self::open_decision_budget)), `None` outside one.
    /// While set, `completion_node_budget` counts every node minted since that point,
    /// by rule applications and by completion alike: each completion `rebuild`
    /// measures its growth from here instead of from its own start, and the
    /// saturation apply loops stop once the count passes it
    /// ([`decision_budget_exhausted`](Self::decision_budget_exhausted)).
    decision_start: Option<usize>,
    /// Set when a completion `rebuild` inside the open lazy decision stopped on a budget
    /// (node growth or round work). The decision is inconclusive from then on, so the
    /// saturation loops stop at their next check instead of growing the graph further.
    decision_spent: bool,
    /// Work budget for one completion round, in rule containment tests (the
    /// normalizers' `find_applicable` and the round's reducibility pass). A round past
    /// it stops and `rebuild` reports [`CompletionOutcome::AbortedWorkLimit`]. Like
    /// `completion_node_budget`, a resource backstop and a config knob, not
    /// semi-persistent state; default [`DEFAULT_COMPLETION_WORK_BUDGET`].
    completion_work_budget: u64,
    /// Set by a completion round that passed `completion_work_budget`: the work it had
    /// spent. `rebuild` takes it and reports the abort.
    cc_work_stop: Option<u64>,
    /// Whether `rebuild` runs the AC congruence-completion pass (superposition +
    /// inter-reduction). **Default off** because ground AC completion is doubly
    /// exponential in the worst case. The growth backstop is checked between rounds and
    /// inside the apply loops, but a bounded node count does not make the algorithm cheap.
    /// See `doc/future/ac-completion-limitations.md` section 1. Opt in with
    /// [`set_cc`](Self::set_cc).
    cc: bool,
    /// Whether `rebuild` runs the AC reduced-basis invariant checks (`cc_basis_dump`:
    /// `min_monomial` minimality, the Kapur-reduced antichain, etc., see `ac_invariants.rs`).
    /// **Default off** and only consulted when `cc` is on: the ground-truth checks
    /// brute-force per-class minima and multi-step normalization (superlinear), so they are
    /// diagnostic/test-only, never on the production hot path. Seeded from the `AC_BASIS_DUMP`
    /// env var at construction (so existing diagnostic runs keep working) and overridable via
    /// [`set_basis_checks`](Self::set_basis_checks).
    basis_checks: bool,
    /// Reusable scratch for comparing two nodes' AC monomials (`monomial_cmp` on the
    /// per-class `min_monomial`, §9a). Two buffers to hold both sides without aliasing;
    /// cleared and refilled per comparison, never grown per merge.
    cmp_buf_a: Vec<(Cfg::G, Cfg::M)>,
    /// Scratch for `rebuild_congruence`: parents whose span shrank in the absorbed-uses
    /// sweep, refreshed into the min-monomial pool after the sweep releases the use-list
    /// borrow. Round-local, never restored.
    refresh_buf: Vec<Cfg::G>,
    /// Classes whose completion order key a merge lowered (`fold_min_monomial`): the
    /// survivor took the absorbed side's lesser key. Every completion node holding such a
    /// class as a child shrank in the key order with no change to its span, so no
    /// recanonization refreshes it; `rebuild_congruence` refreshes those parents. Cleared
    /// by `restore` with the worklist.
    key_lowered: Vec<Cfg::G>,
    cmp_buf_b: Vec<(Cfg::G, Cfg::M)>,
    /// Reusable scratch for flattening nested same-op AC children (`WF_flat`,
    /// design §6c). Worklist of children still to expand; never grown per add.
    flatten_buf: Vec<Cfg::G>,
    /// The same worklist for an AC (MSet) operator's counted children.
    mset_flatten_buf: Vec<Cfg::C>,
    /// Per-op identity (unit) element node, for completion ops declared with `:identity e`
    /// (`x ∘ e = x`; the unit drops from monomials). Resolved to a real node at registration
    /// (sortcheck has the model to parse the term and builds the node), keyed by op id. Stored
    /// here rather than on `OpKind<S>` because a node id is `Cfg::G`, which `OpKind<S>` cannot
    /// carry. Semi-persistent (its own token), so it rolls back with the op declarations that
    /// created the units. Absent key = the op has no declared identity.
    unit_node: crate::containers::SpUniqueMap<Cfg::O, Cfg::G, <Cfg::O as DenseId>::Index, TRACK>,
    /// Per-op group inverse operator, for AC ops declared with `:inverse neg`
    /// (`x ∘ neg(x) = e`). Resolved to a real op id at registration (sortcheck validates
    /// the unary signature). Same persistence story as `unit_node`. Absent key = no
    /// declared inverse. NOTE: gate-level group support — inverse-PAIR cancellation only,
    /// not Kapur §5.4's full Abelian-group completion (no Gaussian elimination).
    inverse_op: crate::containers::SpUniqueMap<Cfg::O, Cfg::O, <Cfg::O as DenseId>::Index, TRACK>,
    /// Debug mirror of the completion merges: the pending tag of the next merge and the
    /// checker's own reading of the round (`cc_mirror`). Not rolled back by `restore`:
    /// it holds nothing between two completion passes.
    #[cfg(debug_assertions)]
    cc_mirror: cc_mirror::Mirror<Cfg::G, Cfg::O>,
    /// Give a rewrite's AC result a flat alternative for each atomic same-op child
    /// (`--flatten-rhs`); see [`EGraph::same_op_summands`].
    pub flatten_rhs: bool,
    /// Outcome of the most recent `rebuild` when `cc` is enabled. Lets callers distinguish
    /// convergence from a growth-budget abort. `None` if completion hasn't run yet.
    completion_outcome: Option<CompletionOutcome>,
    /// Node-growth budget for one completion-enabled `rebuild`: if completion mints more
    /// than this many nodes beyond where the rebuild started, it stops (sound-but-
    /// incomplete, reported as [`CompletionOutcome::AbortedGrowthLimit`]) rather than
    /// allowing unbounded node growth. This is NOT a termination argument or a complete
    /// work bound; it is the resource backstop described in
    /// `doc/future/ac-completion-limitations.md`. A config knob like
    /// `cc`/`basis_checks`, not
    /// semi-persistent state; default [`DEFAULT_COMPLETION_NODE_BUDGET`], overridable via
    /// [`set_completion_node_budget`](Self::set_completion_node_budget) (tests use a tiny
    /// budget to exercise the abort path directly).
    completion_node_budget: usize,
    /// `(touched.len(), num_classes)` as of the last [`canon_repair_round`](EGraph::canon_repair_round)
    /// that found nothing. While both are unchanged no node was created or recanonicalized
    /// and no classes merged, so the round cannot find anything and is skipped. Transient
    /// scratch, not semi-persistent state: `restore` clears it, so a rolled-back graph is
    /// always rescanned.
    repair_state: Option<(usize, usize)>,
}

/// Default node-growth budget for one completion-enabled `rebuild`, or for one lazy
/// decision (see [`EGraph::set_completion_node_budget`]).
pub const DEFAULT_COMPLETION_NODE_BUDGET: usize = 50_000;

/// Default work budget for one completion round, in rule containment tests (see
/// [`EGraph::set_completion_work_budget`]). The largest round of the test suite,
/// the 200-program `conform-cc` sample included, costs 122,750 tests, so the default
/// is about 800 times above it; at the measured 3 to 10 ns per test a round stops
/// within about a second. `ac_lazy_budget_inconclusive.egg` is the round it stops.
pub const DEFAULT_COMPLETION_WORK_BUDGET: u64 = 100_000_000;

/// Outcome of the AC congruence-completion pass inside `rebuild`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompletionOutcome {
    /// Completion was not enabled (`set_cc(false)`).
    Disabled,
    /// The implemented completion passes reached an unchanged full-round fixpoint.
    ///
    /// This is an operational stopping condition, not by itself a certificate
    /// that the abstract AC/ACI theory is complete.
    ///
    /// For associative-only operators this does not claim completeness for
    /// arbitrary asserted ground equations; that general word problem is
    /// undecidable. See `doc/future/ac-completion-limitations.md` section 8.
    Converged { rounds: usize },
    /// Completion aborted because the node-growth budget was exceeded. The e-graph is
    /// sound-but-incomplete: some AC-entailed equalities may be missing.
    AbortedGrowthLimit { added_nodes: usize, limit: usize },
    /// Completion aborted because one round tested more rules for containment than the
    /// work budget allows ([`EGraph::set_completion_work_budget`]): a round over a large
    /// rule set can cost targets times rules while minting almost nothing, which the
    /// node budget cannot see. Sound-but-incomplete, as for the growth limit.
    AbortedWorkLimit { work: u64, limit: u64 },
    /// Completion stopped because a critical pair or a normal form needed a multiplicity
    /// the configured width cannot hold. The e-graph is a valid plain-congruence-closed
    /// state and incomplete; the overflow is also recorded for the caller to report
    /// ([`EGraph::take_width_error`]).
    AbortedOverflow,
    /// Completion stopped early because the goal pair (`set_cc_goal`) joined.
    /// The e-graph is a valid plain-congruence-closed state; completion is
    /// deliberately unfinished — the caller asked a question and it is
    /// answered. Only the lazy-check transaction sets a goal.
    GoalMet { rounds: usize },
}

impl CompletionOutcome {
    /// Whether completion stopped on a resource budget (node growth or round work)
    /// before its fixpoint: the lazy checks report such a stop as inconclusive.
    pub fn is_budget_stop(self) -> bool {
        matches!(
            self,
            Self::AbortedGrowthLimit { .. } | Self::AbortedWorkLimit { .. }
        )
    }
}

/// Aggregate counts from [`EGraph::dump_all_proofs`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProofDumpStats {
    /// One proof-path record is emitted for every e-node, including representatives.
    pub terms: usize,
    /// Records with at least one proof edge.
    pub nontrivial_proofs: usize,
    /// Total proof edges written across all certificates.
    pub steps: usize,
}

/// Survivor policy for class merges (`--union-by`). `Rank` leaves the choice
/// to the union-find's rank heuristic (the historical default). The directed
/// criteria absorb the cheap side, reading the verified per-class counters:
/// `Size` compares member counts (bounds the semi-naive touched-log pushes to
/// amortized O(n log n) — a node is absorbed at most log n times), `Uses`
/// compares use-list lengths (bounds recanonization work the same way), and
/// `Sum` adds the two, bounding their aggregate movement. Survivor identity is
/// intended to be semantically irrelevant because class payloads are
/// merge-folded (design doc §9a), and finite differential tests compare the
/// policies. This is not an end-to-end equivalence theorem; budget-, goal-, or
/// order-sensitive runs may follow different operational paths.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum UnionBy {
    #[default]
    Rank,
    Size,
    Uses,
    Sum,
}

/// Shortlex order on canonical element lists: shorter first, ties broken
/// element-wise by id. The orientation of the A-only inter-reduction rules
/// (`a_round`); well-founded, so rewriting under it terminates.
fn shortlex<G: crate::containers::DenseId>(a: &[G], b: &[G]) -> std::cmp::Ordering {
    a.len().cmp(&b.len()).then_with(|| {
        a.iter()
            .map(|g| g.to_usize())
            .cmp(b.iter().map(|g| g.to_usize()))
    })
}

/// Type alias for the default 31-bit configuration.
pub type EGraph31<L, const TRACK: bool = true, const PROOFS: bool = false> =
    EGraph<crate::nodes::DefaultConfig, L, TRACK, PROOFS>;

/// Type alias for the 63-bit configuration.
pub type EGraph63<L, const TRACK: bool = true, const PROOFS: bool = false> =
    EGraph<crate::nodes::Config64, L, TRACK, PROOFS>;

/// Type alias for 31-bit ids with a 16-bit multiplicity ([`crate::nodes::ConfigM16`]).
pub type EGraphM16<L, const TRACK: bool = true, const PROOFS: bool = false> =
    EGraph<crate::nodes::ConfigM16, L, TRACK, PROOFS>;

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool> Default
    for EGraph<Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>
    EGraph<Cfg, L, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    pub fn new() -> Self {
        Self {
            sorts: SortRegistry::new(),
            ops: OpRegistry::new(),
            rules: RuleRegistry::new(),
            axioms: AxiomRegistry::new(),
            lits: LitValStore::new(),
            classes: EClasses::new(),
            nodes: NodeStore::new(),
            history: crate::containers::history::History::new(),
            worklist: Vec::new(),
            collisions: Vec::new(),
            normalizations: Vec::new(),
            round_open: false,
            merged_log: Vec::new(),
            rule_starts: Vec::new(),
            rule_premises: Vec::new(),
            rule_partial: Vec::new(),
            rule_open: None,
            rule_marks: Vec::new(),
            creation_memo: std::collections::HashMap::new(),
            creation_log: Vec::new(),
            build_starts: Vec::new(),
            build_premises: Vec::new(),
            build_collapsed: Vec::new(),
            last_build_collapsed: false,
            record_flatten: false,
            flatten_witness: Vec::new(),
            no_evidence: false,
            force_survivor: None,
            merge_premise_index: std::collections::HashMap::new(),
            merge_premise_pairs: Vec::new(),
            merge_premise_log: Vec::new(),
            pending_premises: None,
            record_merges: false,
            g_buf: Vec::new(),
            mset_buf: Vec::new(),
            pair_buf: Vec::new(),
            touched: Vec::new(),
            track_merge_members: false,
            matching_shield: false,
            union_by: UnionBy::Rank,
            cc_overflow: false,
            width_error: None,
            no_value: 0,
            monomial_overflow: std::sync::atomic::AtomicBool::new(false),
            spelling_epoch: 0,
            cc_goal: None,
            cc_start_nodes: 0,
            decision_start: None,
            decision_spent: false,
            completion_work_budget: DEFAULT_COMPLETION_WORK_BUDGET,
            cc_work_stop: None,
            cc: false,
            basis_checks: std::env::var_os("AC_BASIS_DUMP").is_some(),
            cmp_buf_a: Vec::new(),
            refresh_buf: Vec::new(),
            key_lowered: Vec::new(),
            cmp_buf_b: Vec::new(),
            flatten_buf: Vec::new(),
            mset_flatten_buf: Vec::new(),
            unit_node: crate::containers::SpUniqueMap::new(),
            inverse_op: crate::containers::SpUniqueMap::new(),
            #[cfg(debug_assertions)]
            cc_mirror: cc_mirror::Mirror::default(),
            flatten_rhs: false,
            completion_outcome: None,
            completion_node_budget: DEFAULT_COMPLETION_NODE_BUDGET,
            repair_state: None,
        }
    }

    /// Outcome of the most recent `rebuild` when `cc` is enabled. `None` before the first
    /// rebuild. Callers can use this to distinguish convergence from a growth-budget abort.
    pub fn completion_outcome(&self) -> Option<CompletionOutcome> {
        self.completion_outcome
    }

    /// A multiplicity past the configured width met by the last `rebuild`, if any,
    /// cleared by the call. A caller that rebuilds reports it and stops: the node that
    /// needed it was left as it was, so the graph is no longer fully canonical.
    pub fn take_width_error(&mut self) -> Option<MultOverflow> {
        self.has_width_error();
        self.width_error.take()
    }

    /// Whether a multiplicity past the width has been met, folding in one recorded by a
    /// monomial read since the last check.
    fn has_width_error(&mut self) -> bool {
        if self
            .monomial_overflow
            .swap(false, std::sync::atomic::Ordering::Relaxed)
        {
            self.width_error.get_or_insert(MultOverflow);
        }
        self.width_error.is_some()
    }

    /// Set the node-growth budget for one completion-enabled `rebuild` (default
    /// [`DEFAULT_COMPLETION_NODE_BUDGET`]). Exceeding it aborts completion soundly and
    /// records [`CompletionOutcome::AbortedGrowthLimit`]. A config knob (like
    /// [`set_cc`](Self::set_cc)), not semi-persistent state.
    pub fn set_completion_node_budget(&mut self, budget: usize) {
        self.completion_node_budget = budget;
    }

    /// Set the work budget for one completion round, in rule containment tests (default
    /// [`DEFAULT_COMPLETION_WORK_BUDGET`]). Exceeding it aborts completion soundly and
    /// records [`CompletionOutcome::AbortedWorkLimit`]. A config knob, not
    /// semi-persistent state.
    pub fn set_completion_work_budget(&mut self, budget: u64) {
        self.completion_work_budget = budget;
    }

    /// Open a lazy decision's cumulative node budget at the current node count (see the
    /// `decision_start` field). Until [`close_decision_budget`](Self::close_decision_budget),
    /// `completion_node_budget` bounds every node minted since this call, and completion
    /// rebuilds report [`CompletionOutcome::AbortedGrowthLimit`] once it is spent.
    pub fn open_decision_budget(&mut self) {
        self.decision_start = Some(self.node_count());
        self.decision_spent = false;
    }

    /// Close the lazy decision's node budget: completion rebuilds measure from their own
    /// start again.
    pub fn close_decision_budget(&mut self) {
        self.decision_start = None;
        self.decision_spent = false;
    }

    /// Whether the last `rebuild` left the graph at its completion fixpoint: completion
    /// is off ([`CompletionOutcome::Disabled`]), reached its fixpoint
    /// ([`CompletionOutcome::Converged`]), or no rebuild has run. Any other outcome
    /// (a budget stop, an overflow, a goal stop) leaves AC-entailed equalities out of
    /// the graph, and a saturation round that changes nothing on it is no fixpoint.
    ///
    /// This is the engine's side of `EnginePhase.before_fixed` (`K.step Sb = none`,
    /// `proofs/lean/SemperProofs/Fidelity/StopTest.lean`): the stop-test theorems
    /// (`engine_stop_unchanged`, `EnginePhase.rebuild_idle`) apply to a round only when
    /// the snapshot it matched on is a completion fixpoint, so the run loops report
    /// `saturated` through this predicate (`tests/saturation_verdict.rs`).
    pub fn completion_at_fixpoint(&self) -> bool {
        matches!(
            self.completion_outcome,
            None | Some(CompletionOutcome::Disabled | CompletionOutcome::Converged { .. })
        )
    }

    /// Whether the open lazy decision is out of budget: it has minted more nodes than
    /// `completion_node_budget` allows, or one of its completion rebuilds stopped on a
    /// budget. Always false outside a decision. The saturation loops read it after each
    /// round's rebuild and after every rule.
    pub fn decision_budget_exhausted(&self) -> bool {
        self.decision_start.is_some_and(|start| {
            self.decision_spent
                || self.node_count() > start.saturating_add(self.completion_node_budget)
        })
    }

    /// Whether the class holds a completion monomial for some op.
    fn class_has_monomial(&self, repr: Cfg::ClassKey) -> bool {
        self.key_col()
            .is_some_and(|k| (0..k).any(|col| self.classes.min_monomial(repr, col).is_some()))
    }

    /// The count of build-spelling changes (see the `spelling_epoch` field).
    pub fn spelling_epoch(&self) -> u64 {
        self.spelling_epoch
    }

    /// Whether AC completion runs in `rebuild` (any completion mode).
    pub fn cc_enabled(&self) -> bool {
        self.cc
    }

    /// Enable or disable the AC congruence-completion pass in `rebuild` (default off).
    /// See the `cc` field docs and `doc/future/ac-completion-limitations.md` §1.
    pub fn set_cc(&mut self, enabled: bool) {
        self.cc = enabled;
    }

    /// Select the merge survivor policy (see [`UnionBy`]).
    pub fn set_union_by(&mut self, u: UnionBy) {
        self.union_by = u;
    }

    /// The weight the `--union-by` criterion assigns to the class of repr `r`.
    fn union_weight(&self, r: Cfg::G) -> usize {
        let Some(k) = self.classes.repr_id(r) else {
            return 0;
        };
        match self.union_by {
            UnionBy::Rank => 0,
            UnionBy::Size => self.classes.class_size(k),
            UnionBy::Uses => self.classes.use_list_len(k),
            UnionBy::Sum => self
                .classes
                .class_size(k)
                .saturating_add(self.classes.use_list_len(k)),
        }
    }

    /// Set or clear the completion goal pair (see the `cc_goal` field). With a
    /// goal set, `rebuild` under completion returns
    /// [`CompletionOutcome::GoalMet`] as soon as the pair joins, without
    /// finishing the closure.
    pub fn set_cc_goal(&mut self, goal: Option<(Cfg::G, Cfg::G)>) {
        self.cc_goal = goal;
    }

    /// Goal-directed early stop for the completion loops: the goal pair
    /// joined, or the in-round node budget is exhausted (counted from the open lazy
    /// decision's start, if any). `rebuild` sorts out which of the two happened.
    fn cc_should_stop(&self) -> bool {
        if let Some((a, b)) = self.cc_goal
            && self.classes.find_const(a) == self.classes.find_const(b)
        {
            return true;
        }
        self.node_count()
            > self
                .cc_start_nodes
                .saturating_add(self.completion_node_budget)
    }

    /// Enable or disable the AC reduced-basis invariant checks in `rebuild` (default off,
    /// seeded from the `AC_BASIS_DUMP` env var). When on (and `cc` is on), each
    /// completion round prints `cc_basis_dump`, which runs the ground-truth checkers
    /// (`min_monomial` minimality, Kapur-reducedness). These are superlinear brute-force checks,
    /// so leave this off outside diagnosis and tests. See `ac_invariants.rs`.
    pub fn set_basis_checks(&mut self, enabled: bool) {
        self.basis_checks = enabled;
    }

    /// Create an e-graph with built-in sorts and reserved op names from a `LitModel`.
    pub fn from_model(model: &impl crate::lit_model::LitModel<Value = L>) -> Self {
        let mut eg = Self::new();
        let sort_names: Vec<&str> = model.sorts().iter().map(|s| s.name).collect();
        eg.sorts.register_builtins(&sort_names);
        eg.ops.register_builtins(model, &eg.sorts);
        eg
    }

    /// Create an e-graph with pre-built registries (from sortcheck).
    pub fn with_registries(
        sorts: SortRegistry<Cfg::S, TRACK>,
        ops: OpRegistry<Cfg::O, Cfg::S, TRACK>,
    ) -> Self {
        let mut eg = Self::new();
        eg.sorts = sorts;
        eg.ops = ops;
        eg
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Every node id in the store, ascending.
    ///
    /// The one place a full scan should get its ids from. The obvious spelling —
    /// `for i in 0..eg.len() { Cfg::G::from_usize(i) }` — is sound but not *locally*
    /// justified: `Cfg::G::Index` spans twice the id space for a bit-stealing id, and
    /// `from_usize` rejects positions outside the smaller payload range. What keeps the
    /// routing table inside that range is that [`TypedRouting::reserve`] mints every entry
    /// through `try_new`, three modules away. Stating that once here means a new scan
    /// inherits the argument instead of re-deriving it.
    ///
    /// [`TypedRouting::reserve`]: crate::typed_routing::TypedRouting::reserve
    pub fn node_ids(&self) -> impl Iterator<Item = Cfg::G> + '_ {
        use crate::containers::DenseId;
        (0..self.len()).map(Cfg::G::from_usize)
    }
    pub fn sorts(&self) -> &SortRegistry<Cfg::S, TRACK> {
        &self.sorts
    }
    pub fn sorts_mut(&mut self) -> &mut SortRegistry<Cfg::S, TRACK> {
        &mut self.sorts
    }
    pub fn ops(&self) -> &OpRegistry<Cfg::O, Cfg::S, TRACK> {
        &self.ops
    }

    pub fn ops_mut(&mut self) -> &mut OpRegistry<Cfg::O, Cfg::S, TRACK> {
        &mut self.ops
    }
    pub fn lits(&self) -> &LitValStore<L, Cfg::V, TRACK> {
        &self.lits
    }
    pub fn lits_mut(&mut self) -> &mut LitValStore<L, Cfg::V, TRACK> {
        &mut self.lits
    }

    pub fn rules(&self) -> &RuleRegistry<TRACK> {
        &self.rules
    }
    pub fn register_rule(&mut self, name: &str, lhs: &str, rhs: &str) -> crate::id::RuleId {
        self.rules.register(name, lhs, rhs)
    }

    pub fn axioms(&self) -> &AxiomRegistry<Cfg::G, TRACK> {
        &self.axioms
    }
    pub fn register_axiom(&mut self, name: &str, lhs: Cfg::G, rhs: Cfg::G) -> crate::id::AxiomId {
        self.axioms.register(name, lhs, rhs)
    }

    // Sorts
    pub fn intern_sort(&mut self, name: &str) -> Cfg::S {
        self.sorts.intern(name)
    }
    pub fn sort_name(&self, id: Cfg::S) -> &str {
        self.sorts.name(id)
    }

    pub fn register_op0(&mut self, name: &str, ret: Cfg::S) -> Cfg::O {
        self.ops.register(name, &[], ret)
    }
    pub fn register_op1(&mut self, name: &str, a: Cfg::S, ret: Cfg::S) -> Cfg::O {
        self.ops.register(name, &[a], ret)
    }
    pub fn register_op2(&mut self, name: &str, a: Cfg::S, b: Cfg::S, ret: Cfg::S) -> Cfg::O {
        self.ops.register(name, &[a, b], ret)
    }
    pub fn register_op3(
        &mut self,
        name: &str,
        a: Cfg::S,
        b: Cfg::S,
        c: Cfg::S,
        ret: Cfg::S,
    ) -> Cfg::O {
        self.ops.register(name, &[a, b, c], ret)
    }
    pub fn register_opn(&mut self, name: &str, args: &[Cfg::S], ret: Cfg::S) -> Cfg::O {
        self.ops.register(name, args, ret)
    }
    pub fn register_c(&mut self, name: &str, arg_sorts: [Cfg::S; 2], ret: Cfg::S) -> Cfg::O {
        self.ops.register_c(name, arg_sorts, ret)
    }
    /// Register an op from a resolved kind plus its non-algebraic metadata (constructor-ness,
    /// `:cost`, `:unextractable`). The surface layer's single registration entry point — see
    /// [`crate::registry::OpRegistry::register_kind_meta`].
    pub fn register_kind_meta(
        &mut self,
        name: &str,
        ret: Cfg::S,
        kind: crate::registry::OpKind<Cfg::S>,
        meta: crate::registry::OpMeta,
    ) -> Cfg::O {
        self.ops.register_kind_meta(name, ret, kind, meta)
    }
    pub fn register_a(
        &mut self,
        name: &str,
        arg: Cfg::S,
        ret: Cfg::S,
        dir: crate::registry::AssocDir,
    ) -> Cfg::O {
        self.ops.register_a(name, arg, ret, dir)
    }
    pub fn register_mset(&mut self, name: &str, arg: Cfg::S, ret: Cfg::S) -> Cfg::O {
        self.ops.register_mset(name, arg, ret)
    }
    pub fn register_set(&mut self, name: &str, arg: Cfg::S, ret: Cfg::S) -> Cfg::O {
        self.ops.register_set(name, arg, ret)
    }
    /// Register an op from a fully-resolved `OpKind` (the property-tag resolver in `sortcheck`).
    pub fn register_kind(&mut self, name: &str, ret: Cfg::S, kind: OpKind<Cfg::S>) -> Cfg::O {
        self.ops.register_kind(name, ret, kind)
    }
    /// Record `op`'s identity (unit) element node (`x ∘ e = x`; the unit drops from monomials).
    /// Called by the resolver in `sortcheck` after it builds the `:identity` term to a node.
    pub fn set_unit_node(&mut self, op: Cfg::O, unit: Cfg::G) {
        // Unique-keyed: an operator declares its identity once, in its own
        // declaration, so a second unit for the same op is a caller error.
        match self.unit_node.try_insert(op, unit) {
            Ok(_) => {}
            Err(ContainerError::DuplicateKey) => panic!("operator already has a unit node"),
            Err(_) => panic!("unit/inverse-op map exhausted its index word"),
        }
    }
    /// Count one right-hand-side action skipped for having no value (`apply::NO_VALUE`).
    pub(crate) fn count_no_value(&mut self) {
        self.no_value = self.no_value.saturating_add(1);
    }

    /// The actions skipped for having no value since the last call, and reset the count.
    pub fn take_no_value(&mut self) -> usize {
        std::mem::take(&mut self.no_value)
    }

    /// The identity (unit) element node of `op`, or `None` if `op` has no declared identity.
    pub fn unit_node(&self, op: Cfg::O) -> Option<Cfg::G> {
        self.unit_node.get_by_key(&op).copied()
    }
    pub fn set_inverse_op(&mut self, op: Cfg::O, inv: Cfg::O) {
        match self.inverse_op.try_insert(op, inv) {
            Ok(_) => {}
            Err(ContainerError::DuplicateKey) => panic!("operator already has an inverse op"),
            Err(_) => panic!("unit/inverse-op map exhausted its index word"),
        }
    }
    /// The canonical summands for `op` of `class`, when its canonical summand form
    /// is an `op` node: the children that node would contribute if spliced. `None`
    /// otherwise. Unlike the splice at build time, this ignores whether the class is
    /// atomic: it is how a caller builds the flat alternative an atomic child
    /// forbids splicing in place.
    pub fn same_op_summands(&self, op: Cfg::O, class: Cfg::G) -> Option<Vec<(Cfg::G, Cfg::M)>> {
        let col = self.ops.completion_column(op)?;
        let repr = self.classes.repr_id(self.classes.find_const(class))?;
        let min_node = self.classes.min_monomial(repr, col)?;
        if self.node_op(min_node) != op
            || !matches!(self.node_ref(min_node), NodeRef::MSet(_) | NodeRef::Set(_))
        {
            return None;
        }
        let mut out = Vec::new();
        self.for_each_child(min_node, |c, times| out.push((c, times)));
        Some(out)
    }

    /// The group inverse operator of `op` (`:inverse neg`), or `None` if none declared.
    pub fn inverse_op(&self, op: Cfg::O) -> Option<Cfg::O> {
        self.inverse_op.get_by_key(&op).copied()
    }

    /// Cancel inverse pairs in a canonical monomial of an op declared `:inverse inv`
    /// (the group law `x ∘ inv(x) = e` applied at pair level, Kapur §5.4's simplest
    /// instance): for each summand class `x`, if the class of the EXISTING node `inv(x)`
    /// is also a summand, matched pairs are removed; a self-inverse class
    /// (`find(inv(x)) == x`) cancels within its own count. Lookup-only (hash-cons probe of
    /// the inverse op's unary partition); removing a pair is sound because the pair equals
    /// the unit, which canonical monomials do not carry (`f({}) = e`). Returns whether the
    /// monomial changed; zeroed entries are dropped. This is NOT full group completion —
    /// no Gaussian elimination, and pairs whose inverse node was never built are not seen.
    /// Cancels `:inverse`-related summand pairs in place, at the configured
    /// multiplicity width. Purely subtractive — `rem_order(2)` and pairwise
    /// cancellation by the smaller of two counts — so no step can overflow.
    pub(crate) fn group_cancel_pairs(&self, inv: Cfg::O, m: &mut Vec<(Cfg::G, Cfg::M)>) -> bool {
        crate::nary_canon::cancel_inverse_pairs(m, |x| self.inverse_class(inv, x))
    }

    /// The class of the existing node `inv(x)`, if the hash-cons holds one.
    pub(crate) fn inverse_class(&self, inv: Cfg::O, x: Cfg::G) -> Option<Cfg::G> {
        self.nodes
            .plain1
            .probe(&inv, &[x])
            .map(|n| self.classes.find_const(n))
    }

    /// The laws `crate::nary_canon::normalize` applies for `op`, with the unit resolved
    /// through the live union-find. A non-n-ary operator reads as `:assoc` with no unit,
    /// which normalizes nothing but the degenerate arity.
    pub fn nary_laws(&self, op: Cfg::O) -> crate::nary_canon::NaryLaws<Cfg::G, Cfg::O> {
        use crate::nary_canon::NaryKind;
        let kind = match self.ops.info(op).kind {
            OpKind::MSet { clamp, .. } => NaryKind::Ac {
                nilpotent: match clamp {
                    crate::registry::Clamp::Nilpotent { order } => Some(order),
                    _ => None,
                },
            },
            OpKind::Set { .. } => NaryKind::Aci,
            _ => NaryKind::Assoc,
        };
        crate::nary_canon::NaryLaws {
            kind,
            unit: self.unit_node(op).map(|u| self.classes.find_const(u)),
            inverse: self.inverse_op(op),
        }
    }
    pub fn register_lit(&mut self, name: &str, ret: Cfg::S) -> Cfg::O {
        self.ops.register_lit(name, ret)
    }
    pub fn op(&self, name: &str) -> Option<Cfg::O> {
        self.ops.id_by_name(name)
    }
    pub fn intern_lit(&mut self, value: L) -> Cfg::V {
        self.lits.intern(value)
    }

    // ── Node operations ──

    /// Run a compiled query plan against this e-graph.
    pub fn run_query(
        &self,
        plan: &crate::schedule::QueryPlan<Cfg::O, Cfg::Index, L>,
    ) -> Vec<crate::ematch::Match<Cfg>> {
        let index = crate::index::IndexStore::build(self);
        let vindex = crate::index::VariantIndex::naive(&index);
        let empty: crate::resolve::GlobalCtx<Cfg::S, Cfg::G> = crate::resolve::GlobalCtx::new();
        crate::ematch::run_query(plan, self, &vindex, &empty)
    }

    /// Saturate: apply rules to fixpoint or until `limit` iterations.
    ///
    /// `Err` is a rule that applied a partial primitive outside its domain; see
    /// [`EvalError`](crate::lit_model::EvalError). Every `saturate*` entry point
    /// here reports it the same way.
    pub fn saturate<M: crate::lit_model::LitModel<Value = L>, S: crate::DenseId + Copy>(
        &mut self,
        rules: &[crate::apply::PreparedRule<Cfg::O, S, L>],
        model: &M,
        limit: usize,
        globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    ) -> Result<crate::saturate::SatResult, crate::lit_model::EvalError> {
        crate::saturate::saturate(rules, self, model, limit, globals)
    }

    /// Semi-naive saturation via delta variants. The driver does not switch
    /// wholesale to naive; rules without safe delta coverage use a full-index match.
    pub fn saturate_semi<M: crate::lit_model::LitModel<Value = L>, S: crate::DenseId + Copy>(
        &mut self,
        rules: &[crate::apply::PreparedRule<Cfg::O, S, L>],
        model: &M,
        limit: usize,
        globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    ) -> Result<crate::saturate::SatResult, crate::lit_model::EvalError> {
        crate::saturate::saturate_semi(rules, self, model, limit, globals)
    }

    /// Saturate under a full [`RunSpec`](crate::saturate::RunSpec) — budget, ruleset, and
    /// `:until` goal. The interpreter's `(run …)` path.
    pub fn saturate_spec<M: crate::lit_model::LitModel<Value = L>, S: crate::DenseId + Copy>(
        &mut self,
        rules: &[crate::apply::PreparedRule<Cfg::O, S, L>],
        model: &M,
        spec: &crate::saturate::RunSpec<Cfg::G>,
        globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    ) -> Result<crate::saturate::SatResult, crate::lit_model::EvalError> {
        crate::saturate::saturate_spec(rules, self, model, spec, globals)
    }

    /// Semi-naive counterpart of [`saturate_spec`](Self::saturate_spec).
    pub fn saturate_semi_spec<
        M: crate::lit_model::LitModel<Value = L>,
        S: crate::DenseId + Copy,
    >(
        &mut self,
        rules: &[crate::apply::PreparedRule<Cfg::O, S, L>],
        model: &M,
        spec: &crate::saturate::RunSpec<Cfg::G>,
        globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    ) -> Result<crate::saturate::SatResult, crate::lit_model::EvalError> {
        crate::saturate::saturate_semi_spec(rules, self, model, spec, globals)
    }

    /// [`saturate_spec`](Self::saturate_spec) over a caller-owned index scratch,
    /// so its span arenas survive the call. See
    /// [`saturate_spec_in`](crate::saturate::saturate_spec_in).
    pub fn saturate_spec_in<M: crate::lit_model::LitModel<Value = L>, S: crate::DenseId + Copy>(
        &mut self,
        rules: &[crate::apply::PreparedRule<Cfg::O, S, L>],
        model: &M,
        spec: &crate::saturate::RunSpec<Cfg::G>,
        globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
        scratch: &mut crate::index::IndexScratch<Cfg>,
    ) -> Result<crate::saturate::SatResult, crate::lit_model::EvalError> {
        crate::saturate::saturate_spec_in(rules, self, model, spec, globals, scratch)
    }

    /// Saturate under `strategy` over a rule list that may hold sequence rules
    /// ([`crate::saturate::Rule`]): each round applies the ordinary rules of the ruleset,
    /// then its sequence rules as one batch on the same snapshot.
    pub fn saturate_rules_in<
        M: crate::lit_model::LitModel<Value = L>,
        S: crate::DenseId + Copy,
        R: crate::saturate::RuleEntry<Cfg, S, L>,
    >(
        &mut self,
        strategy: crate::saturate::SaturationStrategy,
        rules: &[R],
        model: &M,
        spec: &crate::saturate::RunSpec<Cfg::G>,
        globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
        scratch: &mut crate::index::IndexScratch<Cfg>,
        stop: Option<&crate::saturate::StopGoal<'_, Cfg, L, TRACK, PROOFS>>,
    ) -> Result<crate::saturate::SatResult, crate::saturate::SatError> {
        match strategy {
            crate::saturate::SaturationStrategy::Naive => crate::saturate::saturate_rules_naive(
                rules, self, model, spec, globals, scratch, stop,
            ),
            crate::saturate::SaturationStrategy::SemiNaive => {
                // As in `saturate_semi_spec_in`: semi-naive reads the merge-membership delta.
                self.track_merge_members = true;
                let r = crate::saturate::saturate_rules_semi(
                    rules, self, model, spec, globals, scratch, stop,
                );
                self.track_merge_members = false;
                r
            }
        }
    }

    /// Semi-naive counterpart of [`saturate_spec_in`](Self::saturate_spec_in).
    pub fn saturate_semi_spec_in<
        M: crate::lit_model::LitModel<Value = L>,
        S: crate::DenseId + Copy,
    >(
        &mut self,
        rules: &[crate::apply::PreparedRule<Cfg::O, S, L>],
        model: &M,
        spec: &crate::saturate::RunSpec<Cfg::G>,
        globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
        scratch: &mut crate::index::IndexScratch<Cfg>,
    ) -> Result<crate::saturate::SatResult, crate::lit_model::EvalError> {
        // Semi-naive is the one consumer of the merge-membership delta (see
        // `merge_in_classes`); the flag keeps the per-merge ring walks off
        // everywhere else.
        self.track_merge_members = true;
        let r = crate::saturate::saturate_semi_spec_in(rules, self, model, spec, globals, scratch);
        self.track_merge_members = false;
        r
    }

    /// Test support: record merges' absorbed members in the touched log, as semi-naive
    /// saturation does while it runs, so that a test can build one round's delta by
    /// hand (`tests/seq_semi_coverage.rs`).
    #[doc(hidden)]
    pub fn set_track_merge_members(&mut self, on: bool) {
        self.track_merge_members = on;
    }

    /// Whether merges record their absorbed members in the touched log.
    pub fn track_merge_members(&self) -> bool {
        self.track_merge_members
    }

    /// The number of distinct e-classes over the current node set. A scan, not a maintained
    /// counter: `(print-size)` / `(print-stats)` ask for it a handful of times per program.
    pub fn class_count(&self) -> usize {
        let n = self.len();
        let mut seen = vec![false; n];
        let mut count = 0;
        for id in self.node_ids() {
            let r = self.find_const(id).to_usize();
            if !seen[r] {
                seen[r] = true;
                count += 1;
            }
        }
        count
    }

    /// Node counts per operator, indexed by op id (ops with no nodes read 0).
    pub fn op_node_counts(&self) -> Vec<usize> {
        let mut counts = vec![0usize; self.ops.meta_table().len()];
        for id in self.node_ids() {
            let op = self.node_op(id).to_usize();
            if op < counts.len() {
                counts[op] += 1;
            }
        }
        counts
    }

    pub fn find(&mut self, x: Cfg::G) -> Cfg::G {
        self.classes.find(x)
    }

    pub fn find_const(&self, x: Cfg::G) -> Cfg::G {
        self.classes.find_const(x)
    }

    pub fn add(&mut self, op: Cfg::O, children: &[Cfg::G]) -> Cfg::G {
        #[cfg(debug_assertions)]
        {
            let info = self.ops.info(op);
            match &info.kind {
                OpKind::Normal { arg_sorts } => {
                    debug_assert_eq!(
                        children.len(),
                        arg_sorts.len(),
                        "operator '{}' expects {} children, got {}",
                        info.name,
                        arg_sorts.len(),
                        children.len()
                    );
                    for (i, (&c, &s)) in children.iter().zip(arg_sorts.iter()).enumerate() {
                        let got = self.node_sort(c);
                        debug_assert_eq!(
                            got,
                            s,
                            "operator '{}' expected sort '{}' at position {}, got '{}'",
                            info.name,
                            self.sorts.name(s),
                            i,
                            self.sorts.name(got)
                        );
                    }
                }
                OpKind::Commutative { arg_sorts } => {
                    debug_assert_eq!(
                        children.len(),
                        2,
                        "operator '{}' (commutative) expects 2 children, got {}",
                        info.name,
                        children.len()
                    );
                    for (i, (&c, &s)) in children.iter().zip(arg_sorts.iter()).enumerate() {
                        let got = self.node_sort(c);
                        debug_assert_eq!(
                            got,
                            s,
                            "operator '{}' expected sort '{}' at position {}, got '{}'",
                            info.name,
                            self.sorts.name(s),
                            i,
                            self.sorts.name(got)
                        );
                    }
                }
                OpKind::A { arg_sort, .. }
                | OpKind::MSet { arg_sort, .. }
                | OpKind::Set { arg_sort, .. } => {
                    for (i, &c) in children.iter().enumerate() {
                        let got = self.node_sort(c);
                        debug_assert_eq!(
                            got,
                            *arg_sort,
                            "operator '{}' expected sort '{}' at position {}, got '{}'",
                            info.name,
                            self.sorts.name(*arg_sort),
                            i,
                            self.sorts.name(got)
                        );
                    }
                }
                OpKind::Lit => {}
            }
        }
        // Proof mode keeps evidence of how a set, AC or associative term was stored
        // (`add_nary_with_evidence`).
        if PROOFS
            && !self.no_evidence
            && !children.is_empty()
            && matches!(
                self.ops.info(op).kind,
                OpKind::MSet { .. } | OpKind::Set { .. } | OpKind::A { .. }
            )
        {
            let counted: Vec<Cfg::C> = children
                .iter()
                .map(|&c| Cfg::mset_child_single(c))
                .collect();
            return self
                .add_nary_with_evidence(op, children, &counted)
                .unwrap_or_else(|e| {
                    panic!("{e}: `add` lists children one by one, so this needs more children than the width counts (an API contract)")
                });
        }
        // An AC operator stores counted children; listed children count once each, so
        // only a list longer than the width's maximum can overflow, which is a caller's
        // contract here, unlike a rule's computed multiplicity.
        if matches!(self.ops.info(op).kind, OpKind::MSet { .. }) {
            self.mset_buf.clear();
            for &c in children {
                let g = self.classes.find(c);
                self.mset_buf.push(Cfg::mset_child_single(g));
            }
            return self.add_mset_buffered(op).unwrap_or_else(|e| {
                panic!("{e}: `add` lists children one by one, so this needs more children than the width counts (an API contract)")
            });
        }
        self.g_buf.clear();
        self.g_buf
            .extend(children.iter().map(|&c| self.classes.find(c)));

        // Flatten nested same-op ACI children (associativity, `WF_flat`, design §6c), as
        // `flatten_mset_children` does for AC: otherwise `(Or (Or x y) z)` and `(Or x y z)`
        // differ for Set (ACI) ops with completion off. See set_flatten_build.egg.
        if matches!(self.ops.info(op).kind, OpKind::Set { .. }) {
            self.flatten_ac_children(op);
        }

        // A-only operators use an ordered sequence normal form. `AssocDir` selects which
        // nested same-op children belong to that sequence: the first child for a left fold,
        // the last child for a right fold, or every child for full associativity.
        if matches!(self.ops.info(op).kind, OpKind::A { .. }) {
            self.flatten_seq_children(op);
        }

        // Canonization must *establish* the op's algebraic normal form at build time, not
        // defer it to completion: the n-ary arms below call `crate::nary_canon::normalize`.
        // The constructor bit is stamped at creation, not written back after:
        // `set_node_flag` would have to resolve the routing table and dispatch
        // on the node kind again, for a node the store has just built.
        let node_flags = if self.ops.info(op).is_constructor {
            crate::node_types::FLAG_CONSTRUCTOR
        } else {
            0
        };
        let result = match self.ops.info(op).kind {
            OpKind::Set { .. } | OpKind::A { .. } => {
                // The one normalization of an n-ary child list (`crate::nary_canon`):
                // coalesce or dedup, drop the identity's class, clamp, cancel inverse
                // pairs, and resolve a degenerate arity. Degeneracy is an equality, so it
                // returns an *existing* class instead of a fresh node:
                //   - empty multiset  ⇒ the term IS the unit  (`xor(a,a) → {} = e`)
                //   - single mult-1    ⇒ the term IS that child (`+(a, e) → {a} = a`)
                // These hold with completion off; completion only adds the cross-rule
                // (superposition) consequences.
                let laws = self.nary_laws(op);
                self.pair_buf.clear();
                self.pair_buf
                    .extend(self.g_buf.iter().map(|&g| (g, Cfg::M::ONE)));
                let normal = {
                    let (nodes, classes) = (&self.nodes, &self.classes);
                    crate::nary_canon::normalize(&laws, &mut self.pair_buf, |inv, x| {
                        nodes
                            .plain1
                            .probe(&inv, &[x])
                            .map(|n| classes.find_const(n))
                    })
                };
                match normal {
                    crate::nary_canon::Normal::Node => {}
                    // Empty without a declared unit, or with a zero-child A term, is an
                    // API-contract violation (the surface layer rejects it at sortcheck):
                    // the empty monomial names nothing in a semigroup, so minting a node
                    // for it would put a meaningless term in the graph. Panic in ALL
                    // builds, like the other registration invariants.
                    crate::nary_canon::Normal::Empty => panic!(
                        "zero-child n-ary term without a declared identity — \
                         the empty monomial has no algebraic meaning for a semigroup op"
                    ),
                    crate::nary_canon::Normal::Overflow => panic!(
                        "multiplicity overflow on a set or associative operator, whose children \
                         carry no count: an internal invariant"
                    ),
                    crate::nary_canon::Normal::Unit => {
                        self.last_build_collapsed = true;
                        return self
                            .unit_node(op)
                            .expect("Unit is returned only with a unit");
                    }
                    crate::nary_canon::Normal::Single(g) => {
                        self.last_build_collapsed = true;
                        return self.classes.find(g);
                    }
                }
                match self.ops.info(op).kind {
                    OpKind::Set { .. } => {
                        self.g_buf.clear();
                        self.g_buf.extend(self.pair_buf.iter().map(|&(g, _)| g));
                        self.nodes.add_set(op, &self.g_buf, node_flags)
                    }
                    _ => {
                        self.g_buf.clear();
                        self.g_buf.extend(self.pair_buf.iter().map(|&(g, _)| g));
                        self.nodes.add(op, &self.g_buf, &self.ops, node_flags)
                    }
                }
            }
            OpKind::Normal { .. } | OpKind::Commutative { .. }
                if PROOFS && !children.is_empty() =>
            {
                return self.add_with_creation_evidence(op, children, node_flags);
            }
            _ => self.nodes.add(op, &self.g_buf, &self.ops, node_flags),
        };

        let id = self.register_if_fresh(result, op);
        if result.is_fresh() {
            for &child in &self.g_buf {
                if let Some(repr) = self.classes.repr_id(child) {
                    if !self.classes.atomic(repr)
                        && (0..self.classes.min_width().saturating_sub(1))
                            .any(|col| self.classes.min_monomial(repr, col).is_some())
                    {
                        // A class holding a completion monomial turns `atomic`: from now on
                        // a build keeps it nested (see the `spelling_epoch` field).
                        self.spelling_epoch += 1;
                    }
                    self.classes.add_use(repr, id);
                }
            }
        }
        id
    }

    /// Build an AC (MSet) node from its counted children, in the store's own child type,
    /// so a child of multiplicity `k` is one entry: `(Plus x:4294967295 y)` costs two
    /// entries, not 2^32. A multiplicity of zero omits the child. Canonicalization is
    /// [`add`](Self::add)'s: `find` each class, flatten nested same-op children,
    /// normalize, and resolve a degenerate arity to an existing class.
    ///
    /// `Err(MultOverflow)` when the canonical form needs a multiplicity the configured
    /// width cannot hold: two entries of one class whose counts sum past it, or a nested
    /// same-op child whose count times its parent's does.
    pub fn add_mset(&mut self, op: Cfg::O, children: &[Cfg::C]) -> Result<Cfg::G, MultOverflow> {
        #[cfg(debug_assertions)]
        {
            let info = self.ops.info(op);
            let OpKind::MSet { arg_sort, .. } = &info.kind else {
                panic!("add_mset: operator '{}' is not AC", info.name);
            };
            for c in children {
                let got = self.node_sort(Cfg::mset_child_id(c));
                debug_assert_eq!(
                    got,
                    *arg_sort,
                    "operator '{}' expected sort '{}', got '{}'",
                    info.name,
                    self.sorts.name(*arg_sort),
                    self.sorts.name(got)
                );
            }
        }
        if PROOFS && !self.no_evidence {
            let counted: Vec<Cfg::C> = children
                .iter()
                .filter(|c| Cfg::mset_child_mult(c) > Cfg::M::ZERO)
                .copied()
                .collect();
            if !counted.is_empty() {
                let ids: Vec<Cfg::G> = counted.iter().map(Cfg::mset_child_id).collect();
                return self.add_nary_with_evidence(op, &ids, &counted);
            }
        }
        self.mset_buf.clear();
        for c in children {
            let k = Cfg::mset_child_mult(c);
            if k > Cfg::M::ZERO {
                let g = self.classes.find(Cfg::mset_child_id(c));
                self.mset_buf.push(Cfg::mset_child_with_mult(g, k));
            }
        }
        self.add_mset_buffered(op)
    }

    /// Proof-mode build of a set, AC or associative term. The canonical build
    /// `find`s the children, flattens nested same-operator children by splicing
    /// a node of their class, and normalizes under the operator's laws, so the
    /// node it returns can be another spelling than the client's: without
    /// evidence, an explanation about that node never cites the equalities that
    /// turned the client's term into it. When the build changed anything, the
    /// client's term is kept as an evidence node with its given children,
    /// merged into the canonical node's class by a `Build` step whose premises
    /// are the splices. Evidence nodes carry `FLAG_SUBSUMED` and
    /// `FLAG_CONGRUENT_DUP`: their content is the canonical node's, so matching,
    /// completion and extraction skip them, which keeps saturation the plain
    /// engine's. `ids` are the given children; `counted` the same children with
    /// their multiplicities, for an AC operator.
    fn add_nary_with_evidence(
        &mut self,
        op: Cfg::O,
        ids: &[Cfg::G],
        counted: &[Cfg::C],
    ) -> Result<Cfg::G, MultOverflow> {
        let mut key: Vec<(Cfg::G, usize)> = counted
            .iter()
            .map(|c| (Cfg::mset_child_id(c), Cfg::mset_child_mult(c).to_usize()))
            .collect();
        // The canonical build runs every time, memo or not: the spelling it stores
        // depends on the graph (a splice takes the class's current minimal monomial), and
        // a later build of the same term can store a new node that rules must see.
        let saved = (self.no_evidence, self.record_flatten);
        self.no_evidence = true;
        self.record_flatten = true;
        self.flatten_witness.clear();
        self.last_build_collapsed = false;
        let is_mset = matches!(self.ops.info(op).kind, OpKind::MSet { .. });
        let built = if is_mset {
            self.add_mset(op, counted)
        } else {
            Ok(self.add(op, ids))
        };
        let splices = std::mem::take(&mut self.flatten_witness);
        (self.no_evidence, self.record_flatten) = saved;
        let canon = built?;
        let collapsed = std::mem::take(&mut self.last_build_collapsed);
        if !collapsed && !self.build_changed(op, &key, canon, &splices) {
            return Ok(canon);
        }
        // One evidence node per (client term, stored node): the memo key ends with the
        // canonical node, marked by a multiplicity no child carries.
        key.push((canon, usize::MAX));
        if let Some(&id) = self.creation_memo.get(&(op, key.clone())) {
            return Ok(id);
        }
        let mut flags = crate::node_types::FLAG_SUBSUMED | crate::node_types::FLAG_CONGRUENT_DUP;
        if self.ops.info(op).is_constructor {
            flags |= crate::node_types::FLAG_CONSTRUCTOR;
        }
        let id = self
            .nodes
            .add_evidence_nary(op, ids, counted, &self.ops, flags);
        self.classes.add_singleton(id);
        let inst = u32::try_from(self.build_starts.len()).expect("build count exceeds u32");
        self.build_starts.push(self.build_premises.len());
        self.build_premises.extend_from_slice(&splices);
        self.build_collapsed.push(collapsed);
        self.force_survivor = Some(self.classes.find_const(canon));
        if let Some(m) =
            self.merge_in_classes(id, canon, Some(Justification::Build { node: id, inst }))
        {
            self.fold_min_monomial(
                m.survivor,
                m.absorbed,
                m.absorbed_min_row,
                m.absorbed_atomic,
            );
            self.worklist.push((m.absorbed_uses, m.survivor));
        }
        if !self.worklist.is_empty() && !self.round_open {
            self.rebuild_congruence();
        }
        self.remember_creation(op, &key, id);
        Ok(id)
    }

    /// Whether the canonical build of `given` stored another spelling: it
    /// spliced a child, returned a node of another operator (a law collapsed
    /// the term), or returned a node whose original children differ from the
    /// given ones (a child not its class root, a law that dropped or merged
    /// children, or a node first built from other children).
    fn build_changed(
        &self,
        op: Cfg::O,
        given: &[(Cfg::G, usize)],
        canon: Cfg::G,
        splices: &[(Cfg::G, Cfg::G)],
    ) -> bool {
        if !splices.is_empty() || self.node_op(canon) != op {
            return true;
        }
        let mut stored: Vec<(Cfg::G, usize)> = Vec::new();
        let mut ids = Vec::new();
        let mut counted = Vec::new();
        if self.nodes.original_children(canon, &mut ids, &mut counted) {
            stored.extend(ids.iter().map(|&g| (g, 1)));
            stored.extend(
                counted
                    .iter()
                    .map(|c| (Cfg::mset_child_id(c), Cfg::mset_child_mult(c).to_usize())),
            );
        } else {
            self.for_each_child(canon, |g, m| stored.push((g, m.to_usize())));
        }
        let mut given: Vec<(Cfg::G, usize)> = given.to_vec();
        if !matches!(self.ops.info(op).kind, OpKind::A { .. }) {
            // Unordered: compare as multisets, summing a child's repeated entries.
            let norm = |v: &mut Vec<(Cfg::G, usize)>| {
                v.sort_by_key(|&(g, _)| g.to_usize());
                let mut out: Vec<(Cfg::G, usize)> = Vec::with_capacity(v.len());
                for &(g, m) in v.iter() {
                    match out.last_mut() {
                        Some((h, k)) if *h == g => *k += m,
                        _ => out.push((g, m)),
                    }
                }
                *v = out;
            };
            norm(&mut given);
            norm(&mut stored);
        }
        given != stored
    }

    /// A proof-mode evidence node: a client's raw spelling, kept for
    /// explanations and skipped by matching and completion.
    pub fn is_evidence_node_pub(&self, n: Cfg::G) -> bool {
        self.is_evidence_node(n)
    }

    /// A proof-mode evidence node (`add_nary_with_evidence`).
    fn is_evidence_node(&self, n: Cfg::G) -> bool {
        let f = self.node_flags(n);
        f & crate::node_types::FLAG_SUBSUMED != 0 && f & crate::node_types::FLAG_CONGRUENT_DUP != 0
    }

    /// The AC build path behind [`add`](Self::add) and [`add_mset`](Self::add_mset),
    /// over the `find`'d counted children in `mset_buf`.
    fn add_mset_buffered(&mut self, op: Cfg::O) -> Result<Cfg::G, MultOverflow> {
        self.flatten_mset_children(op)?;
        let node_flags = if self.ops.info(op).is_constructor {
            crate::node_types::FLAG_CONSTRUCTOR
        } else {
            0
        };
        // The one normalization (`crate::nary_canon`), on the stored child type directly.
        let laws = self.nary_laws(op);
        let normal = {
            let (nodes, classes) = (&self.nodes, &self.classes);
            crate::nary_canon::normalize_by(
                &laws,
                &mut self.mset_buf,
                |c| Cfg::mset_child_id(c),
                |c| Cfg::mset_child_mult(c),
                |c, m| *c = Cfg::mset_child_with_mult(Cfg::mset_child_id(c), m),
                |inv, x| {
                    nodes
                        .plain1
                        .probe(&inv, &[x])
                        .map(|n| classes.find_const(n))
                },
            )
        };
        match normal {
            crate::nary_canon::Normal::Node => {}
            // See `add`: an empty AC term without a declared unit is an API-contract
            // violation the surface layer rejects at sortcheck.
            crate::nary_canon::Normal::Empty => panic!(
                "zero-child n-ary term without a declared identity — \
                 the empty monomial has no algebraic meaning for a semigroup op"
            ),
            crate::nary_canon::Normal::Overflow => return Err(MultOverflow),
            crate::nary_canon::Normal::Unit => {
                self.last_build_collapsed = true;
                return Ok(self
                    .unit_node(op)
                    .expect("Unit is returned only with a unit"));
            }
            crate::nary_canon::Normal::Single(g) => {
                self.last_build_collapsed = true;
                return Ok(self.classes.find(g));
            }
        }
        let result = self.nodes.add_mset(op, &self.mset_buf, node_flags);
        let id = self.register_if_fresh(result, op);
        if result.is_fresh() {
            for c in &self.mset_buf {
                if let Some(repr) = self.classes.repr_id(Cfg::mset_child_id(c)) {
                    if !self.classes.atomic(repr)
                        && (0..self.classes.min_width().saturating_sub(1))
                            .any(|col| self.classes.min_monomial(repr, col).is_some())
                    {
                        // A class holding a completion monomial turns `atomic`: from now on
                        // a build keeps it nested (see the `spelling_epoch` field).
                        self.spelling_epoch += 1;
                    }
                    self.classes.add_use(repr, id);
                }
            }
        }
        Ok(id)
    }

    /// Build a completion monomial `ms` of `op` (AC or ACI) as a node: counted for AC,
    /// one entry per class for ACI. `scratch` is reused across calls.
    fn add_monomial(
        &mut self,
        op: Cfg::O,
        ms: &[(Cfg::G, Cfg::M)],
        scratch: &mut Vec<Cfg::C>,
    ) -> Result<Cfg::G, MultOverflow> {
        // Completion's monomials are built from class roots and are not client terms:
        // they carry no evidence node.
        let saved = std::mem::replace(&mut self.no_evidence, true);
        let built = if matches!(self.ops.info(op).kind, OpKind::MSet { .. }) {
            scratch.clear();
            scratch.extend(ms.iter().map(|&(g, m)| Cfg::mset_child_with_mult(g, m)));
            self.add_mset(op, scratch)
        } else {
            let ids: Vec<Cfg::G> = ms.iter().map(|&(g, _)| g).collect();
            Ok(self.add(op, &ids))
        };
        self.no_evidence = saved;
        built
    }

    pub fn add_lit(&mut self, op: Cfg::O, lit: Cfg::V) -> Cfg::G {
        let result = self.nodes.add_lit(op, lit, 0);
        self.register_if_fresh(result, op)
    }

    /// Build a *ground* checked term (a literal or a constructor applied to ground args) into a
    /// node, returning its id. Mirrors the interpreter's `build_cterm` for the ground cases; it
    /// has no access to globals, so a `CTerm::Global` is unreachable here (a unit is always
    /// ground) and panics. Used by the property-tag resolver to materialize an op's `:identity`
    /// unit at registration.
    ///
    /// `Err` when a written multiplicity does not fit the configured width
    /// ([`add_with_counts`](Self::add_with_counts)).
    pub fn build_ground_cterm(
        &mut self,
        ct: &crate::sortcheck::CTerm<Cfg::O, Cfg::S, L>,
    ) -> Result<Cfg::G, String> {
        use crate::sortcheck::CTerm;
        match ct {
            CTerm::Lit(val, sort) => {
                let lit_op = self
                    .ops
                    .lit_op_for_sort(*sort)
                    .expect("no lit op for identity's sort");
                let vid = self.lits.intern(val.clone());
                Ok(self.add_lit(lit_op, vid))
            }
            CTerm::App { op, children, .. } => {
                let mut kids = Vec::with_capacity(children.len());
                for c in children {
                    kids.push(match c {
                        CTerm::Counted(t, k) => (self.build_ground_cterm(t)?, Some(k)),
                        _ => (self.build_ground_cterm(c)?, None),
                    });
                }
                self.add_with_counts(*op, &kids)
            }
            CTerm::Counted(t, _) => self.build_ground_cterm(t),
            CTerm::Global(..) => {
                panic!("identity unit must be a ground term, not a global reference")
            }
        }
    }

    /// Build `op` applied to children with counts, as a ground term writes them
    /// (`(Plus x:3 y)`, a count of `None` being 1): one counted child under an AC
    /// operator, the class once under ACI, and `k` positions under any other operator
    /// (the sort checker admits a count only under a variadic one).
    ///
    /// `Err` when a count does not fit the configured multiplicity width, when the AC
    /// node's canonical form needs one that does not ([`add_mset`](Self::add_mset)), or
    /// when the positions exceed [`crate::seq_rhs::MAX_WIDTH`].
    pub fn add_with_counts(
        &mut self,
        op: Cfg::O,
        kids: &[(Cfg::G, Option<&num_bigint::BigUint>)],
    ) -> Result<Cfg::G, String> {
        match self.ops.info(op).kind {
            OpKind::MSet { .. } => {
                let mut cs = Vec::with_capacity(kids.len());
                for &(g, k) in kids {
                    let m = match k {
                        None => Cfg::M::ONE,
                        Some(k) => Cfg::M::try_from_biguint(k).ok_or_else(|| {
                            crate::multiplicity::overflow_message::<Cfg::M>(&format!(
                                "the ground count {k} does not fit the configured multiplicity width"
                            ))
                        })?,
                    };
                    cs.push(Cfg::mset_child_with_mult(g, m));
                }
                self.add_mset(op, &cs).map_err(|_| {
                    crate::multiplicity::overflow_message::<Cfg::M>(
                        "the term's counts, summed or multiplied through nested AC children, do not fit the configured multiplicity width",
                    )
                })
            }
            OpKind::Set { .. } => {
                let ids: Vec<Cfg::G> = kids.iter().map(|&(g, _)| g).collect();
                Ok(self.add(op, &ids))
            }
            _ => {
                let mut ids = Vec::with_capacity(kids.len());
                for &(g, k) in kids {
                    let k = match k {
                        None => Some(1),
                        Some(k) => usize::try_from(k).ok(),
                    }
                    .filter(|&k| {
                        ids.len()
                            .checked_add(k)
                            .is_some_and(|n| n <= crate::seq_rhs::MAX_WIDTH)
                    });
                    let Some(k) = k else {
                        return Err(crate::seq_rhs::TOO_WIDE.to_string());
                    };
                    ids.extend(std::iter::repeat_n(g, k));
                }
                Ok(self.add(op, &ids))
            }
        }
    }

    /// Fill `buf` with `node`'s monomial for `monomial_cmp`: its canonical AC child
    /// multiset if it is an AC node, else the singleton `{node}` (a non-AC node is a
    /// size-1 monomial, §9b). Children are `find`-canonicalized and coalesced.
    pub(crate) fn node_monomial_into(&self, node: Cfg::G, buf: &mut Vec<(Cfg::G, Cfg::M)>) {
        use crate::nary_canon::{NaryKind, NaryLaws, Normal, normalize};
        buf.clear();
        let kind = match self.node_ref(node) {
            NodeRef::MSet(_) => NaryKind::Ac { nilpotent: None },
            NodeRef::Set(_) => NaryKind::Aci,
            _ => {
                buf.push((self.classes.find_const(node), Cfg::M::ONE));
                return;
            }
        };
        self.for_each_child(node, |g, mult| {
            buf.push((self.classes.find_const(g), mult));
        });
        // Coalesce (AC) or dedup (ACI) through the one normalization, with no other law:
        // see below for why the clamp and the unit drop are not reapplied here.
        let laws: NaryLaws<Cfg::G, Cfg::O> = NaryLaws {
            kind,
            unit: None,
            inverse: None,
        };
        if normalize(&laws, buf, |_, _| None) == Normal::Overflow {
            // Coalescing after find-canonicalization grows a multiplicity, so it can
            // exceed the configured width: a union in one round can join two counted
            // children of one node before `rebuild` sees it
            // (`audit_merge_monomial_overflow.egg`). Detected, not wrapped: a wrapped sum
            // would shrink the monomial, and the caller's clamps would then drop the
            // summand, making the e-graph assert an equality that does not hold. The
            // overflow is recorded and reported as the run's multiplicity overflow; the
            // monomial read this once is the node's children as stored, find-canonical.
            self.monomial_overflow
                .store(true, std::sync::atomic::Ordering::Relaxed);
            buf.clear();
            self.for_each_child(node, |g, mult| {
                buf.push((self.classes.find_const(g), mult));
            });
            buf.sort_unstable();
        }
        // No clamp / unit-drop here: canonization (`add`, `recanonize_node`) already established
        // the op's algebraic normal form (nilpotent mod-n, identity unit-drop) in the stored node,
        // and `cc_round` only runs after `rebuild_congruence` recanonicalizes every node. So a
        // stored MSet/Set node's children are already the canonical monomial; reading them
        // back is enough. Unit dropping on the recanonize path is enforced by
        // `CanonMode.unit` (through `crate::nary_canon::normalize_by`) plus the
        // became-a-unit sweep in `rebuild_congruence`; completion does not reapply
        // canonization.
    }

    /// The completion column of `node`'s op (its position in the registry `completion_ops`
    /// array), or `None` if `node`'s op is not a completion (MSet/Set) op.
    fn completion_column(&self, node: Cfg::G) -> Option<usize> {
        self.ops.completion_column(self.node_op(node))
    }

    /// Whether the op is declared cancelative (`:cancellative`, or implied by `:inverse` —
    /// groups are cancelative, Kapur §5.4). Drives the §5 cancel-closure inferences.
    fn op_cancellative(&self, op: Cfg::O) -> bool {
        match self.ops.info(op).kind {
            OpKind::MSet { cancellative, .. } | OpKind::Set { cancellative, .. } => cancellative,
            _ => false,
        }
    }

    /// The normalization clamp for an op's completion monomials: unbounded (MSet), clamp-to-1
    /// (Set idempotent, ACI), or mod-n (nilpotent — stored MSet). Determines how reducts and normal forms
    /// are reduced (design "three independent axes").
    pub(crate) fn op_clamp(&self, op: Cfg::O) -> CompletionClamp {
        use crate::registry::Clamp;
        match self.ops.info(op).kind {
            // Nilpotent is stored MSet (keeps multiplicities); its clamp is read here.
            OpKind::MSet {
                clamp: Clamp::Nilpotent { order },
                ..
            } => CompletionClamp::Nilpotent { order },
            OpKind::MSet { .. } => CompletionClamp::Multiset,
            OpKind::Set {
                clamp: Clamp::Idempotent,
                ..
            } => CompletionClamp::Idempotent,
            // A Set with any other clamp is never constructed (resolver invariant); treat as ACI.
            OpKind::Set { .. } => CompletionClamp::Idempotent,
            _ => CompletionClamp::Multiset, // non-completion op; never reached in the round
        }
    }

    /// Fill `buf` with the completion rule right-hand side for the class of `node`: the
    /// **empty monomial** if the class is `node`'s op's identity (unit) class, the size-1
    /// monomial `{find(node)}` if the class is `atomic` (referenced as a child), else
    /// the monomial of the class's stored min-monomial for `node`'s op column (§9a). Reads the
    /// per-class pool slot; O(1) plus the monomial read. Returns `false` if `node` has no class
    /// (or, in the non-atomic case, no stored monomial for its op — a genuine rule always has
    /// one, so this only guards the degenerate case).
    ///
    /// The unit case is Kapur's `f({}) = e` convention (§2.4) and it is load-bearing: a rule
    /// whose class is the identity must rewrite `f(M) → f({})`, NOT `f(M) → {e}`. With the
    /// atom form, every monomial built from the RHS — superposition reducts, axiom critical
    /// pairs, normalization steps — would carry the unit as a summand that `normalize_*`
    /// (which has no `f(x,e) = x` law) can never remove and that no stored node matches
    /// (canonization unit-drops). The empty-monomial form folds the identity law into the
    /// representation, so rewriting can never insert a unit anywhere.
    pub(crate) fn class_rhs_into(&self, node: Cfg::G, buf: &mut Vec<(Cfg::G, Cfg::M)>) -> bool {
        let cls = self.classes.find_const(node);
        let Some(repr) = self.classes.repr_id(cls) else {
            return false;
        };
        if self
            .unit_node(self.node_op(node))
            .is_some_and(|u| self.classes.find_const(u) == cls)
        {
            buf.clear();
            return true;
        }
        if self.classes.atomic(repr) {
            buf.clear();
            buf.push((cls, Cfg::M::ONE));
            return true;
        }
        let Some(col) = self.completion_column(node) else {
            return false;
        };
        let Some(min) = self.classes.min_monomial(repr, col) else {
            return false;
        };
        self.node_monomial_into(min, buf);
        true
    }

    /// The node whose monomial `class_rhs_into` returns for `node`'s class: the
    /// unit for the unit's class, the class root for an atomic class, else the
    /// class's minimal monomial node (the class root when there is none).
    pub(crate) fn class_rhs_node(&self, node: Cfg::G) -> Cfg::G {
        let cls = self.classes.find_const(node);
        if let Some(u) = self.unit_node(self.node_op(node))
            && self.classes.find_const(u) == cls
        {
            return u;
        }
        let Some(repr) = self.classes.repr_id(cls) else {
            return cls;
        };
        if self.classes.atomic(repr) {
            return cls;
        }
        self.completion_column(node)
            .and_then(|col| self.classes.min_monomial(repr, col))
            .unwrap_or(cls)
    }

    /// The inverse nodes a group-law cancellation in `ms` can use: for each
    /// class `x` of `ms` with a node `inv(x)`, the pair `(inv(x), its class)`.
    fn inverse_premises(
        &self,
        inv: Cfg::O,
        ms: &[(Cfg::G, Cfg::M)],
        out: &mut Vec<(Cfg::G, Cfg::G)>,
    ) {
        for &(x, _) in ms {
            let root = self.classes.find_const(x);
            if let Some(n) = self.nodes.plain1.probe(&inv, &[root]) {
                out.push((n, self.classes.find_const(n)));
            }
        }
    }

    /// Lookup-only resolution of a canonical monomial to the class of an existing node of
    /// `op`: degenerate monomials resolve structurally (empty → the op's unit class, size-1
    /// mult-1 → that child's class); otherwise the op's partition is probed by hash-cons and
    /// the found node's class returned. `None` if no such node exists. Read-only diagnostic
    /// helper for the axiom-CP joinability checker (`ac_invariants`); never mutates.
    pub(crate) fn resolve_monomial_class(
        &self,
        op: Cfg::O,
        m: &[(Cfg::G, Cfg::M)],
    ) -> Option<Cfg::G> {
        if m.is_empty() {
            return self.unit_node(op).map(|u| self.classes.find_const(u));
        }
        if m.len() == 1 && m[0].1 == Cfg::M::ONE {
            return Some(self.classes.find_const(m[0].0));
        }
        let node = match self.ops.info(op).kind {
            OpKind::MSet { .. } => {
                let elems: Vec<Cfg::C> = m
                    .iter()
                    .map(|&(g, mult)| Cfg::mset_child_with_mult(g, mult))
                    .collect();
                self.nodes.mset.probe(op, &elems)
            }
            OpKind::Set { .. } => {
                let elems: Vec<Cfg::G> = m.iter().map(|&(g, _)| g).collect();
                self.nodes.set.probe(op, &elems)
            }
            _ => None,
        };
        node.map(|n| self.classes.find_const(n))
    }

    /// After a merge, fold the absorbed class's per-class AC data into the survivor's:
    /// the merged class takes the lesser of the two completion order keys (`order_key`),
    /// then, per completion column, keeps the `monomial_cmp_key`-least min-monomial node
    /// for each op and ORs in the `atomic` flag (§9a). The key is folded first, so the
    /// two minimal monomials are compared in the order as it stands after the merge. O(nb_completion)
    /// columns, each O(1) plus a monomial read, into reusable buffers. Done here, not in
    /// `EClasses`, because the comparison needs node (AC-children) access and the
    /// op→column map. Best-effort under merge-cascade staleness; completion's read-time
    /// orientation guard makes that safe (§9b).
    fn fold_min_monomial(
        &mut self,
        survivor: Cfg::G,
        absorbed: Cfg::G,
        absorbed_min_row: Option<<Cfg::G as DenseId>::Index>,
        absorbed_atomic: bool,
    ) {
        let surv_root = self.classes.find_const(survivor);
        let surv_repr = match self.classes.repr_id(surv_root) {
            Some(r) => r,
            None => return,
        };
        let Some(key_col) = self.key_col() else {
            if absorbed_atomic {
                self.classes.set_atomic(surv_repr);
            }
            return;
        };
        let surv_atomic = self.classes.atomic(surv_repr);
        if surv_atomic != absorbed_atomic {
            // The joined class is atomic; the side that was not had its monomials spliced.
            let was_spliced = if surv_atomic {
                (0..key_col).any(|col| {
                    self.classes
                        .min_monomial_at_row(absorbed_min_row, col)
                        .is_some()
                })
            } else {
                self.class_has_monomial(surv_repr)
            };
            if was_spliced {
                self.spelling_epoch += 1;
            }
        }
        if absorbed_atomic {
            self.classes.set_atomic(surv_repr);
        }
        // The merged class's key is the lesser of the two. A class with no stored key has
        // its root as key: it has not merged since keys were first kept (the first
        // completion node), and its root has not changed since. Written only when the
        // absorbed side's key is the lesser, so a merge that keeps the survivor's key
        // allocates no pool row.
        let surv_key = self
            .classes
            .min_monomial(surv_repr, key_col)
            .unwrap_or(surv_root);
        let abs_key = self
            .classes
            .min_monomial_at_row(absorbed_min_row, key_col)
            .unwrap_or(absorbed);
        if abs_key < surv_key {
            self.classes.set_min_monomial(surv_repr, key_col, abs_key);
            self.key_lowered.push(surv_root);
        }
        let mut a = std::mem::take(&mut self.cmp_buf_a);
        let mut b = std::mem::take(&mut self.cmp_buf_b);
        for col in 0..key_col {
            let Some(absorbed_min) = self.classes.min_monomial_at_row(absorbed_min_row, col) else {
                continue; // absorbed class has no monomial for this op
            };
            match self.classes.min_monomial(surv_repr, col) {
                None => {
                    // survivor had no monomial for this op; take the absorbed one.
                    self.classes.set_min_monomial(surv_repr, col, absorbed_min);
                    self.spelling_epoch += 1;
                }
                Some(surv_min) if surv_min != absorbed_min => {
                    self.node_monomial_into(surv_min, &mut a);
                    self.node_monomial_into(absorbed_min, &mut b);
                    if self.monomial_cmp_key(&b, &a) == std::cmp::Ordering::Less {
                        self.classes.set_min_monomial(surv_repr, col, absorbed_min);
                    }
                    // Either side's references now splice one monomial where they spliced
                    // two different ones.
                    self.spelling_epoch += 1;
                }
                Some(_) => {} // equal; nothing to do
            }
        }
        self.cmp_buf_a = a;
        self.cmp_buf_b = b;
    }

    /// The pool column of the completion order key: the last one, after one column per
    /// completion op. `None` before the first completion node, when no class keeps a key
    /// and completion has nothing to order.
    fn key_col(&self) -> Option<usize> {
        self.classes.min_width().checked_sub(1)
    }

    /// The completion order key of `g`'s class. Completion orders monomials by keys, not
    /// by class ids (`monomial_cmp_key`): a fresh class's key is its id, and a merged
    /// class takes the lesser of the two keys (`fold_min_monomial`), so keys are distinct
    /// across live classes and a merge only ever lowers the key of the classes it joins.
    /// The union-find keeps its own survivor policy (rank, size, `--union-by`), and the
    /// representative id can be the larger one. Ordering by representative id made a
    /// node grow when a child merged into a class with a larger representative, which left
    /// the class's stored minimal monomial above another member (I5) and lost completion
    /// consequences (`ac_minmono_grow_wa.egg`; Lean `idOrder_grow_breaks_I5`). With keys a
    /// child's key only goes down, so recanonization never grows a node and the shrink
    /// refresh (`refresh_min_monomial`) keeps I5. The key lives in the classes' tracked
    /// min-monomial pool, so `restore` rolls it back.
    pub(crate) fn order_key(&self, g: Cfg::G) -> Cfg::G {
        let root = self.classes.find_const(g);
        if let Some(col) = self.key_col()
            && let Some(repr) = self.classes.repr_id(root)
            && let Some(k) = self.classes.min_monomial(repr, col)
        {
            return k;
        }
        root
    }

    /// Degree-lex over completion order keys: total size first, then the `(key, count)`
    /// entries from the largest key down, the larger count winning at the first
    /// difference. This is `multiset::monomial_cmp` with each class replaced by its
    /// `order_key`; stored monomials stay sorted by class id (the hash-cons, the
    /// decompositions and the indexes depend on that), so each side is copied and sorted
    /// by key into an inline buffer, with no allocation up to 16 distinct classes. Every
    /// order completion uses goes through here: rule orientation, the minimal monomial
    /// (fold, refresh) and the basis diagnostics, so orientation and the minimal monomial
    /// agree.
    pub(crate) fn monomial_cmp_key(
        &self,
        a: &[(Cfg::G, Cfg::M)],
        b: &[(Cfg::G, Cfg::M)],
    ) -> std::cmp::Ordering {
        type Keyed<G, M> = smallvec::SmallVec<[(G, M); 16]>;
        crate::multiset::monomial_size_cmp(a, b).then_with(|| {
            let keyed = |m: &[(Cfg::G, Cfg::M)]| -> Keyed<Cfg::G, Cfg::M> {
                let mut v: Keyed<Cfg::G, Cfg::M> =
                    m.iter().map(|&(g, k)| (self.order_key(g), k)).collect();
                v.sort_unstable();
                v
            };
            let (ka, kb) = (keyed(a), keyed(b));
            ka.iter().rev().cmp(kb.iter().rev())
        })
    }

    /// Keep the min-monomial slot least after an in-place recanonization. Invariant (I5):
    /// the slot of a class in `id`'s op column is the degree-lex-least *active* same-op
    /// monomial of that class. The slot is written at creation (`register_if_fresh`) and
    /// folded on merge (`fold_min_monomial`); recanonization rewrites a stored node's span
    /// in place (coalesce, unit drop, clamp after a child merge) and can shrink `id` below
    /// the stored minimum. It never grows `id`: completion orders by `order_key`, and a merge
    /// only lowers keys, so this one-sided update keeps the stored minimum least. A key
    /// lowered on the
    /// survivor's side shrinks parents without rewriting them; `refresh_key_lowered` calls
    /// this for those. The trap: with a stale minimum the old minimum is not a rule
    /// (`M = r(c)`) and the shrunk node is dropped by the orientation guard (`M ≺ r(c)`), so
    /// the class yields no rule and completion misses `a+b+z = p+q+z` from `a+b = p+q+r`,
    /// `r = 0`.
    /// O(1) plus two monomial reads; the write goes through the tracked pool, so `restore`
    /// rolls it back with the recanonization.
    fn refresh_min_monomial(&mut self, id: Cfg::G) {
        use crate::node_types::{FLAG_AC_COLLAPSED, FLAG_SUBSUMED};
        if self.node_flags(id) & (FLAG_SUBSUMED | FLAG_AC_COLLAPSED) != 0 {
            return;
        }
        let Some(col) = self.completion_column(id) else {
            return;
        };
        let Some(repr) = self.classes.repr_id(self.classes.find_const(id)) else {
            return;
        };
        match self.classes.min_monomial(repr, col) {
            None => self.classes.set_min_monomial(repr, col, id),
            Some(cur) if cur != id => {
                let mut a = std::mem::take(&mut self.cmp_buf_a);
                let mut b = std::mem::take(&mut self.cmp_buf_b);
                self.node_monomial_into(cur, &mut a);
                self.node_monomial_into(id, &mut b);
                if self.monomial_cmp_key(&b, &a) == std::cmp::Ordering::Less {
                    self.classes.set_min_monomial(repr, col, id);
                }
                self.cmp_buf_a = a;
                self.cmp_buf_b = b;
            }
            Some(_) => {}
        }
    }

    pub fn merge(&mut self, a: Cfg::G, b: Cfg::G) -> Option<(Cfg::G, Cfg::G)> {
        debug_assert_eq!(
            self.node_sort(a),
            self.node_sort(b),
            "cannot merge e-classes of different sorts: '{}' has sort '{}', '{}' has sort '{}'",
            self.node_op_name(a),
            self.sorts.name(self.node_sort(a)),
            self.node_op_name(b),
            self.sorts.name(self.node_sort(b))
        );
        debug_assert!(
            !self.sorts.is_concrete(self.node_sort(a)),
            "cannot merge concrete sort '{}' e-classes",
            self.sorts.name(self.node_sort(a))
        );
        let m = self.merge_in_classes(a, b, None)?;
        self.fold_min_monomial(
            m.survivor,
            m.absorbed,
            m.absorbed_min_row,
            m.absorbed_atomic,
        );
        self.worklist.push((m.absorbed_uses, m.survivor));
        Some((m.survivor, m.absorbed))
    }

    /// Class merge, recording the absorbed side's member nodes in the
    /// semi-naive touched log when `track_merge_members` is set.
    ///
    /// A merge can create matches without changing any node's canonical form:
    /// when the surviving representative is the id the parents already store,
    /// nothing recanonicalizes, yet nodes of the absorbed side changed class.
    /// The variant decomposition's premise — every new match shows up as a new
    /// or re-canonicalized tuple in some atom's relation — then needs the
    /// membership change itself in the delta, and the absorbed members are
    /// exactly that change: a new match either recanonicalizes a parent
    /// (already touched) or connects through a node whose class assignment
    /// moved. Collection walks both rings before the merge splices them,
    /// because the survivor is not known until the union decides; the flag
    /// keeps the walk off outside semi-naive saturation, where nothing
    /// consumes the log.
    fn merge_in_classes(
        &mut self,
        a: Cfg::G,
        b: Cfg::G,
        just: Option<Justification<Cfg::G>>,
    ) -> Option<crate::classes::MergeInfo<Cfg::G, Cfg::UL>> {
        let ra = self.classes.find_const(a);
        let rb = self.classes.find_const(b);
        if ra == rb {
            return None;
        }
        // Inside the completion code every merge carries a tag naming the Lean theorem
        // that justifies it; the mirror checks the theorem's preconditions on the state
        // as it stands before the merge.
        #[cfg(debug_assertions)]
        self.cc_mirror_on_merge(a, b);
        let grouped = if PROOFS {
            match self.pending_premises.take() {
                Some(p) => Some(p),
                None => just.and_then(|j| self.grouped_premises_now(j, a, b)),
            }
        } else {
            None
        };
        // Survivor policy (--union-by): `Rank` leaves the choice to the
        // union-find; the directed criteria keep the heavier side, so the
        // absorbed side is the cheap one and is known before the union.
        let prefer_a = match (self.force_survivor.take(), self.union_by) {
            (Some(keep), _) => Some(keep == ra),
            (None, UnionBy::Rank) => None,
            (None, _) => Some(self.union_weight(ra) >= self.union_weight(rb)),
        };
        // Semi-naive merge tracking: collect the absorbed side's members
        // before the splice. Under a directed policy only the (small)
        // absorbed ring is walked; under rank the survivor is unknown until
        // the union decides, so both rings are collected and the absorbed
        // one pushed after.
        let pre = if self.track_merge_members {
            match prefer_a {
                Some(pa) => {
                    let absorbed_repr = if pa { rb } else { ra };
                    let v: Vec<Cfg::G> = self.classes.iter_class(absorbed_repr).collect();
                    Some((absorbed_repr, v, None))
                }
                None => {
                    let va: Vec<Cfg::G> = self.classes.iter_class(ra).collect();
                    let vb: Vec<Cfg::G> = self.classes.iter_class(rb).collect();
                    Some((ra, va, Some(vb)))
                }
            }
        } else {
            None
        };
        let m = match (prefer_a, just) {
            (None, None) => self.classes.merge(a, b),
            (None, Some(j)) => self.classes.merge_justified(a, b, j),
            (Some(pa), None) => self.classes.merge_directed_with(a, b, pa),
            (Some(pa), Some(j)) => self.classes.merge_justified_directed_with(a, b, pa, j),
        }?;
        if let Some((r0, v0, v1)) = pre {
            let absorbed = match v1 {
                None => v0,
                Some(v1) => {
                    if m.absorbed == r0 {
                        v0
                    } else {
                        v1
                    }
                }
            };
            self.touched.extend(absorbed);
        }
        // Tee every merge (direct, congruence, completion — all route through
        // here) to the Nelson-Oppen export log. Captured at merge time with the
        // pre-merge roots, because after congruence closure the two classes are
        // one and the pairing cannot be recovered from `find`.
        if self.record_merges {
            self.merged_log.push((m.survivor, m.absorbed));
        }
        if let Some(pairs) = grouped {
            let key = Self::pair_key(a, b);
            let start = self.merge_premise_pairs.len();
            self.merge_premise_pairs.extend_from_slice(&pairs);
            self.merge_premise_index
                .insert(key, (start, self.merge_premise_pairs.len()));
            self.merge_premise_log.push(key);
        }
        Some(m)
    }

    /// Enable or disable capture of EUF-derived merges into `merged_log` for
    /// Nelson-Oppen equality export. Off by default. Disabling clears whatever
    /// was captured.
    pub fn set_record_merges(&mut self, enabled: bool) {
        self.record_merges = enabled;
        if !enabled {
            self.merged_log.clear();
        }
    }

    /// Whether merge capture is currently on.
    pub fn record_merges(&self) -> bool {
        self.record_merges
    }

    /// Take and clear the merges captured since the last call. Each is a
    /// `(survivor, absorbed)` class-root pair as of merge time. The caller must
    /// drain before advancing the decision level: merges from a level that is
    /// later popped are meaningless, and `restore` clears the log regardless.
    pub fn take_merged_log(&mut self) -> Vec<(Cfg::G, Cfg::G)> {
        std::mem::take(&mut self.merged_log)
    }

    /// The merges captured since the last [`take_merged_log`](Self::take_merged_log),
    /// without clearing them: lets a second consumer (a relevancy client)
    /// read the log with its own cursor while the Nelson-Oppen export still
    /// drains it. Cleared by `restore` like the log itself.
    pub fn merged_log(&self) -> &[(Cfg::G, Cfg::G)] {
        &self.merged_log
    }

    /// The member nodes of `id`'s e-class (the class ring, in ring order).
    pub fn class_members(&self, id: Cfg::G) -> impl Iterator<Item = Cfg::G> + '_ {
        self.classes.iter_class(self.classes.find_const(id))
    }

    /// Turn the node-level e-matching shield on or off: while on, the index
    /// build skips nodes carrying `FLAG_UNMATCHABLE`; while off, they are
    /// indexed as usual. Off by default, so a client that never shields
    /// anything sees no change.
    pub fn set_matching_shield(&mut self, on: bool) {
        self.matching_shield = on;
    }

    /// Whether the node-level e-matching shield is on.
    pub fn matching_shield(&self) -> bool {
        self.matching_shield
    }

    /// Shield (`false`) or un-shield (`true`) the single node `id` from
    /// e-matching (`FLAG_UNMATCHABLE`). Reversible and semi-persistent: the
    /// write goes through the node store, so it rolls back on `restore`.
    /// Shielding only removes matches, so it is soundness-free.
    pub fn set_node_matchable(&mut self, id: Cfg::G, matchable: bool) {
        if matchable {
            self.clear_node_flag(id, crate::node_types::FLAG_UNMATCHABLE);
        } else {
            self.set_node_flag(id, crate::node_types::FLAG_UNMATCHABLE);
        }
    }

    /// Whether `id`'s node is free of `FLAG_UNMATCHABLE`.
    pub fn is_node_matchable(&self, id: Cfg::G) -> bool {
        self.node_flags(id) & crate::node_types::FLAG_UNMATCHABLE == 0
    }

    pub fn merge_justified(
        &mut self,
        a: Cfg::G,
        b: Cfg::G,
        just: Justification<Cfg::G>,
    ) -> Option<(Cfg::G, Cfg::G)> {
        debug_assert_eq!(
            self.node_sort(a),
            self.node_sort(b),
            "cannot merge e-classes of different sorts: '{}' has sort '{}', '{}' has sort '{}'",
            self.node_op_name(a),
            self.sorts.name(self.node_sort(a)),
            self.node_op_name(b),
            self.sorts.name(self.node_sort(b))
        );
        debug_assert!(
            !self.sorts.is_concrete(self.node_sort(a)),
            "cannot merge concrete sort '{}' e-classes",
            self.sorts.name(self.node_sort(a))
        );
        let m = self.merge_in_classes(a, b, Some(just))?;
        self.fold_min_monomial(
            m.survivor,
            m.absorbed,
            m.absorbed_min_row,
            m.absorbed_atomic,
        );
        self.worklist.push((m.absorbed_uses, m.survivor));
        Some((m.survivor, m.absorbed))
    }

    pub fn explain(&self, a: Cfg::G, b: Cfg::G, buf: &mut ProofBuf<Cfg::G>) -> bool {
        self.classes.explain(a, b, buf)
    }

    /// Write a deterministic, line-oriented proof-path record for every e-node.
    ///
    /// Each record names the node's current operator, children, representative,
    /// proof-tree LCA, and every justified edge from the node to that
    /// representative. One Euler-tour table is built in O(n), then each LCA is
    /// queried in O(1); writing the proof paths costs O(number of emitted
    /// steps). Representative records have an empty reflexive proof.
    ///
    /// The dump is available only when `PROOFS = true`. Any successful
    /// justified merge or restore invalidates the table, so the complete build
    /// and write happen under this single immutable borrow.
    pub fn dump_all_proofs<W: std::io::Write>(
        &self,
        mut out: W,
    ) -> std::io::Result<ProofDumpStats> {
        if !PROOFS {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "proof dump requires an EGraph with PROOFS=true",
            ));
        }

        let lca = {
            let parents = self.classes.proof_parent().ok_or_else(|| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "PROOFS=true e-graph has no proof-parent forest",
                )
            })?;
            crate::lca::LcaTable::build(parents, self.len())
        };

        writeln!(out, "# semi-persistent-proof-dump v2")?;
        writeln!(
            out,
            "# each term record proves node == representative; ids are decimal"
        )?;
        writeln!(
            out,
            "# original: the children a congruence step through the node takes as premises"
        )?;
        writeln!(
            out,
            "# rewrite, grouped and completion steps list their premise pairs, each proved by its own term records"
        )?;
        writeln!(out, "axioms {}", self.axioms.len())?;
        for i in 0..self.axioms.len() {
            let id = crate::id::AxiomId::new(i as u32);
            let info = self.axioms.info(id);
            writeln!(
                out,
                "axiom {} lhs {} rhs {} name {:?}",
                i,
                info.lhs.to_usize(),
                info.rhs.to_usize(),
                info.name
            )?;
        }
        writeln!(out, "terms {}", self.len())?;

        let mut stats = ProofDumpStats::default();
        let mut buf = ProofBuf::new();
        let mut children = Vec::new();

        for node in self.node_ids() {
            let representative = self.find_const(node);
            let ancestor = lca.lca(node, representative).ok_or_else(|| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!(
                        "proof forest has no LCA for equivalent nodes {} and {}",
                        node.to_usize(),
                        representative.to_usize()
                    ),
                )
            })?;

            buf.clear();
            if !self
                .classes
                .explain_with_lca(node, representative, ancestor, &mut buf)
            {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    format!(
                        "LCA {} is not on both proof paths for nodes {} and {}",
                        ancestor.to_usize(),
                        node.to_usize(),
                        representative.to_usize()
                    ),
                ));
            }

            write!(
                out,
                "term {} representative {} op {:?}",
                node.to_usize(),
                representative.to_usize(),
                self.node_op_name(node)
            )?;
            match self.get_lit_val(node) {
                Some(value) => write!(out, " literal {:?}", value.to_string())?,
                None => write!(out, " literal -")?,
            }
            children.clear();
            self.for_each_child(node, |child, mult| {
                children.push((child, mult));
            });
            write!(out, " children [")?;
            for (i, (child, mult)) in children.iter().enumerate() {
                if i > 0 {
                    write!(out, ",")?;
                }
                write!(out, "{}:{}", child.to_usize(), mult)?;
            }
            write!(out, "] original [")?;
            for (i, child) in self.original_children(node).iter().enumerate() {
                if i > 0 {
                    write!(out, ",")?;
                }
                write!(out, "{}", child.to_usize())?;
            }
            writeln!(out, "]")?;

            writeln!(
                out,
                "proof lca {} steps {}",
                ancestor.to_usize(),
                buf.steps.len()
            )?;
            for &(from, to, justification) in &buf.steps {
                write!(out, "step {} {} ", from.to_usize(), to.to_usize())?;
                self.write_proof_dump_justification(&mut out, justification)?;
                // The premises recorded at the merge (grouped and completion steps).
                if let Some(premises) = self.merge_premises(from, to) {
                    write!(out, " premises [")?;
                    for (i, (x, y)) in premises.iter().enumerate() {
                        if i > 0 {
                            write!(out, ",")?;
                        }
                        write!(out, "{}={}", x.to_usize(), y.to_usize())?;
                    }
                    write!(out, "]")?;
                }
                writeln!(out)?;
            }
            writeln!(out, "end")?;

            stats.terms += 1;
            stats.nontrivial_proofs += usize::from(!buf.steps.is_empty());
            stats.steps += buf.steps.len();
        }

        writeln!(
            out,
            "summary terms {} nontrivial {} steps {}",
            stats.terms, stats.nontrivial_proofs, stats.steps
        )?;
        Ok(stats)
    }

    fn write_proof_dump_justification<W: std::io::Write>(
        &self,
        out: &mut W,
        justification: Justification<Cfg::G>,
    ) -> std::io::Result<()> {
        match justification {
            Justification::Filler => Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "proof path contains a filler justification",
            )),
            Justification::Rewrite { rule_id, inst } => {
                write!(out, "rewrite rule={}", rule_id.to_usize())?;
                match self.rewrite_premises(justification) {
                    Some(premises) => {
                        write!(out, " instance={inst} premises [")?;
                        for (i, (x, y)) in premises.iter().enumerate() {
                            if i > 0 {
                                write!(out, ",")?;
                            }
                            write!(out, "{}={}", x.to_usize(), y.to_usize())?;
                        }
                        write!(out, "]")
                    }
                    None => write!(out, " premises unknown"),
                }
            }
            Justification::Congruence { node_a, node_b } => write!(
                out,
                "congruence nodes={},{}",
                node_a.to_usize(),
                node_b.to_usize()
            ),
            Justification::Axiom { axiom_id } => {
                write!(out, "axiom id={}", axiom_id.to_usize())
            }
            Justification::ACSuperposition { node_a, node_b } => write!(
                out,
                "ac-superposition nodes={},{}",
                node_a.to_usize(),
                node_b.to_usize()
            ),
            Justification::ACInterReduction { node_a, node_b } => write!(
                out,
                "ac-inter-reduction nodes={},{}",
                node_a.to_usize(),
                node_b.to_usize()
            ),
            Justification::ACAxiomCP { node_a, node_b } => write!(
                out,
                "ac-axiom-cp nodes={},{}",
                node_a.to_usize(),
                node_b.to_usize()
            ),
            Justification::Cancellative { node_a, node_b } => write!(
                out,
                "cancellative nodes={},{}",
                node_a.to_usize(),
                node_b.to_usize()
            ),
            Justification::Assumption { lit } => {
                write!(out, "assumption lit={}", lit.as_usize())
            }
            Justification::Normalize { node, normal } => write!(
                out,
                "normalize node={} normal={}",
                node.to_usize(),
                normal.to_usize()
            ),
            Justification::Build { node, .. } => {
                write!(out, "build node={} splices [", node.to_usize())?;
                for (i, (g, m)) in self
                    .build_premises(justification)
                    .unwrap_or(&[])
                    .iter()
                    .enumerate()
                {
                    if i > 0 {
                        write!(out, ",")?;
                    }
                    write!(out, "{}={}", g.to_usize(), m.to_usize())?;
                }
                write!(out, "]")
            }
            Justification::InverseCancel { node_a, node_b } => write!(
                out,
                "inverse-cancel nodes={},{}",
                node_a.to_usize(),
                node_b.to_usize()
            ),
        }
    }

    /// Deep explanation: expand Congruence justifications into child-pair proofs.
    /// Appends all steps (including recursive child explanations) to `buf.steps`.
    /// Uses an iterative worklist — no recursion.
    ///
    /// For C/AC/ACI nodes, children are matched by canonical representative
    /// (group-by-find), not by position. This avoids combinatorial search.
    pub fn explain_deep(&self, a: Cfg::G, b: Cfg::G, buf: &mut ProofBuf<Cfg::G>) -> bool {
        if !self.classes.explain(a, b, buf) {
            return false;
        }

        // The expansion walks a DAG of pair dependencies. Without
        // memoization a pair shared by several paths is re-expanded once per
        // path, which is exponential on diamond-shaped explanation structure
        // (a two-assertion Boolean-congruence input ran for over 15 seconds
        // before these sets were added). Worse than exponential: it can fail
        // to terminate. A congruence step's premises are the two nodes'
        // ORIGINAL children, which predate recanonization, and their present
        // equality can route through the very congruence edge the collision
        // produced. Without a record of expanded pairs the walk re-emits that
        // edge, expands it again, and loops forever (measured past 2 million
        // steps and 16 GB on the SMT regression
        // `edge_cases/boolean_backtracking.smt2`, a Boolean child oscillating
        // across backtracks). With the sets every congruence pair is expanded
        // at most once and every pair's forest path is appended at most once,
        // so the step list is bounded by the number of distinct pairs times
        // the longest forest path, whatever shape the forest has.
        // Two sets, because the two guards
        // protect different work: `expanded` marks congruence steps whose
        // child pairs have been walked; `explained` marks pairs whose forest
        // path is already in `buf.steps`. A congruence pair must not seed
        // `explained` (its path can be longer than the one recorded edge),
        // and the initial pair must not seed `expanded` (its own congruence
        // step still needs its children walked). Repeats append no steps,
        // and consumers collect leaf justifications as a set, so skipping
        // them loses nothing.
        let mut expanded: std::collections::HashSet<(usize, usize)> =
            std::collections::HashSet::new();
        let mut explained: std::collections::HashSet<(usize, usize)> =
            std::collections::HashSet::new();
        explained.insert(Self::pair_key(a, b));

        let mut ac_scratch: Vec<Cfg::C> = Vec::new();
        let mut i = 0;
        while i < buf.steps.len() {
            let step = buf.steps[i].2;
            match step {
                Justification::Congruence { node_a, node_b } => {
                    if expanded.insert(Self::pair_key(node_a, node_b)) {
                        buf.children_a.clear();
                        buf.children_b.clear();
                        self.collect_original_children(
                            node_a,
                            &mut buf.children_a,
                            &mut ac_scratch,
                        );
                        self.collect_original_children(
                            node_b,
                            &mut buf.children_b,
                            &mut ac_scratch,
                        );
                        let is_ordered = matches!(
                            self.node_ref(node_a),
                            NodeRef::Plain1(_)
                                | NodeRef::Plain2(_)
                                | NodeRef::Plain3(_)
                                | NodeRef::PlainN(_)
                                | NodeRef::Seq(_)
                        );
                        if is_ordered {
                            // Positional premises: the two child lists have one length, and
                            // children at one position are in one class. A violation would
                            // leave a premise unexplained, so it stops a debug build.
                            debug_assert_eq!(
                                buf.children_a.len(),
                                buf.children_b.len(),
                                "congruence step between ordered nodes of different arity"
                            );
                            for j in 0..buf.children_a.len().min(buf.children_b.len()) {
                                let ca = buf.children_a[j];
                                let cb = buf.children_b[j];
                                if ca == cb {
                                    continue;
                                }
                                debug_assert_eq!(
                                    self.classes.find_const(ca),
                                    self.classes.find_const(cb),
                                    "congruence step whose children differ in class"
                                );
                                if explained.insert(Self::pair_key(ca, cb)) {
                                    self.classes.explain(ca, cb, buf);
                                }
                            }
                        } else if let Some(pairs) = self.merge_premises(node_a, node_b) {
                            for &(x, y) in pairs {
                                if explained.insert(Self::pair_key(x, y)) {
                                    self.classes.explain(x, y, buf);
                                }
                            }
                        } else {
                            let op = self.node_op(node_a);
                            self.law_witnesses(op, buf);
                            self.explain_grouped(buf, &mut explained);
                        }
                    }
                }
                Justification::Normalize { node, normal }
                    if self.merge_premises(node, normal).is_some() =>
                {
                    if expanded.insert(Self::pair_key(node, normal)) {
                        for &(x, y) in self.merge_premises(node, normal).unwrap_or(&[]) {
                            if explained.insert(Self::pair_key(x, y)) {
                                self.classes.explain(x, y, buf);
                            }
                        }
                    }
                }
                Justification::Normalize { node, normal } => {
                    if expanded.insert(Self::pair_key(node, normal)) {
                        buf.children_a.clear();
                        buf.children_b.clear();
                        self.collect_original_children(node, &mut buf.children_a, &mut ac_scratch);
                        buf.children_b.push(normal);
                        let op = self.node_op(node);
                        self.law_witnesses(op, buf);
                        self.explain_grouped(buf, &mut explained);
                    }
                }
                Justification::Build { node, .. } => {
                    let (from, to, _) = buf.steps[i];
                    let other = if from == node { to } else { from };
                    if let Some(pairs) = self.merge_premises(from, to) {
                        if expanded.insert(Self::pair_key(node, other)) {
                            for &(x, y) in pairs {
                                if explained.insert(Self::pair_key(x, y)) {
                                    self.classes.explain(x, y, buf);
                                }
                            }
                        }
                    } else if expanded.insert(Self::pair_key(node, other)) {
                        buf.children_a.clear();
                        buf.children_b.clear();
                        self.for_each_child(node, |c, _| buf.children_a.push(c));
                        if let Some(splices) = self.build_premises(step) {
                            for &(g, m) in splices {
                                buf.children_a.push(g);
                                buf.children_a.push(m);
                                self.for_each_child(m, |c, _| buf.children_a.push(c));
                            }
                        }
                        let op = self.node_op(node);
                        if self.build_collapsed(step) == Some(false) {
                            self.collect_original_children(
                                other,
                                &mut buf.children_b,
                                &mut ac_scratch,
                            );
                        } else {
                            buf.children_b.push(other);
                        }
                        self.law_witnesses(op, buf);
                        self.explain_grouped(buf, &mut explained);
                    }
                }
                Justification::Rewrite { .. } => {
                    if let Some(premises) = self.rewrite_premises(step) {
                        for &(x, y) in premises {
                            if explained.insert(Self::pair_key(x, y)) {
                                self.classes.explain(x, y, buf);
                            }
                        }
                    }
                }
                Justification::ACSuperposition { .. }
                | Justification::ACInterReduction { .. }
                | Justification::ACAxiomCP { .. }
                | Justification::Cancellative { .. }
                | Justification::InverseCancel { .. } => {
                    let (from, to, _) = buf.steps[i];
                    if let Some(pairs) = self.merge_premises(from, to)
                        && expanded.insert(Self::pair_key(from, to))
                    {
                        for &(x, y) in pairs {
                            if explained.insert(Self::pair_key(x, y)) {
                                self.classes.explain(x, y, buf);
                            }
                        }
                    }
                }
                _ => {}
            }
            i += 1;
        }
        true
    }

    /// Add to `buf.children_b` the nodes an operator's laws compare children
    /// with: the unit, which a child in its class is dropped against, and the
    /// argument of each inverse child, which cancels against a child in its
    /// class. `explain_grouped` then explains those equalities too.
    /// The premises of a grouped step about to merge `a` and `b`, from the
    /// current classes: the nodes the step compares (see `explain_deep`),
    /// grouped by class, each member paired with the first of its class.
    /// `None` for a step that is not grouped.
    fn grouped_premises_now(
        &self,
        j: Justification<Cfg::G>,
        a: Cfg::G,
        b: Cfg::G,
    ) -> Option<Vec<(Cfg::G, Cfg::G)>> {
        let mut scratch = Vec::new();
        let mut list: Vec<Cfg::G> = Vec::new();
        let op = match j {
            Justification::Congruence { node_a, node_b } => {
                if self.is_ordered_node(node_a) {
                    return None;
                }
                self.collect_original_children(node_a, &mut list, &mut scratch);
                self.collect_original_children(node_b, &mut list, &mut scratch);
                self.node_op(node_a)
            }
            Justification::Normalize { node, normal } => {
                self.collect_original_children(node, &mut list, &mut scratch);
                list.push(normal);
                self.node_op(node)
            }
            // An inverse repair: one side is the other with an inverse pair cancelled
            // (or an inverse law applied); both sides' children, or the side itself when
            // it is not a node of the operator.
            Justification::InverseCancel { node_a, node_b } => {
                let op = self.node_op(node_b);
                for n in [node_a, node_b] {
                    if self.node_op(n) == op && !self.is_ordered_node(n) {
                        self.collect_original_children(n, &mut list, &mut scratch);
                    } else {
                        list.push(n);
                    }
                }
                op
            }
            Justification::Build { node, .. } => {
                let other = if a == node { b } else { a };
                self.for_each_child(node, |c, _| list.push(c));
                for &(g, m) in self.build_premises(j).unwrap_or(&[]) {
                    list.push(g);
                    list.push(m);
                    self.for_each_child(m, |c, _| list.push(c));
                }
                if self.build_collapsed(j) == Some(false) {
                    self.collect_original_children(other, &mut list, &mut scratch);
                } else {
                    list.push(other);
                }
                self.node_op(node)
            }
            _ => return None,
        };
        if let Some(u) = self.unit_node(op) {
            list.push(u);
        }
        if let Some(inv) = self.inverse_op(op) {
            // The inverse node's original argument: the cancellation compares the
            // argument the term was built with, not the class root it now stores. And
            // the inverse node a child's class holds (`b` after `b = inv(a)`): the
            // normalization finds it by probing `inv(x)` for each child `x`.
            let mut extra = Vec::new();
            for k in 0..list.len() {
                let c = list[k];
                if self.node_op(c) == inv {
                    self.collect_original_children(c, &mut extra, &mut scratch);
                }
                let root = self.classes.find_const(c);
                if let Some(n) = self.nodes.plain1.probe(&inv, &[root]) {
                    extra.push(n);
                    self.collect_original_children(n, &mut extra, &mut scratch);
                }
            }
            list.extend(extra);
        }
        list.sort_by_key(|c| self.classes.find_const(*c).to_usize());
        let mut pairs = Vec::new();
        let mut first = 0;
        for k in 1..list.len() {
            if self.classes.find_const(list[k]) != self.classes.find_const(list[first]) {
                first = k;
            } else if list[k] != list[first] {
                pairs.push((list[first], list[k]));
            }
        }
        Some(pairs)
    }

    /// The premises recorded when `a` and `b` were merged: the grouped pairs of
    /// a congruence, `Normalize` or `Build` step, or the rules and inverse
    /// nodes a completion step used. For explanation checkers.
    pub fn step_premises(&self, a: Cfg::G, b: Cfg::G) -> Option<&[(Cfg::G, Cfg::G)]> {
        self.merge_premises(a, b)
    }

    /// The merge-time premises recorded for the grouped step that merged `a`
    /// and `b` (`grouped_premises_now`).
    fn merge_premises(&self, a: Cfg::G, b: Cfg::G) -> Option<&[(Cfg::G, Cfg::G)]> {
        let &(s, e) = self.merge_premise_index.get(&Self::pair_key(a, b))?;
        Some(&self.merge_premise_pairs[s..e])
    }

    /// Whether `id`'s operator takes its children in order.
    fn is_ordered_node(&self, id: Cfg::G) -> bool {
        matches!(
            self.node_ref(id),
            NodeRef::Plain1(_)
                | NodeRef::Plain2(_)
                | NodeRef::Plain3(_)
                | NodeRef::PlainN(_)
                | NodeRef::Seq(_)
        )
    }

    fn law_witnesses(&self, op: Cfg::O, buf: &mut ProofBuf<Cfg::G>) {
        if let Some(u) = self.unit_node(op) {
            buf.children_b.push(u);
        }
        if let Some(inv) = self.inverse_op(op) {
            let n = buf.children_a.len() + buf.children_b.len();
            for k in 0..n {
                let c = if k < buf.children_a.len() {
                    buf.children_a[k]
                } else {
                    buf.children_b[k - buf.children_a.len()]
                };
                if self.node_op(c) == inv {
                    let mut args = Vec::new();
                    let mut scratch = Vec::new();
                    self.collect_original_children(c, &mut args, &mut scratch);
                    buf.children_b.extend(args);
                }
            }
        }
    }

    /// Order-normalized key for the explain-once set: `(a, b)` and `(b, a)`
    /// name the same explanation.
    fn pair_key(a: Cfg::G, b: Cfg::G) -> (usize, usize) {
        let (x, y) = (a.to_usize(), b.to_usize());
        if x <= y { (x, y) } else { (y, x) }
    }

    /// Explain every equality among `buf.children_a` and `buf.children_b`
    /// taken together: the children of both sides, sorted by class, and in
    /// each class every member against the first. A pairing that takes one
    /// child per class from each side misses the rest: `+(a, b)` and
    /// `+(a, a)` after `a = b` pair `a` with `a` and never cite `a = b`, and a
    /// child equal to the unit or cancelled by an inverse has no partner on
    /// the other side at all.
    fn explain_grouped(
        &self,
        buf: &mut ProofBuf<Cfg::G>,
        explained: &mut std::collections::HashSet<(usize, usize)>,
    ) {
        buf.group_a.clear();
        buf.group_a.extend_from_slice(&buf.children_a);
        buf.group_a.extend_from_slice(&buf.children_b);
        buf.group_a
            .sort_by_key(|c| self.classes.find_const(*c).to_usize());

        buf.children_a.clear();
        let mut first = 0;
        for k in 1..buf.group_a.len() {
            let c = buf.group_a[k];
            if self.classes.find_const(c) != self.classes.find_const(buf.group_a[first]) {
                first = k;
                continue;
            }
            let f = buf.group_a[first];
            if c != f {
                buf.children_a.push(f);
                buf.children_a.push(c);
            }
        }

        let mut k = 0;
        while k < buf.children_a.len() {
            let ca = buf.children_a[k];
            let cb = buf.children_a[k + 1];
            if explained.insert(Self::pair_key(ca, cb)) {
                self.classes.explain(ca, cb, buf);
            }
            k += 2;
        }
    }

    /// The premise pairs of a `Rewrite` step's rule instance: the node pairs
    /// the match and the right-hand side's construction need equal. `None`
    /// for any other justification, for a step with no recorded instance, and
    /// for an instance whose premise list is incomplete.
    pub fn rewrite_premises(&self, j: Justification<Cfg::G>) -> Option<&[(Cfg::G, Cfg::G)]> {
        let Justification::Rewrite { inst, .. } = j else {
            return None;
        };
        let i = inst as usize;
        if inst == crate::union_find::NO_INSTANCE || self.rule_partial.get(i) != Some(&false) {
            return None;
        }
        let start = self.rule_starts[i];
        let end = self
            .rule_starts
            .get(i + 1)
            .copied()
            .unwrap_or(self.rule_premises.len());
        Some(&self.rule_premises[start..end])
    }

    /// Open a rule instance for one match (`PROOFS` only; otherwise
    /// [`NO_INSTANCE`](crate::union_find::NO_INSTANCE)). Premises noted until
    /// [`end_rule_instance`](Self::end_rule_instance) belong to it.
    pub(crate) fn begin_rule_instance(&mut self) -> u32 {
        if !PROOFS {
            return crate::union_find::NO_INSTANCE;
        }
        debug_assert!(self.rule_open.is_none(), "rule instances do not nest");
        let id = u32::try_from(self.rule_starts.len())
            .ok()
            .filter(|&i| i != crate::union_find::NO_INSTANCE)
            .expect("rule instance count exceeds u32");
        self.rule_starts.push(self.rule_premises.len());
        self.rule_partial.push(false);
        self.rule_open = Some(id);
        id
    }

    /// The open instance, for the `Rewrite` steps its actions record.
    pub(crate) fn open_rule_instance(&self) -> u32 {
        self.rule_open.unwrap_or(crate::union_find::NO_INSTANCE)
    }

    pub(crate) fn end_rule_instance(&mut self) {
        self.rule_open = None;
    }

    /// Record that the open instance needs `a` and `b` equal. A no-op with no
    /// open instance, and for a node paired with itself.
    pub(crate) fn note_rule_premise(&mut self, a: Cfg::G, b: Cfg::G) {
        if PROOFS && a != b && self.rule_open.is_some() {
            self.rule_premises.push((a, b));
        }
    }

    /// Mark the open instance's premise list incomplete.
    pub(crate) fn note_rule_partial(&mut self) {
        if let Some(i) = self.rule_open {
            self.rule_partial[i as usize] = true;
        }
    }

    /// Drop the rule instances, build witnesses and creation-memo entries
    /// recorded after the given lengths: their nodes belong to a discarded
    /// scope.
    fn truncate_rule_instances(&mut self, len: ProofLens) {
        self.rule_starts.truncate(len.rule_starts);
        self.rule_partial.truncate(len.rule_starts);
        self.rule_premises.truncate(len.rule_premises);
        self.rule_open = None;
        self.build_starts.truncate(len.build_starts);
        self.build_collapsed.truncate(len.build_starts);
        self.build_premises.truncate(len.build_premises);
        self.merge_premise_pairs.truncate(len.merge_premise_pairs);
        for key in self
            .merge_premise_log
            .drain(len.merge_premise_log.min(self.merge_premise_log.len())..)
        {
            self.merge_premise_index.remove(&key);
        }
        for key in self
            .creation_log
            .drain(len.creation_log.min(self.creation_log.len())..)
        {
            self.creation_memo.remove(&key);
        }
    }

    /// Whether a `Build` step's build collapsed to a class (see
    /// `build_collapsed`); `None` for any other step.
    pub fn build_collapsed(&self, j: Justification<Cfg::G>) -> Option<bool> {
        let Justification::Build { inst, .. } = j else {
            return None;
        };
        self.build_collapsed.get(inst as usize).copied()
    }

    /// The splice witnesses of a `Build` step; `None` for any other step.
    pub fn build_premises(&self, j: Justification<Cfg::G>) -> Option<&[(Cfg::G, Cfg::G)]> {
        let Justification::Build { inst, .. } = j else {
            return None;
        };
        let i = inst as usize;
        let start = *self.build_starts.get(i)?;
        let end = self
            .build_starts
            .get(i + 1)
            .copied()
            .unwrap_or(self.build_premises.len());
        Some(&self.build_premises[start..end])
    }

    /// Record the node built for the client term `(op, given)`.
    fn remember_creation(&mut self, op: Cfg::O, given: &[(Cfg::G, usize)], id: Cfg::G) {
        let key = (op, given.to_vec());
        if self.creation_memo.insert(key.clone(), id).is_none() {
            self.creation_log.push(key);
        }
    }

    /// The children `explain_deep` takes as a congruence step's premises for
    /// `id`: the saved original children when the node has history, else
    /// its stored children. For clients auditing explanations.
    pub fn original_children(&self, id: Cfg::G) -> Vec<Cfg::G> {
        let mut out = Vec::new();
        let mut scratch = Vec::new();
        self.collect_original_children(id, &mut out, &mut scratch);
        out
    }

    fn collect_original_children(
        &self,
        id: Cfg::G,
        out: &mut Vec<Cfg::G>,
        ac_scratch: &mut Vec<Cfg::C>,
    ) {
        ac_scratch.clear();
        if self.nodes.original_children(id, out, ac_scratch) {
            for c in ac_scratch.iter() {
                out.push(Cfg::mset_child_id(c));
            }
            return;
        }
        self.for_each_child(id, |child, _mult| out.push(child));
    }

    // -----------------------------------------------------------------------
    // Rebuild — worklist-based congruence closure
    // -----------------------------------------------------------------------

    /// Rebuild to a plain-congruence-closed state.
    ///
    /// Plain congruence closure always runs. AC/ACI completion is opt-in through
    /// [`set_cc`](Self::set_cc); it is disabled by default. When enabled, two
    /// closures are interleaved (see `doc/design/06-ac-congruence-closure.md`
    /// section 8, rebuild = Kapur's Algorithm 3):
    /// - `rebuild_congruence`: ordinary worklist-driven
    ///   congruence closure (substitutes equal *atoms* into recanonicalized nodes);
    /// - `cc_round`: AC completion (substitutes
    ///   equal *sub-sums*), which canonization alone misses.
    ///
    /// A completion round may push new merges onto the worklist; we drain them with
    /// another congruence pass, then complete again, until a whole completion round
    /// adds nothing. Only [`CompletionOutcome::Converged`] reports that joint
    /// fixpoint. [`CompletionOutcome::Disabled`], [`CompletionOutcome::GoalMet`],
    /// [`CompletionOutcome::AbortedGrowthLimit`] and
    /// [`CompletionOutcome::AbortedWorkLimit`] guarantee plain congruence
    /// closure but not complete AC/ACI congruence closure. Inspect
    /// [`completion_outcome`](Self::completion_outcome) after each call.
    pub fn rebuild(&mut self) {
        // A rebuild ends any round left open by a fault inside it.
        self.round_open = false;
        // Terms the rebuild builds (completion's normal forms and rewrites) are the
        // engine's, not a client's: they carry no evidence node.
        let saved_evidence = std::mem::replace(&mut self.no_evidence, true);
        self.rebuild_inner();
        self.no_evidence = saved_evidence;
    }

    fn rebuild_inner(&mut self) {
        // Ordinary atom-level congruence closure always runs. AC completion runs only
        // when opted in (default off for divergence scoping — see the `cc` field docs).
        if !self.cc {
            // Canonization repair runs in plain mode too: it does not derive AC
            // consequences, it supplies the equalities the canonization laws already
            // *state* but whose stored spelling `add` chose from a non-monotone predicate
            // (see `canon_repair_round`). Its merges feed congruence, so the two run to a
            // joint fixpoint. The loop has no budget: the repair is purely subtractive
            // (inverse-pair cancellation), so each of its merges strictly reduces the class
            // count, and the fixpoint is bounded by the number of classes.
            loop {
                self.rebuild_congruence();
                // A node that could not be recanonicalized stops the rebuild: the caller
                // reports `take_width_error` and the run ends.
                if self.has_width_error() || !self.canon_repair_round() {
                    break;
                }
            }
            self.completion_outcome = Some(CompletionOutcome::Disabled);
            return;
        }
        // Multiple MSet symbols are supported: the per-class min-monomial pool stores a
        // separate least-monomial per completion op (step 3), and the round groups rules by op
        // (superposition/normalization filter on `r.op`, RHS via the node's own op column). Two
        // MSet ops therefore complete as independent rule sets sharing only the constant pool;
        // a class holding monomials of both (`a+b = a*b`) keeps each in its own column, and
        // union-find records the cross-op equality (Kapur's shared-constant case). Set (ACI)
        // completion is driven too: `completion_node_ids` yields both partitions, reducts
        // normalize in the op's count domain (idempotent clamp / mod-n / ℕ), and each rule
        // additionally superposes with its op's own axiom (Kapur §4 per-rule critical
        // pairs).
        let trace = std::env::var_os("AC_COMPLETE_TRACE").is_some();
        // Safety backstop against an expensive or nonterminating completion run (minting
        // critical-pair nodes): the configurable node-growth budget (see
        // `set_completion_node_budget`). If the AC node count grows past the budget beyond
        // where it started, we stop rather than continue materializing nodes. This is NOT a
        // termination argument or a work bound — it is a growth guard, and the
        // abort is REPORTED (`CompletionOutcome::AbortedGrowthLimit`), never silent.
        // Inside a lazy decision the budget is cumulative: growth counts from the
        // decision's start, so nodes minted by rule rounds and earlier rebuilds are charged.
        let budget = self.completion_node_budget;
        let start_nodes = self.decision_start.unwrap_or_else(|| self.node_count());
        self.cc_start_nodes = start_nodes;
        let basis_dump = self.basis_checks;
        let mut round = 0usize;
        // Watermark into the `touched` log: rules whose `(op, monomial)` changed since the
        // previous round are approximated by nodes touched (created or recanonicalized) in the
        // slice `touched[prev_mark..mark]`. Superposition (B) is incremental over this delta
        // (S3b): round 0 is a full pass (base case), each later round superposes only pairs
        // with ≥1 endpoint in the delta. A later full confirmation round compensates for
        // changes, such as a rule RHS shift, that this node-touch delta does not name.
        let mut prev_mark = 0usize;
        // Incremental rounds run until one finds nothing; then a single *full* confirmation
        // round checks the whole implemented rule set before reporting its operational
        // fixpoint. The node-touch delta misses a
        // pair only if a rule's RHS shifted without its node being recanonicalized (its own
        // class merged, not a child's); a full round closes any such pair. Convergence is
        // reported only when a *full* round is unchanged. This is an implementation stopping
        // condition, not a machine-checked completeness theorem. Full rounds run at the base
        // case and after an unchanged incremental round; their cost is input-dependent.
        let mut full = true; // round 0 is full (base case)
        loop {
            self.rebuild_congruence();
            if self.has_width_error() {
                self.completion_outcome = Some(CompletionOutcome::AbortedOverflow);
                return;
            }
            // A merge can reorient the rule that collapsed a node; the node is then a
            // rule again (`ac_collapsed_reoriented.egg`).
            self.unretire_irreducible_collapsed();
            // Debug builds check I5 on every congruence-closed state of the loop: the
            // stored minimal monomials are what the round orients its rules toward.
            #[cfg(debug_assertions)]
            self.debug_check_min_monomial_invariant();
            // And that no collapsed node is irreducible under the current rules and
            // laws: such a node is an equation completion never superposes.
            #[cfg(debug_assertions)]
            self.debug_check_no_irreducible_collapsed();
            // Goal-directed early stop (the lazy-check transaction): the pair
            // joined, so the question is answered — stop mid-closure. The
            // graph is plain-congruence-closed at this point, a valid state.
            if let Some((ga, gb)) = self.cc_goal
                && self.classes.find_const(ga) == self.classes.find_const(gb)
            {
                self.completion_outcome = Some(CompletionOutcome::GoalMet { rounds: round });
                return;
            }
            // A budget already spent (by the open lazy decision's rule rounds or by an
            // earlier rebuild of it) stops before a round: the round's rule scan and
            // reducibility pass cost rules squared before any in-round check runs.
            if self.decision_spent {
                // An earlier rebuild of the open lazy decision already stopped on a
                // budget: the decision is inconclusive, and its outcome stays the one
                // that rebuild reported. The graph is plain-congruence-closed here.
                return;
            }
            if self.node_count() - start_nodes > budget {
                self.abort_growth(start_nodes, budget, trace);
                return;
            }
            if basis_dump {
                self.cc_basis_dump(&format!("round {round} pre"));
            }
            let before = self.node_count();
            let mark = self.touched.len();
            let was_full = full;
            // `|`, not `||`: the A-only pass runs every iteration, its changes
            // and the AC round's alike drain through the same fixpoint.
            #[cfg(debug_assertions)]
            self.cc_mirror_enter_round();
            let cc_changed = self.cc_round(full, prev_mark, mark);
            #[cfg(debug_assertions)]
            self.cc_mirror_exit();
            let changed = cc_changed | self.a_round() | self.canon_repair_round();
            prev_mark = mark;
            if std::mem::take(&mut self.cc_overflow) {
                // Sound-but-incomplete stop, as for the growth budget, and reported. A
                // work stop the same round recorded is superseded, not left for the next
                // rebuild to read.
                self.cc_work_stop = None;
                self.rebuild_congruence();
                self.width_error.get_or_insert(MultOverflow);
                self.completion_outcome = Some(CompletionOutcome::AbortedOverflow);
                return;
            }
            if let Some(work) = self.cc_work_stop.take() {
                // The round stopped on its work budget: same sound-but-incomplete stop,
                // reported, and never read as a fixpoint (the round may have stopped
                // before changing anything).
                self.rebuild_congruence();
                let limit = self.completion_work_budget;
                self.completion_outcome = Some(CompletionOutcome::AbortedWorkLimit { work, limit });
                self.decision_spent = self.decision_start.is_some();
                if trace {
                    eprintln!("[ac-complete] ABORT: round work {work} > budget {limit}");
                }
                return;
            }
            // A round the node budget stopped mid-apply may report no change, so the
            // budget is checked before the fixpoint test, not after it.
            if self.node_count() - start_nodes > budget {
                self.abort_growth(start_nodes, budget, trace);
                return;
            }
            if trace {
                eprintln!(
                    "[ac-complete] round {round}{}: nodes {before} -> {} (+{}), changed={changed}",
                    if was_full { " (full)" } else { "" },
                    self.node_count(),
                    self.node_count() - before
                );
            }
            round += 1;
            if !changed {
                // Incremental round found nothing: confirm with a full round before exiting.
                // A full round that also finds nothing is the implemented fixpoint reported
                // by CompletionOutcome::Converged.
                if was_full {
                    // The exact cancelative closure runs at the fixpoint only: it merges
                    // classes without adding nodes, and each merge reopens completion.
                    #[cfg(debug_assertions)]
                    self.cc_mirror_enter();
                    let lattice_changed = self.lattice_round();
                    #[cfg(debug_assertions)]
                    self.cc_mirror_exit();
                    if lattice_changed {
                        full = false;
                        continue;
                    }
                    self.completion_outcome = Some(CompletionOutcome::Converged { rounds: round });
                    return;
                }
                full = true;
                continue;
            }
            // Made progress: stay incremental for the next round.
            full = false;
        }
    }

    /// The exact closure of a cancelative operator's equations, run when a full completion
    /// round finds nothing. Over the commutative semigroup (or monoid) freely generated by
    /// the classes, the cancelative congruence generated by equations `uᵢ = vᵢ` relates `x`
    /// and `y` exactly when `x − y` lies in the lattice `L ⊆ ℤⁿ` spanned by the vectors
    /// `uᵢ − vᵢ`: the quotient is cancelative, so it embeds in its universal group, which is
    /// `ℤⁿ / L`. Kapur's §5 inferences (cancel-close each rule, superpose disjoint pairs)
    /// cancel the common part of one equation at a time and do not reach every member of
    /// `L`: in tests/egg/cancel_lattice.egg `c1c3² = ∅` needs
    /// `c1c4² = c0²` added to two copies of `c4 = c0c3`, and no rule pair yields it.
    ///
    /// The step reads every node of the op (collapsed ones included: their equations still
    /// hold) as the row `e_class − Σ mult·e_child`, adds `e_unit` for a declared identity,
    /// `order·e_x` for every class under `:nilpotent` (which requires `:identity`, so the
    /// structure is a group of exponent `order`, cancelative whether or not `:cancellative`
    /// is declared; tests/egg/nilpotent_group_lattice.egg), and
    /// `e_x + e_inv(x)` for every inverse node. It brings the rows to echelon form over ℤ
    /// with exact integers, reduces each `e_class` to its coset representative (the entry at
    /// each pivot column in `[0, pivot)`), and merges classes with equal representatives.
    /// Two vectors in one coset reduce to one representative because a nonzero member of
    /// `L` has a leading entry that is a nonzero multiple of that column's pivot.
    ///
    /// Each merge is a consequence of the declared laws, so the step is sound; it adds no
    /// node, so it cannot grow the graph. A merge reopens completion: the caller runs
    /// another round, and the next fixpoint runs this step again.
    fn lattice_round(&mut self) -> bool {
        use num_bigint::BigInt;
        use num_traits::{Signed, Zero};
        let mut ops: Vec<Cfg::O> = self
            .completion_node_ids()
            .map(|g| self.node_op(g))
            .filter(|&op| {
                self.op_cancellative(op)
                    || matches!(self.op_clamp(op), CompletionClamp::Nilpotent { .. })
            })
            .collect();
        ops.sort_unstable();
        ops.dedup();
        let mut merges: Vec<(Cfg::G, Cfg::G)> = Vec::new();
        // Proof mode: per operator, the equations of its lattice system (each node
        // equals its class, the unit's class, each inverse node's class), and per
        // merge, the index of its operator's list. A lattice merge follows from the
        // whole system, so its premises are all of them.
        let mut op_prems: Vec<Vec<(Cfg::G, Cfg::G)>> = Vec::new();
        let mut merge_prem: Vec<usize> = Vec::new();
        // The operator of each merge, for its mirror tag.
        #[cfg(debug_assertions)]
        let mut merge_ops: Vec<Cfg::O> = Vec::new();
        let mut mono: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        for op in ops {
            let mut var: std::collections::HashMap<Cfg::G, usize> = Default::default();
            let mut classes: Vec<Cfg::G> = Vec::new();
            let mut sparse: Vec<Vec<(usize, BigInt)>> = Vec::new();
            let mut index = |g: Cfg::G, var: &mut std::collections::HashMap<Cfg::G, usize>| {
                *var.entry(g).or_insert_with(|| {
                    classes.push(g);
                    classes.len() - 1
                })
            };
            let nodes: Vec<Cfg::G> = self
                .completion_node_ids()
                .filter(|&g| self.node_op(g) == op && !self.is_evidence_node(g))
                .collect();
            if PROOFS {
                let mut prem: Vec<(Cfg::G, Cfg::G)> = nodes
                    .iter()
                    .map(|&g| (g, self.classes.find_const(g)))
                    .collect();
                if let Some(u) = self.unit_node(op) {
                    prem.push((u, self.classes.find_const(u)));
                }
                if let Some(inv) = self.inverse_op(op) {
                    for (_, x) in self.inverse_classes(inv) {
                        let root = self.classes.find_const(x);
                        if let Some(n) = self.nodes.plain1.probe(&inv, &[root]) {
                            prem.push((n, self.classes.find_const(n)));
                        }
                    }
                }
                op_prems.push(prem);
            }
            for node in nodes {
                mono.clear();
                self.node_monomial_into(node, &mut mono);
                let mut row = vec![(
                    index(self.classes.find_const(node), &mut var),
                    BigInt::from(1),
                )];
                for &(c, m) in &mono {
                    let k = index(self.classes.find_const(c), &mut var);
                    row.push((k, -BigInt::from(m.to_biguint())));
                }
                sparse.push(row);
            }
            if let Some(u) = self.unit_node(op) {
                sparse.push(vec![(
                    index(self.classes.find_const(u), &mut var),
                    BigInt::from(1),
                )]);
            }
            if let Some(inv) = self.inverse_op(op) {
                for (y, x) in self.inverse_classes(inv) {
                    let a = index(self.classes.find_const(y), &mut var);
                    let b = index(self.classes.find_const(x), &mut var);
                    sparse.push(vec![(a, BigInt::from(1)), (b, BigInt::from(1))]);
                }
            }
            let n = classes.len();
            if let CompletionClamp::Nilpotent { order } = self.op_clamp(op) {
                for k in 0..n {
                    sparse.push(vec![(k, BigInt::from(order))]);
                }
            }
            let mut rows: Vec<Vec<BigInt>> = sparse
                .into_iter()
                .map(|r| {
                    let mut d = vec![BigInt::zero(); n];
                    for (k, v) in r {
                        d[k] += v;
                    }
                    d
                })
                .filter(|d| d.iter().any(|v| !v.is_zero()))
                .collect();
            // Echelon form by Euclid's algorithm per column.
            let mut pivots: Vec<(usize, Vec<BigInt>)> = Vec::new();
            for col in 0..n {
                loop {
                    let mut best: Option<usize> = None;
                    for (i, r) in rows.iter().enumerate() {
                        if !r[col].is_zero()
                            && best.is_none_or(|b| r[col].abs() < rows[b][col].abs())
                        {
                            best = Some(i);
                        }
                    }
                    let Some(b) = best else { break };
                    let mut pivot = rows.swap_remove(b);
                    if pivot[col].is_negative() {
                        pivot.iter_mut().for_each(|v| *v = -&*v);
                    }
                    let mut reduced_all = true;
                    for r in rows.iter_mut() {
                        if r[col].is_zero() {
                            continue;
                        }
                        let q = &r[col] / &pivot[col];
                        for k in col..n {
                            let t = &q * &pivot[k];
                            r[k] -= t;
                        }
                        if !r[col].is_zero() {
                            reduced_all = false;
                        }
                    }
                    rows.retain(|r| r.iter().any(|v| !v.is_zero()));
                    if reduced_all {
                        pivots.push((col, pivot));
                        break;
                    }
                    rows.push(pivot);
                }
            }
            let mut by_rep: std::collections::HashMap<Vec<BigInt>, Cfg::G> = Default::default();
            for (k, &g) in classes.iter().enumerate() {
                let mut v = vec![BigInt::zero(); n];
                v[k] = BigInt::from(1);
                for (col, pivot) in &pivots {
                    let p = &pivot[*col];
                    let mut q = &v[*col] / p;
                    if (&v[*col] - &q * p).is_negative() {
                        q -= 1;
                    }
                    if !q.is_zero() {
                        for j in *col..n {
                            let t = &q * &pivot[j];
                            v[j] -= t;
                        }
                    }
                }
                match by_rep.entry(v) {
                    std::collections::hash_map::Entry::Occupied(e) => {
                        merges.push((*e.get(), g));
                        if PROOFS {
                            merge_prem.push(op_prems.len() - 1);
                        }
                        #[cfg(debug_assertions)]
                        merge_ops.push(op);
                    }
                    std::collections::hash_map::Entry::Vacant(e) => {
                        e.insert(g);
                    }
                }
            }
        }
        let mut changed = false;
        #[cfg(debug_assertions)]
        let mut merge_ops = merge_ops.into_iter();
        for (mi, (x, y)) in merges.into_iter().enumerate() {
            #[cfg(debug_assertions)]
            let op = merge_ops.next().expect("one operator per lattice merge");
            if self.classes.find_const(x) == self.classes.find_const(y) {
                continue;
            }
            let just = Justification::Cancellative {
                node_a: x,
                node_b: y,
            };
            #[cfg(debug_assertions)]
            self.cc_mirror_tag(cc_mirror::MergeWhy::Lattice { op });
            let m = if PROOFS {
                self.pending_premises = Some(op_prems[merge_prem[mi]].clone());
                let m = self.merge_in_classes(x, y, Some(just));
                self.pending_premises = None;
                m
            } else {
                self.merge_in_classes(x, y, None)
            };
            if let Some(m) = m {
                self.fold_min_monomial(
                    m.survivor,
                    m.absorbed,
                    m.absorbed_min_row,
                    m.absorbed_atomic,
                );
                self.worklist.push((m.absorbed_uses, m.survivor));
                changed = true;
            }
        }
        changed
    }

    /// Stop completion on the node budget: drain the pending congruence work so the
    /// graph is a valid (plain-congruence-closed) state, then report the abort through
    /// `completion_outcome`. The caller decides what to do with a partial completion
    /// (there is deliberately no assert here: the abort is an expected, reported
    /// condition on pathological inputs, and tests drive it directly with a tiny budget).
    fn abort_growth(&mut self, start_nodes: usize, budget: usize, trace: bool) {
        self.rebuild_congruence();
        let added = self.node_count() - start_nodes;
        self.completion_outcome = Some(CompletionOutcome::AbortedGrowthLimit {
            added_nodes: added,
            limit: budget,
        });
        self.decision_spent = self.decision_start.is_some();
        if trace {
            eprintln!(
                "[ac-complete] ABORT: added {added} nodes > budget {budget} without converging"
            );
        }
    }

    /// The equality a degenerate canonical form states (`crate::nary_canon::Normal`): a
    /// single child of multiplicity 1 is that child's class, and an empty list is the
    /// unit. Read from the canonization's own result, not from the stored span.
    fn degeneracy_pair(
        &self,
        node: Cfg::G,
        normal: crate::nary_canon::Normal<Cfg::G>,
    ) -> Option<(Cfg::G, Cfg::G)> {
        use crate::nary_canon::Normal;
        match normal {
            Normal::Single(g) => Some((node, g)),
            Normal::Unit => self.unit_node(self.node_op(node)).map(|u| (node, u)),
            Normal::Node | Normal::Empty | Normal::Overflow => None,
        }
    }

    /// Recanonize one parent node — find-canonicalize its children and apply the op's
    /// algebraic canonization laws (count clamp, identity unit-drop) — and record any
    /// resulting hash-cons collision or degenerate-arity merge into `self.collisions`.
    /// Shared by the absorbed-uses sweep and the became-a-unit sweep in
    /// [`rebuild_congruence`](Self::rebuild_congruence).
    /// [`recanonize_parent`](Self::recanonize_parent) outside `rebuild`, so a test can
    /// rewrite an indexed node's stored children mid-round and see the snapshot check in
    /// `saturate::debug_check_snapshot_contents` fire.
    #[cfg(all(test, debug_assertions))]
    pub(crate) fn test_recanonize_parent(&mut self, parent: Cfg::G) {
        self.recanonize_parent(parent);
    }

    fn recanonize_parent(&mut self, parent: Cfg::G) {
        let find = |g: Cfg::G| self.classes.find_const(g);
        // The op's identity as a *class* under the current union-find: recanonize drops it
        // from MSet/Set children (`f(x,e) = x`), so a summand that merged into the unit's
        // class after the node was built is dropped exactly as it would have been at build
        // (Kapur Lemma 4.3's normalization assumption). Field-precise captures keep the
        // borrows disjoint from `self.nodes`.
        let units = &self.unit_node;
        let classes = &self.classes;
        let unit_of = |op: Cfg::O| {
            units
                .get_by_key(&op)
                .copied()
                .map(|u| classes.find_const(u))
        };
        let touched_before = self.touched.len();
        let (normal, law) = self.nodes.recanonize_node(
            parent,
            find,
            unit_of,
            &mut self.g_buf,
            &mut self.mset_buf,
            &mut self.collisions,
            &mut self.touched,
            &self.ops,
        );
        // A law changed the node beyond `find`: a right-hand side built from its class may
        // now spell differently, and nothing in the delta names it (see the
        // `spelling_epoch` field).
        if law {
            self.spelling_epoch += 1;
        }
        // The span changed (recanonize pushes to `touched` only then) and still forms a
        // node: keep the class's min-monomial slot least (I5).
        if normal == crate::nary_canon::Normal::Node && self.touched.len() > touched_before {
            // A collapse retired the node because another rule's left-hand side was
            // contained in its old monomial; the new monomial may contain none, and then
            // the node is a rule completion must superpose. Reactivate it: the next round
            // re-tests reducibility and collapses it again if a rule still reduces it.
            // Left set, `Add{c2,c3,c5}` collapsed by `c2c4 → c2c3` became `Add{c2²,c5}` at
            // `C2 = C3`, and `C5 = C5·C5` was never derived (`ac_collapsed_recanon.egg`).
            // The flag is cleared before the refresh, which skips collapsed nodes: a node
            // active again takes part in the class's minimal monomial.
            if self.node_flags(parent) & crate::node_types::FLAG_AC_COLLAPSED != 0 {
                self.clear_node_flag(parent, crate::node_types::FLAG_AC_COLLAPSED);
            }
            self.refresh_min_monomial(parent);
        }
        // Canonization can shrink an MSet/Set node to a degenerate arity (a child merge
        // pushes a nilpotent count to 0, or coalesces/drops to a single summand): the node
        // then *equals* an existing class — empty ⇒ the unit, size-1 mult-1 ⇒ that child.
        // Recanonize (representation) can't express that equality, so record it as a merge
        // here (the congruence layer), alongside the hash-cons collisions. `and(a,b)` after
        // `a=b` becomes `{a}` = `a`; `xor(a,b)` after `a=b` becomes `{}` = the unit.
        if normal == crate::nary_canon::Normal::Overflow {
            self.width_error.get_or_insert(MultOverflow);
        }
        if let Some(pair) = self.degeneracy_pair(parent, normal) {
            self.normalizations.push(pair);
        }
    }

    /// Refresh the minimal monomial for every completion parent of a class whose order
    /// key a merge lowered (`key_lowered`). Lowering a child's key shrinks the parent in
    /// the key order without touching its span, so the recanonization sweep, which visits
    /// the absorbed side's parents only, does not see it; each such parent is folded into
    /// its class's minimal monomial as an in-place shrink (`refresh_min_monomial`). The walk covers
    /// the merged class's whole use list: the absorbed side's parents were refreshed
    /// already, and a second refresh of them changes nothing.
    fn refresh_key_lowered(&mut self) {
        while let Some(class) = self.key_lowered.pop() {
            let root = self.classes.find_const(class);
            let Some(repr) = self.classes.repr_id(root) else {
                continue;
            };
            let mut refresh = std::mem::take(&mut self.refresh_buf);
            refresh.clear();
            let list = self.classes.use_list_id(repr);
            refresh.extend(
                self.classes
                    .uses()
                    .iter(list)
                    .filter(|&p| self.ops.completion_column(self.node_op(p)).is_some()),
            );
            for &parent in &refresh {
                self.refresh_min_monomial(parent);
            }
            self.refresh_buf = refresh;
        }
    }

    /// Reactivate every collapsed completion node that no current rule of its operator
    /// reduces. A node is collapsed against the rules of the round that reduced it; a
    /// later merge can reorient every rule whose left-hand side it contains (the
    /// reducer's class takes the reducer as its minimal monomial), and the node is then
    /// an equation no rule represents and completion never superposes. The rules are
    /// read as `cc_round` reads them: active nodes whose monomial is greater than their
    /// class's right-hand side. A node holding an inverse pair stays collapsed: the
    /// group law reduces it. A reactivated node takes part in its class's minimal
    /// monomial, and the next round reads it as a rule; the full round that precedes a
    /// reported fixpoint superposes it. Reactivation only adds rules (a lower minimal
    /// monomial orients more nodes, never fewer), so one pass leaves no collapsed node
    /// irreducible. Runs after each congruence rebuild of the completion loop.
    fn unretire_irreducible_collapsed(&mut self) {
        use crate::multiset::multiset_subset;
        use crate::node_types::{FLAG_AC_COLLAPSED, FLAG_SUBSUMED};
        let mut collapsed: Vec<Cfg::G> = Vec::new();
        let mut rules: Vec<(Cfg::O, Vec<(Cfg::G, Cfg::M)>)> = Vec::new();
        let mut mono: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        let mut rhs: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        for id in self.completion_node_ids() {
            let flags = self.node_flags(id);
            if flags & FLAG_SUBSUMED != 0 {
                continue;
            }
            if flags & FLAG_AC_COLLAPSED != 0 {
                collapsed.push(id);
                continue;
            }
            self.node_monomial_into(id, &mut mono);
            if self.class_rhs_into(id, &mut rhs)
                && self.monomial_cmp_key(&mono, &rhs) == std::cmp::Ordering::Greater
            {
                rules.push((self.node_op(id), mono.clone()));
            }
        }
        for id in collapsed {
            let op = self.node_op(id);
            self.node_monomial_into(id, &mut mono);
            if rules
                .iter()
                .any(|(o, lhs)| *o == op && multiset_subset(lhs, &mono))
            {
                continue;
            }
            if let Some(inv) = self.inverse_op(op)
                && self.group_cancel_pairs(inv, &mut mono)
            {
                continue;
            }
            self.clear_node_flag(id, FLAG_AC_COLLAPSED);
            self.refresh_min_monomial(id);
        }
    }

    /// Ordinary worklist-driven congruence closure: drain the merge worklist,
    /// recanonicalizing the parents of each absorbed class and merging the
    /// resulting hash-cons collisions, to a fixpoint.
    fn rebuild_congruence(&mut self) {
        while let Some((absorbed_uses, survivor)) = self.worklist.pop() {
            self.collisions.clear();
            self.normalizations.clear();
            // Hot path: iterate the absorbed use list directly (no allocation). The body
            // mirrors `recanonize_parent` — it cannot be a method call here because the
            // use-list iterator holds `self.classes` for the whole loop, and only inline
            // field-disjoint borrows split around it.
            let mut refresh = std::mem::take(&mut self.refresh_buf);
            refresh.clear();
            for parent in self.classes.uses().iter(absorbed_uses) {
                let find = |g: Cfg::G| self.classes.find_const(g);
                let units = &self.unit_node;
                let classes = &self.classes;
                let unit_of = |op: Cfg::O| {
                    units
                        .get_by_key(&op)
                        .copied()
                        .map(|u| classes.find_const(u))
                };
                let touched_before = self.touched.len();
                let (normal, law) = self.nodes.recanonize_node(
                    parent,
                    find,
                    unit_of,
                    &mut self.g_buf,
                    &mut self.mset_buf,
                    &mut self.collisions,
                    &mut self.touched,
                    &self.ops,
                );
                // As in `recanonize_parent`: a law applied beyond `find` is a spelling
                // change the delta does not name.
                if law {
                    self.spelling_epoch += 1;
                }
                // As in `recanonize_parent`: a changed span that is still a node refreshes
                // the class's min-monomial slot (I5). Deferred past the loop, which holds
                // the use-list borrow.
                if normal == crate::nary_canon::Normal::Node && self.touched.len() > touched_before
                {
                    refresh.push(parent);
                }
                if normal == crate::nary_canon::Normal::Overflow {
                    self.width_error.get_or_insert(MultOverflow);
                }
                if let Some(pair) = self.degeneracy_pair(parent, normal) {
                    self.normalizations.push(pair);
                }
            }

            for &parent in &refresh {
                // As in `recanonize_parent`: a collapsed node whose monomial changed is
                // active again, and the next round re-tests it (`ac_collapsed_stuck.egg`).
                // Cleared before the refresh, which skips collapsed nodes.
                if self.node_flags(parent) & crate::node_types::FLAG_AC_COLLAPSED != 0 {
                    self.clear_node_flag(parent, crate::node_types::FLAG_AC_COLLAPSED);
                }
                self.refresh_min_monomial(parent);
            }
            self.refresh_buf = refresh;

            let current_surv = self.classes.find_const(survivor);
            let surv_repr = self.classes.repr_id(current_surv).unwrap();
            let surv_list = self.classes.use_list_id(surv_repr);
            self.classes.splice_uses(surv_list, absorbed_uses);
            self.refresh_key_lowered();

            // If this merge made the merged class an op's identity (unit) class, the
            // unit-drop law now applies to EVERY parent holding this class as a summand —
            // including parents on the *surviving* side, which the absorbed-uses sweep
            // never visits (their children's `find` did not change; their canonization
            // mode did). Sweep the full spliced use list; parents that are already
            // canonical early-return inside recanonize. Rare path (a class becomes a unit
            // class at most once per op), so the scratch collection is acceptable.
            // Iterate the unit-node map's own entries: its population is the
            // number of declared `:identity` elements (zero for EUF), where
            // the op-registry chain scanned every mset and set op per merge.
            let merged_is_unit = {
                let classes = &self.classes;
                self.unit_node
                    .iter()
                    .any(|(_, u)| classes.find_const(*u) == current_surv)
            };
            if merged_is_unit {
                let parents: Vec<Cfg::G> = self.classes.uses().iter(surv_list).collect();
                for parent in parents {
                    self.recanonize_parent(parent);
                }
            }

            let n_collisions = self.collisions.len();
            for i in 0..n_collisions + self.normalizations.len() {
                let (a, b, normalize) = if i < n_collisions {
                    let (a, b) = self.collisions[i];
                    (a, b, false)
                } else {
                    let (a, b) = self.normalizations[i - n_collisions];
                    (a, b, true)
                };
                let m = if PROOFS {
                    let just = if normalize {
                        Justification::Normalize { node: a, normal: b }
                    } else {
                        Justification::Congruence {
                            node_a: a,
                            node_b: b,
                        }
                    };
                    self.merge_in_classes(a, b, Some(just))
                } else {
                    self.merge_in_classes(a, b, None)
                };
                if let Some(m) = m {
                    self.fold_min_monomial(
                        m.survivor,
                        m.absorbed,
                        m.absorbed_min_row,
                        m.absorbed_atomic,
                    );
                    self.worklist.push((m.absorbed_uses, m.survivor));
                }
            }
        }
        // A key lowered by a merge that pushed no worklist entry of its own.
        self.refresh_key_lowered();
    }

    /// One A-only (`Seq`) inter-reduction round: the transfer of the AC
    /// repair to associativity-only operators, run inside the same completion
    /// loop (so only when completion is enabled — plain mode is untouched and
    /// its node counts stand).
    ///
    /// The gap it closes: build-time flattening splices a pure-`op`-sequence
    /// child into its parents, erasing the class reference, and a class can
    /// never *become* pure late (merges only add members, and an atom member
    /// never leaves) — so the one way an A-equation escapes congruence is two
    /// pure-sequence classes merging. That class then holds two distinct
    /// `op`-sequence spellings: a ground string equation `seq_1 = seq_2` that
    /// parents which spliced different spellings cannot see. Each such
    /// equation is oriented shortlex (longer to shorter, ties by element ids)
    /// and contiguous occurrences of the larger spelling inside other
    /// `op`-sequences are rewritten: the rewritten sequence is added and
    /// merged with its source, justification `ACInterReduction` (the same
    /// sub-term-for-class substitution shape as the AC case).
    ///
    /// Every rewrite is shortlex-decreasing, so a round terminates, and the
    /// loop above drains rounds to a joint fixpoint under the same budget and
    /// goal polls as the AC pass. **Deliberately no critical-pair chase**:
    /// completing a ground string system is Knuth-Bendix on a semi-Thue
    /// system, and the word problem for finitely presented monoids is
    /// undecidable — unlike the AC side, where Dickson's Lemma bounds the
    /// basis, there is no completeness theorem to aim for. This pass closes
    /// the single-substitution gap (the erased-reference case above) and
    /// stops; what it derives is sound, what it misses is documented.
    fn a_round(&mut self) -> bool {
        use crate::containers::DenseId;
        use crate::typed_routing::NodeIds;
        let n_seq = self.nodes.seq.len().to_usize();
        if n_seq == 0 {
            return false;
        }
        // (op, class) -> the class's `op`-sequence spellings.
        let mut groups: std::collections::HashMap<(Cfg::O, Cfg::G), Vec<Cfg::G>> =
            std::collections::HashMap::new();
        for i in 0..n_seq {
            let l = <Cfg::Ids as NodeIds>::LSeq::from_usize(i);
            let g = self.nodes.seq.get(l).global_id();
            // A proof-mode evidence node is a client's raw spelling, not a stored one.
            if self.is_evidence_node(g) {
                continue;
            }
            let cls = self.classes.find_const(g);
            groups.entry((self.node_op(g), cls)).or_default().push(g);
        }
        // Oriented rules: larger spelling -> the class's shortlex-least one, with the
        // two spellings' nodes (the rule's proof premise).
        #[allow(clippy::type_complexity)]
        let mut rules: Vec<(Cfg::O, Vec<Cfg::G>, Vec<Cfg::G>, Cfg::G, Cfg::G)> = Vec::new();
        let mut buf: Vec<Cfg::G> = Vec::new();
        for ((op, _cls), nodes) in groups.iter().filter(|(_, v)| v.len() > 1) {
            let mut spellings: Vec<(Vec<Cfg::G>, Cfg::G)> = Vec::with_capacity(nodes.len());
            for &n in nodes {
                self.seq_children(n, &mut buf);
                for e in buf.iter_mut() {
                    *e = self.classes.find_const(*e);
                }
                spellings.push((buf.clone(), n));
            }
            let (least, least_node) = spellings
                .iter()
                .min_by(|a, b| shortlex(&a.0, &b.0))
                .expect("non-empty spelling group")
                .clone();
            for (elems, n) in spellings {
                if shortlex(&elems, &least) == std::cmp::Ordering::Greater {
                    rules.push((*op, elems, least.clone(), n, least_node));
                }
            }
        }
        if rules.is_empty() {
            return false;
        }
        // Rewrite pass over the round-start sequences (nodes added below are
        // visited next round). One rewrite per node per round: the fixpoint
        // loop supplies the iteration.
        let mut changed = false;
        let mut new_children: Vec<Cfg::G> = Vec::new();
        for i in 0..n_seq {
            if self.cc_should_stop() {
                break;
            }
            let l = <Cfg::Ids as NodeIds>::LSeq::from_usize(i);
            let g = self.nodes.seq.get(l).global_id();
            if self.is_evidence_node(g) {
                continue;
            }
            let g_op = self.node_op(g);
            self.seq_children(g, &mut buf);
            // Proof mode: each stored element paired with the class root the rewrite
            // reads it as.
            let stored: Vec<Cfg::G> = if PROOFS { buf.clone() } else { Vec::new() };
            for e in buf.iter_mut() {
                *e = self.classes.find_const(*e);
            }
            for (op, lhs, rhs, lhs_node, rhs_node) in &rules {
                if *op != g_op || lhs.len() > buf.len() {
                    continue;
                }
                // Where `lhs` may be replaced: only at an offset where it spells a subterm of
                // the stored term. `:assoc` is associative, so every contiguous run is one.
                // A fold is not: `:assoc-left` stores `f(f(a, b), c)` as `[a, b, c]` and keeps
                // `f(a, f(b, c))` as `[a, f[b, c]]`, so in `[x, c, d]`, which is
                // `f(f(x, c), d)`, the run `[c, d]` spells no subterm, and the only run that
                // does is a prefix. Rewriting `[c, d]` there would derive `(x - c) - d =
                // (x - a) - b` from `a - b = c - d`: an unsound equality. A right fold keeps
                // only suffixes. The same rule bounds `:flatten` views (`flatten::spine`).
                let last = buf.len() - lhs.len();
                let allowed = match self.ops().info(*op).kind {
                    crate::registry::OpKind::A { dir, .. } => dir,
                    _ => crate::registry::AssocDir::Both,
                };
                let at = |s: usize| &buf[s..s + lhs.len()] == lhs.as_slice();
                let found = match allowed {
                    crate::registry::AssocDir::Both => (0..=last).find(|&s| at(s)),
                    crate::registry::AssocDir::Left => at(0).then_some(0),
                    crate::registry::AssocDir::Right => at(last).then_some(last),
                };
                let Some(s) = found else {
                    continue;
                };
                new_children.clear();
                new_children.extend_from_slice(&buf[..s]);
                new_children.extend_from_slice(rhs);
                new_children.extend_from_slice(&buf[s + lhs.len()..]);
                let nid = self.add(*op, &new_children);
                if self.classes.find_const(nid) != self.classes.find_const(g) {
                    let m = if PROOFS {
                        let mut prem = vec![(*lhs_node, *rhs_node)];
                        prem.extend(
                            stored
                                .iter()
                                .zip(buf.iter())
                                .filter(|(a, b)| a != b)
                                .map(|(&a, &b)| (a, b)),
                        );
                        self.pending_premises = Some(prem);
                        let m = self.merge_justified(
                            g,
                            nid,
                            Justification::ACInterReduction {
                                node_a: g,
                                node_b: nid,
                            },
                        );
                        self.pending_premises = None;
                        m
                    } else {
                        self.merge(g, nid)
                    };
                    changed |= m.is_some();
                }
                break;
            }
        }
        changed
    }

    /// One canonization-repair round: re-apply the canonization law whose applicability
    /// condition *opens* with later merges, so that applying it stays a function of the
    /// e-graph rather than of statement order. Returns `true` if it scheduled any merge (the
    /// caller drains congruence and calls again). Runs in every mode, plain included.
    ///
    /// # What this does and does not repair
    ///
    /// `add` decides each child's stored spelling once, from a predicate over the child's
    /// *class* at that moment, and those predicates are monotone in one direction. Two
    /// canonization laws are affected, and they need opposite treatment:
    ///
    /// | law | predicate | direction | reordering symptom |
    /// | --- | --- | --- | --- |
    /// | inverse cancel ([`group_cancel_pairs`](Self::group_cancel_pairs)) | `inv(x)`'s node resolves to a summand | **opens**: a later merge can create the pair | `(+ a (neg b))` built *before* `(union a b)` hides `+(a, neg(a)) = 0` |
    /// | AC flatten ([`flatten_ac_children`](Self::flatten_ac_children)) | `¬atomic(c)` | **closes**: `atomic` is monotone-true | `+(*(d,d), a)` built *before* `*(a,d,*(d,d))` hides `*(a,d,d,d) = *(a,d,*(d,d))` |
    ///
    /// Only the first is repaired here. An opening condition means the law simply was not
    /// tried at the moment it became applicable, and re-trying it costs nothing and can only
    /// shrink a monomial. Plain mode already applies this law at build, so *not* re-applying
    /// it leaves plain mode inconsistent with itself.
    ///
    /// The AC flatten row is deliberately **not** repaired, and the reason is worth recording
    /// because it is not obvious. `atomic` answers "is this class used as a non-same-op child"
    /// with *so far*; order independence would need it answered for the rest of the program,
    /// which no build-time predicate can do. Every way of removing the dependence is worse:
    /// always splice breaks `§5b`'s cancellation (`+(c, neg(c))` needs the pair to survive as
    /// two summands), never splice regresses the flatten fixtures, and deciding syntactically
    /// on inline-versus-by-name still breaks `§5b` for a `§5b` term written inline. Note that
    /// `atomic` *is* order-independent within a single term, since argument evaluation fixes
    /// the order; the dependence is only across statements, which is exactly the AC
    /// incompleteness the eager and lazy modes exist to close (`--derive-ac-eqs` proves
    /// `ac_flatten_order_dependence.egg`, plain declines it). Supplying the equality here
    /// instead was measured at +73% nodes on `rhs_mult_expr` under `--derive-ac-eqs`, for a
    /// consequence plain mode is not meant to derive.
    ///
    /// The A-only (`Seq`) analogue of the flatten row is a separate matter and *is* fixed, at
    /// the source rather than here: [`splice_raw_seq_children`](Self::splice_raw_seq_children)
    /// decides on the immutable child node id, so it mints nothing and cannot depend on merge
    /// order. That works for `Seq` and not for AC because an A-only operator has no
    /// `:identity` or `:inverse` (the property resolver rejects them without `:comm`), so no
    /// `§5b` pair depends on the nested spelling being kept.
    ///
    /// # Termination
    ///
    /// Cancellation is purely subtractive and each repair merge strictly reduces the class
    /// count, so the caller's fixpoint terminates with no growth budget and mints no node that
    /// needs one.
    fn canon_repair_round(&mut self) -> bool {
        // Nothing to re-decide unless a node was created or recanonicalized (`touched` grew)
        // or classes merged (`num_classes` fell) since the last round that found nothing.
        // Both counters are cheap and monotone within a rebuild, so a `rebuild` on an
        // unchanged graph — the common case for a run of `(check-eq ...)` commands — costs two
        // integer reads. `restore` resets the watermark, so a rolled-back graph is rescanned.
        let state = (
            self.touched.len(),
            crate::containers::IndexLike::as_usize(self.classes.num_classes()),
        );
        if self.repair_state == Some(state) {
            return false;
        }
        #[cfg(debug_assertions)]
        self.cc_mirror_enter();
        let changed = self.inverse_cancel_repair() | self.inverse_law_repair();
        #[cfg(debug_assertions)]
        self.cc_mirror_exit();
        if !changed {
            // Arm the skip only on a clean round. A round that merged left `touched` and
            // `num_classes` moved, and the caller drains congruence and calls again.
            self.repair_state = Some((
                self.touched.len(),
                crate::containers::IndexLike::as_usize(self.classes.num_classes()),
            ));
        }
        changed
    }

    /// Merge helper for the repair passes: skip an already-joined pair, fold the
    /// min-monomial pool, and queue the absorbed use-list for congruence. Mirrors
    /// `cc_round`'s local `do_merge`.
    fn repair_merge(&mut self, x: Cfg::G, y: Cfg::G, just: Justification<Cfg::G>) -> bool {
        if self.classes.find_const(x) == self.classes.find_const(y) {
            return false;
        }
        let m = if PROOFS {
            self.merge_in_classes(x, y, Some(just))
        } else {
            self.merge_in_classes(x, y, None)
        };
        match m {
            Some(m) => {
                self.fold_min_monomial(
                    m.survivor,
                    m.absorbed,
                    m.absorbed_min_row,
                    m.absorbed_atomic,
                );
                self.worklist.push((m.absorbed_uses, m.survivor));
                true
            }
            None => false,
        }
    }

    /// Re-apply inverse-pair cancellation (`x ∘ inv(x) = e`) to the stored MSet nodes.
    ///
    /// The build path cancels a pair only if the `inv(x)` node already existed *and* landed
    /// in a summand class at that moment; a later merge can create the pair, and nothing
    /// re-ran the law. `(+ a (neg b))` then `(union a b)` is the smallest witness: the node
    /// recanonicalizes to `+{a, neg-class}` and `find(neg(a)) == find(neg(b))` holds by
    /// congruence, but the summand pair is never cancelled, so `s = 0` is lost.
    ///
    /// Cancellation is purely subtractive, so unlike the two flatten laws it cannot grow a
    /// node and needs no cap. MSet only: the one normalization (`crate::nary_canon`)
    /// cancels inverse pairs under AC only, and this pass reaches it through
    /// `group_cancel_pairs` and `add`. Free for a graph with no `:inverse` op.
    ///
    /// Recanonization does not cancel inverse pairs: it rewrites a stored node's span in
    /// place, and a pair the law removes there would change the node's content without
    /// the `InverseCancel` justification this pass records.
    fn inverse_cancel_repair(&mut self) -> bool {
        // O(1) precheck: the inverse-op map is populated only by `:inverse`
        // declarations, so a program with no group operator pays two loads.
        // (This was an O(#ops) registry scan per repair round; measured at
        // the top of the QF_UF forward-path profile, where rounds run per
        // rebuild per assertion and no instance declares an inverse.)
        if self.inverse_op.is_empty() {
            return false;
        }
        // Collect first, apply second: `add`/`merge` below mutate the node store that
        // `completion_node_ids` walks.
        let mut work: Vec<(Cfg::O, Cfg::G, Vec<(Cfg::G, Cfg::M)>)> = Vec::new();
        let mut m: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        let ids: Vec<Cfg::G> = self.completion_node_ids().collect();
        for gid in ids {
            if !matches!(self.node_ref(gid), NodeRef::MSet(_)) {
                continue;
            }
            let op = self.node_op(gid);
            let Some(inv) = self.inverse_op(op) else {
                continue;
            };
            self.node_monomial_into(gid, &mut m);
            if self.group_cancel_pairs(inv, &mut m) {
                work.push((op, gid, std::mem::take(&mut m)));
            }
        }
        let mut scratch: Vec<Cfg::C> = Vec::new();
        let mut changed = false;
        for (op, gid, ms) in work {
            // `add_mset` resolves the degenerate results itself: a fully cancelled monomial
            // is the unit (`+(a, neg(a)) → {} = 0`) and a single mult-1 residue is that
            // class. Cancellation only lowers the counts of a stored node's monomial.
            let c = self
                .add_monomial(op, &ms, &mut scratch)
                .expect("cancellation only lowers the counts of a stored monomial");
            #[cfg(debug_assertions)]
            self.cc_mirror_tag(cc_mirror::MergeWhy::InverseRepair {
                op,
                node: gid,
                reduct: cc_mirror::mono(&ms),
            });
            changed |= self.repair_merge(
                c,
                gid,
                Justification::InverseCancel {
                    node_a: c,
                    node_b: gid,
                },
            );
            #[cfg(debug_assertions)]
            self.cc_mirror_untag();
        }
        changed
    }

    /// The nodes `inv(x)` of the unary op `inv`, as `(node, class of x)`: a scan of the
    /// unary partition.
    fn inverse_nodes(&self, inv: Cfg::O) -> Vec<(Cfg::G, Cfg::G)> {
        use crate::typed_routing::NodeIds;
        let n = self.nodes.plain1.len().to_usize();
        let mut out = Vec::new();
        for i in 0..n {
            let node = self
                .nodes
                .plain1
                .get(<Cfg::Ids as NodeIds>::L1::from_usize(i));
            if node.op() == inv {
                out.push((node.global_id(), self.classes.find_const(node.children[0])));
            }
        }
        out
    }

    /// `(class of inv(x), class of x)` over the nodes of `inv`, sorted by the first: the
    /// reverse of `inverse_class`, answering which class a class is the inverse of.
    pub(crate) fn inverse_classes(&self, inv: Cfg::O) -> Vec<(Cfg::G, Cfg::G)> {
        let mut out: Vec<(Cfg::G, Cfg::G)> = self
            .inverse_nodes(inv)
            .into_iter()
            .map(|(node, x)| (self.classes.find_const(node), x))
            .collect();
        out.sort_unstable();
        out.dedup();
        out
    }

    /// The consequences of the group law `x ∘ inv(x) = e` that cancelling pairs inside one
    /// monomial cannot reach, over the nodes of every `:inverse` op (the `InvMatching`,
    /// `InvUnitFree` and `NilpotentInverseCP` hypotheses of the completeness proof):
    /// - `inv(a) = inv(c)` gives `a = c`, and the node `inv(inv(x))` equals `x`
    ///   (`{a, inv a} = ∅ = {c, inv c}` cancelled on the shared inverse);
    /// - with `:identity e`: `inv(x) = e` gives `x = e` and `x = e` gives `inv(x) = e`
    ///   (`{x, inv x} = ∅` with the unit dropped);
    /// - with `:nilpotent k`: `inv(x) = x^(k−1)` (`x^k = ∅` and `{x, inv x} = ∅` overlap
    ///   on `x`), and for `inv(x)` of class `y ≠ x`, `y^(k−1) = x` (the overlap on `y`,
    ///   whether or not the node `inv(y)` exists); both nodes are built. A self-inverse
    ///   class is not exempt: for odd `k` its `x^(k−1)` normalizes to the unit, so `x = e`.
    ///
    /// Collect over a snapshot of the union-find, then apply through `repair_merge` and
    /// `add_monomial`, so `restore` rolls everything back. The whole unary partition is
    /// read, not the touched log: the first premise is a merge of two classes each holding
    /// an inverse node, which recanonizes neither node. Free for a graph with no `:inverse`
    /// op; otherwise it runs only when `canon_repair_round` sees a change.
    fn inverse_law_repair(&mut self) -> bool {
        if self.inverse_op.is_empty() {
            return false;
        }
        let ops: Vec<(Cfg::O, Cfg::O)> = self.inverse_op.iter().copied().collect();
        let mut merges: Vec<(Cfg::G, Cfg::G)> = Vec::new();
        // `(op, base, k−1, target)`: the node `base^(k−1)` to build and merge with `target`.
        let mut powers: Vec<(Cfg::O, Cfg::G, Cfg::M, Cfg::G)> = Vec::new();
        // The inference each entry of `merges` and of `powers` is, for its mirror tag.
        #[cfg(debug_assertions)]
        let mut merge_why: Vec<(Cfg::O, cc_mirror::InvRule<Cfg::G>)> = Vec::new();
        #[cfg(debug_assertions)]
        let mut power_why: Vec<cc_mirror::InvRule<Cfg::G>> = Vec::new();
        for (op, inv) in ops {
            let nodes = self.inverse_nodes(inv);
            if nodes.is_empty() {
                continue;
            }
            let unit = self.unit_node(op).map(|u| self.classes.find_const(u));
            let power = match self.ops.info(op).kind {
                OpKind::MSet {
                    clamp: crate::registry::Clamp::Nilpotent { order },
                    ..
                } => Some(
                    Cfg::M::try_from_u64(u64::from(order) - 1)
                        .expect("a u8 nilpotent order fits every multiplicity width"),
                ),
                _ => None,
            };
            // `(class of inv(x), class of x)`, sorted: equal first components are two
            // inverse nodes in one class.
            let mut classes: Vec<(Cfg::G, Cfg::G)> = Vec::with_capacity(nodes.len());
            for &(node, x) in &nodes {
                let y = self.classes.find_const(node);
                classes.push((y, x));
                if let Some(e) = unit {
                    if y == e && x != e {
                        merges.push((x, node));
                        #[cfg(debug_assertions)]
                        merge_why.push((op, cc_mirror::InvRule::R2InvUnit { node }));
                    }
                    if x == e && y != e {
                        merges.push((node, x));
                        #[cfg(debug_assertions)]
                        merge_why.push((op, cc_mirror::InvRule::R2UnitInv { node }));
                    }
                }
                if let Some(k) = power {
                    powers.push((op, x, k, node));
                    #[cfg(debug_assertions)]
                    power_why.push(cc_mirror::InvRule::R4 { node });
                    if y != x {
                        powers.push((op, y, k, x));
                        #[cfg(debug_assertions)]
                        power_why.push(cc_mirror::InvRule::R5 { node });
                    }
                }
            }
            classes.sort_unstable();
            for w in classes.windows(2) {
                if w[0].0 == w[1].0 && w[0].1 != w[1].1 {
                    merges.push((w[0].1, w[1].1));
                    #[cfg(debug_assertions)]
                    merge_why.push((op, cc_mirror::InvRule::R1Inj));
                }
            }
            for &(node, x) in &nodes {
                // `x` holds some `inv(z)`, so `node` is `inv(inv(z))`.
                if let Ok(i) = classes.binary_search_by(|p| p.0.cmp(&x)) {
                    merges.push((node, classes[i].1));
                    #[cfg(debug_assertions)]
                    merge_why.push((op, cc_mirror::InvRule::R1Inv { node }));
                }
            }
        }
        let mut changed = false;
        #[cfg(debug_assertions)]
        let mut merge_why = merge_why.into_iter();
        for (a, b) in merges {
            #[cfg(debug_assertions)]
            {
                let (op, rule) = merge_why.next().expect("one inference per merge");
                self.cc_mirror_tag(cc_mirror::MergeWhy::InverseLaw { op, rule });
            }
            changed |= self.repair_merge(
                a,
                b,
                Justification::InverseCancel {
                    node_a: a,
                    node_b: b,
                },
            );
            #[cfg(debug_assertions)]
            self.cc_mirror_untag();
        }
        let mut scratch: Vec<Cfg::C> = Vec::new();
        #[cfg(debug_assertions)]
        let mut power_why = power_why.into_iter();
        for (op, base, k, target) in powers {
            let c = self
                .add_monomial(op, &[(base, k)], &mut scratch)
                .expect("a count below the nilpotent order fits every multiplicity width");
            #[cfg(debug_assertions)]
            {
                let rule = power_why.next().expect("one inference per power");
                self.cc_mirror_tag(cc_mirror::MergeWhy::InverseLaw { op, rule });
            }
            changed |= self.repair_merge(
                c,
                target,
                Justification::InverseCancel {
                    node_a: c,
                    node_b: target,
                },
            );
            #[cfg(debug_assertions)]
            self.cc_mirror_untag();
        }
        changed
    }

    /// One AC congruence-completion round (Kapur FSCD 2021 Algorithm 1, the steps our
    /// rebuild otherwise omits). Returns `true` if it scheduled any new merge.
    ///
    /// Reading each non-subsumed AC node `+M = d` as a ground rule `+M → d`,
    /// for each pair of partners found through the class use-lists (same op,
    /// sharing ≥1 child class):
    ///
    /// - **(A) inter-reduction + Collapse** — if `A ⊊ M`, the sub-sum `+A` equals `a`,
    ///   so the residual `(M − A) ⊎ {a}`, **normalized to a fixpoint**, equals `d`:
    ///   merge, then **mark `+M` subsumed** so it leaves the active set. The collapse
    ///   is intended to maintain the active-rule antichain required by the conditional
    ///   Dickson argument (design doc §6b).
    /// - **(B) superposition** — if `A` and `M` overlap but neither contains the other,
    ///   build the lcm `AB`, **normalize both reducts** `(AB−M)⊎{d}` and `(AB−A)⊎{a}`
    ///   to normal form, and merge if they still differ (design doc §4b, §6 (B)).
    ///
    /// Disjoint partners are skipped (trivial critical pair). The crucial corrections
    /// over a naïve materialize-and-merge (design §6b): every reduct is reduced to
    /// **normal form before** being materialized (a raw reduct can be a superset of an
    /// existing rule's LHS, hence itself reducible, and would persist as a runaway
    /// superposition source), and reducible source rules are **collapsed** (subsumed).
    ///
    /// Completion collapse is the non-deletable form of Kapur/Conchon's rule retirement:
    /// the node and the equality it established stay in the DAG, but completion's
    /// active-rule projection skips it, so it is no longer a completion partner.
    /// `FLAG_AC_COLLAPSED` does not remove the node from matching; user-level
    /// `FLAG_SUBSUMED` does.
    /// One AC completion round. Superposition (B) is incremental (S3b): when `full` is
    /// false, only critical pairs with ≥1 endpoint among the *delta rules* (nodes touched
    /// in `self.touched[delta_lo..delta_hi]`, i.e. created or recanonicalized since the
    /// previous round) are generated. A later full round rechecks every pair, including
    /// old×old pairs whose effective RHS changed without touching their node. `full`
    /// generates every pair. The (A′)
    /// collapse/normalize pass and the antichain `reducible` check stay full scans: a small
    /// new rule must still be able to collapse a large old one.
    fn cc_round(&mut self, full: bool, delta_lo: usize, delta_hi: usize) -> bool {
        use crate::multiset::{
            NfIndex, NfRuleRef, NfRules, multiset_disjoint, multiset_lcm_into, multiset_subset,
            multiset_subtract_into, try_multiset_union, try_normalize_ms_into,
            try_normalize_nilpotent_into, try_normalize_set_into,
        };
        // A sum, product, or normal form past the configured width ends the round: the
        // pair cannot be represented, so completion stops there (`rebuild` reports
        // `CompletionOutcome::AbortedOverflow` and records the error) instead of panicking.
        let overflow = std::cell::Cell::new(false);
        // The round's work meter, in rule containment tests: the reducibility pass and
        // every normalization step charge it. A round past `completion_work_budget`
        // stops and leaves the work spent in `cc_work_stop` for `rebuild` to report. A
        // round over a large rule set costs targets times rules while minting almost
        // nothing, which the node budget cannot see.
        let work = std::cell::Cell::new(0u64);
        let work_limit = self.completion_work_budget;
        let multiset_union = |a: &[(Cfg::G, Cfg::M)], b: &[(Cfg::G, Cfg::M)]| {
            try_multiset_union(a, b).unwrap_or_else(|_| {
                overflow.set(true);
                Vec::new()
            })
        };

        // Canonical monomial of a completion node as sorted (class-repr, mult): coalesced
        // multiplicities for an MSet op, deduped set (all mult 1) for a Set (ACI) op.
        // Delegates to `node_monomial_into`, which dispatches on the node's representation.
        let multiset_of = |eg: &Self, id: Cfg::G| -> Vec<(Cfg::G, Cfg::M)> {
            let mut out = Vec::new();
            eg.node_monomial_into(id, &mut out);
            out
        };

        use crate::node_types::{FLAG_AC_COLLAPSED, FLAG_SUBSUMED};

        // Completion's active set excludes nodes that are user-subsumed (not matchable)
        // OR AC-collapsed (reducible by a smaller rule). Either way they are not rules.
        let inactive = FLAG_SUBSUMED | FLAG_AC_COLLAPSED;

        // Each active AC node is a candidate rule `+M → rhs(class)`, where the RHS comes
        // from the per-class slot (`class_rhs_into`: `{class}` if atomic, else the stored
        // `min_monomial` monomial, §9a) — not recomputed per round. The orientation guard keeps
        // only nodes whose own monomial `M` is strictly `≫_f`-greater than that RHS: those
        // are the currently oriented rules (a node equal to the maintained class candidate
        // is no rule, and a
        // mis-oriented `M ≺ rhs` is dropped, §9b axis-2a). `node` lets us collapse it.
        struct Rule<G, O, M> {
            /// The typed op id, not a widened `usize` copy of one. Storing the id itself
            /// keeps the row at the config's op width and — more to the point — leaves
            /// nothing to re-mint: the round used to spend a masking
            /// `Cfg::O::from_usize` per rule to undo a `to_usize` performed a few lines
            /// above, and only the op's own registration bound kept that honest.
            op: O,
            lhs: Vec<(G, M)>,
            rhs: Vec<(G, M)>,
            node: G,
            /// The node whose monomial is `rhs` (the class's minimal monomial node,
            /// the class root for an atomic class, the unit for the unit's class):
            /// the rule is the equality `node = rhs_node`, its proof premise.
            rhs_node: G,
        }
        let mut rules: Vec<Rule<Cfg::G, Cfg::O, Cfg::M>> = Vec::new();
        let mut rhs_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        // Iterate the AC node partition directly (ascending global id), not all nodes: the
        // `is_mset` filter is implicit and the non-AC majority is never visited.
        for gid in self.completion_node_ids() {
            if self.node_flags(gid) & inactive != 0 {
                continue;
            }
            let op = self.node_op(gid);
            let lhs = multiset_of(self, gid);
            if !self.class_rhs_into(gid, &mut rhs_buf) {
                continue;
            }
            // Read-time orientation guard (§9b): only `M ≫ rhs` is a rule.
            if self.monomial_cmp_key(&lhs, &rhs_buf) == std::cmp::Ordering::Greater {
                rules.push(Rule {
                    op,
                    lhs,
                    rhs: rhs_buf.clone(),
                    node: gid,
                    rhs_node: self.class_rhs_node(gid),
                });
            }
        }
        // Dedup the reducer/superposition set by (op, LHS). Congruent AC nodes can
        // recanonicalize to the same monomial after a child merge without being hash-consed
        // into one node, so the same rule `+M → r` appears as several nodes. Kapur step 2
        // discards a duplicate equation and keeps one; here we keep the lowest-node-id copy
        // as the canonical rule and drop the rest from `rules`. This is what makes the active
        // set Kapur-*reduced* (no LHS reducible by another's), not merely a strict-containment
        // antichain: identical-LHS copies were the whole measured gap between `reducible_pairs`
        // and the ground-truth `kapur_lhs_reducible` (ac_invariants). The dropped copies are
        // NOT lost: they remain in `targets`, so (A′) still collapses each (its monomial
        // reduces to the shared RHS via the kept rule) and still merges any differing-RHS copy
        // (the implied equality fires through `targets`, not `rules`). Without the dedup, every
        // copy reduces every other copy, so they mutually collapse and the rule vanishes
        // entirely (the §6b "merge before mark" / self-reduction hazard, at the set level).
        // Clone-free: sort by (op, lhs, node) with borrowed
        // comparisons, drop adjacent (op, lhs) duplicates keeping the first (= lowest node
        // id), then restore node order for the (B) binary search.
        rules.sort_unstable_by(|x, y| {
            x.op.cmp(&y.op)
                .then_with(|| x.lhs.cmp(&y.lhs))
                .then_with(|| x.node.cmp(&y.node))
        });
        rules.dedup_by(|later, earlier| later.op == earlier.op && later.lhs == earlier.lhs);

        // The (B) partner search binary-searches `rules` by global node id, so it must be
        // sorted by `node`. Distinct nodes ⇒ strictly sorted.
        rules.sort_unstable_by_key(|r| r.node);
        debug_assert!(rules.windows(2).all(|w| w[0].node < w[1].node));

        // Delta rule-node set for incremental (B): sorted, dedup'd node ids touched since
        // the previous round. `touched` may contain duplicates; sort+dedup once, then test
        // a rule's membership by binary search (mirrors the `rules` binary-search idiom).
        let delta: Vec<Cfg::G> = if full {
            Vec::new()
        } else {
            let mut d: Vec<Cfg::G> = self.touched[delta_lo..delta_hi].to_vec();
            d.sort_unstable();
            d.dedup();
            d
        };
        let in_delta = |n: Cfg::G| -> bool { full || delta.binary_search(&n).is_ok() };

        // Reducibility flag per rule: a rule whose LHS strictly contains another rule's LHS
        // (same op) is reducible by it, so collapse will retire it. Kapur superposes only
        // over the inter-reduced *antichain*, never over a reducible rule (FSCD'21 Algo 1:
        // collapse before superpose). The batch round collapses these only on the *next*
        // round, so excluding them as (B) sources/partners here is what keeps the active
        // set an antichain within the round and stops the critical-pair blowup.
        // O(rules²) over the small active set; acceptable while the worklist rewrite (S3b)
        // is pending.
        let phase_time = std::env::var_os("AC_PHASE_TIME").is_some();
        let t_reducible = std::time::Instant::now();
        let reducible: Vec<bool> = (0..rules.len())
            .map(|i| {
                rules.iter().enumerate().any(|(j, rj)| {
                    work.set(work.get() + 1);
                    j != i
                        && rj.op == rules[i].op
                        && rj.lhs != rules[i].lhs
                        && multiset_subset(&rj.lhs, &rules[i].lhs)
                })
            })
            .collect();
        let dt_reducible = t_reducible.elapsed();
        if work.get() > work_limit {
            self.cc_work_stop = Some(work.get());
            return false;
        }

        // Build a normal form as a node, one entry per distinct summand, into a reused
        // scratch. The combinators that form these monomials (`multiset_union`) already
        // panic on a sum past the width, so an overflow here is the same condition.
        let mut mat_buf: Vec<Cfg::C> = Vec::new();
        // A materialized monomial is a normal form under the round's rules. If hash-consing
        // returns a node an earlier round collapsed (against a rule since retired or
        // reoriented), that node is irreducible now and must be a rule again: otherwise
        // its superpositions are never generated. `ac_collapsed_recanon.egg`: the normal
        // form `c2²c5` of `c2c4c5` was such a node, and `C5 = C5·C5` was never derived.
        // Reactivation counts as a change, so the round loop does not report a fixpoint
        // before the node is processed. The node is active again, so it takes part in
        // its class's minimal monomial (I5): the refresh folds it in. Without it the
        // stored minimal monomial can stay on a node this round collapses, when the
        // reactivated node is the normal form of the class's own minimal monomial under a
        // rule a merge reoriented (`ac_reactivate_min_monomial.egg`).
        let reactivated = std::cell::Cell::new(false);
        let materialize =
            |eg: &mut Self, op: Cfg::O, ms: &[(Cfg::G, Cfg::M)], buf: &mut Vec<Cfg::C>| {
                let id = eg.add_monomial(op, ms, buf).ok()?;
                if matches!(eg.node_ref(id), NodeRef::MSet(_) | NodeRef::Set(_))
                    && eg.node_flags(id) & crate::node_types::FLAG_AC_COLLAPSED != 0
                {
                    eg.clear_node_flag(id, crate::node_types::FLAG_AC_COLLAPSED);
                    eg.refresh_min_monomial(id);
                    reactivated.set(true);
                }
                Some(id)
            };
        let do_merge = |eg: &mut Self, x: Cfg::G, y: Cfg::G, just: Justification<Cfg::G>| -> bool {
            if eg.classes.find_const(x) == eg.classes.find_const(y) {
                return false;
            }
            let m = if PROOFS {
                eg.merge_in_classes(x, y, Some(just))
            } else {
                eg.merge_in_classes(x, y, None)
            };
            match m {
                Some(m) => {
                    eg.fold_min_monomial(
                        m.survivor,
                        m.absorbed,
                        m.absorbed_min_row,
                        m.absorbed_atomic,
                    );
                    eg.worklist.push((m.absorbed_uses, m.survivor));
                    true
                }
                None => false,
            }
        };

        // Collect work over pairs of rules (same op), then apply (so the rule set we
        // normalize against does not shift mid-scan). Superposition (B) and collapse (A)
        // both range over *rules*: Kapur superposes/inter-reduces rule left sides, and a
        // class's minimal monomial (a normal form) is never a rule, so it cannot be a
        // source or a collapse target. The search ranges over the `rules` Vec directly
        // (already the small active set), via an all-pairs loop.
        //   targets — (A): collapse a node's class into its residual's normal form.
        //   crit    — (B): merge the normal forms of the two lcm reducts.
        // Each critical pair carries its ORIGIN so the close-time merge records the
        // faithful proof justification (pairwise superposition vs. per-rule semantic
        // axiom CP vs. cancelative closure) instead of a catch-all label.
        #[derive(Clone, Copy)]
        enum CpOrigin {
            Superposition,
            AxiomCp,
            Cancellative,
        }
        let mut crit: Vec<(
            Cfg::O,
            CpOrigin,
            Vec<(Cfg::G, Cfg::M)>,
            Vec<(Cfg::G, Cfg::M)>,
        )> = Vec::new();
        // One mirror tag per entry of `crit`: which pair it is and of which rules.
        #[cfg(debug_assertions)]
        let mut crit_why: Vec<cc_mirror::PairWhy<Cfg::G>> = Vec::new();
        // Proof mode: per entry of `crit`, the equalities its reducts came from (the
        // rules' `node = rhs_node` pairs and the inverse nodes a group-law pair used).
        // The normalization's own rules are added when the pair is closed.
        let mut crit_prem: Vec<Vec<(Cfg::G, Cfg::G)>> = Vec::new();
        let rule_pair = |r: &Rule<Cfg::G, Cfg::O, Cfg::M>| (r.node, r.rhs_node);

        // (A′) Normalize every active monomial node against the rules and merge its
        // normal form back in (Kapur Algo 2 step 2, "normalize Sf"). This subsumes plain
        // inter-reduction (A): a node +{a,b,neg(c)} with rule +{a,b}→{c} reduces to
        // +{c,neg(c)}, which is *materialized* so the ordinary matcher reaches it
        // (design §5b). `(op, monomial, class, node)`. A node that is itself a rule is
        // collapsed by the collapse pass, which identifies rules on its own (design §6b);
        // this list carried an `is_rule` flag no reader used, at O(rules) per node (bug #10).
        let t_gen = std::time::Instant::now();
        let mut targets: Vec<(Cfg::O, Vec<(Cfg::G, Cfg::M)>, Cfg::G, Cfg::G)> = Vec::new();
        // AC partition only, same as the rules scan (no full-graph walk, no `is_mset` filter).
        for gid in self.completion_node_ids() {
            if self.node_flags(gid) & inactive != 0 {
                continue;
            }
            let op = self.node_op(gid);
            targets.push((
                op,
                multiset_of(self, gid),
                self.classes.find_const(gid),
                gid,
            ));
        }

        // (B) Superposition critical pairs over pairs of *rules* sharing ≥1 child class,
        // neither containing the other (overlap). Partners are found via the use-lists
        // (`iter_uses`), not an O(rules²) all-pairs scan: a partner of rule `+M` must
        // share a child with `M`, so it appears in some `iter_uses(x)` for `x ∈ M`. `rules`
        // is built in node-id order, so it is sorted by `node`; look a partner's rule up by
        // binary search (no map, no per-round allocation). Each unordered pair is processed
        // once (`ti.node < partner.node`). Both reducts are normalized before merge.
        let mut partner_buf: Vec<Cfg::G> = Vec::new();
        // Reusable temporaries for the (B) reduct arithmetic: the
        // lcm and residual are per-pair scratch; only the stored reducts (`crit` entries)
        // allocate. Grown once, reused across every pair.
        let mut ab_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        let mut sub_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        let mut delta_skipped = 0usize;
        let delta_in_rules = rules.iter().filter(|r| in_delta(r.node)).count();
        // The rule-inverse pairs below need the reverse of `inverse_class`: which class a
        // summand is the inverse of. One scan per op with an inverse, per round.
        let inv_classes: Vec<(Cfg::O, Vec<(Cfg::G, Cfg::G)>)> = self
            .inverse_op
            .iter()
            .map(|&(op, inv)| (op, self.inverse_classes(inv)))
            .collect();
        for ti in 0..rules.len() {
            // A reducible rule is not a member of the antichain: collapse will retire it,
            // so it must not seed critical pairs.
            if reducible[ti] {
                continue;
            }
            let op = rules[ti].op;
            let m_node = rules[ti].node;

            // Per-rule axiom critical pairs (Kapur §4): superpose the rule with
            // the op's own semantic axiom. The count clamp canonizes counts
            // *within* a monomial but cannot produce these cross-rule consequences — e.g.
            // or(a,b)=c ⟹ or(a,c)=c, and xor(a,b)=c ⟹ xor(a,c)=b — so without these
            // pairs completion is incomplete (Lemmas 4.1(ii), 4.2(ii)/4.5). Generated for
            // antichain members only (like (B) sources), when the rule is in the delta;
            // the full confirmation round is the completeness net, as for (B).
            if in_delta(m_node) {
                match self.op_clamp(op) {
                    CompletionClamp::Idempotent => {
                        // x∘x = x: for each a ∈ M, the pair (N ⊎ {a}, N). Since M → N by
                        // the rule itself, joinability of Kapur's (f(M), f(N∪{a})) reduces
                        // to exactly this pair. a ∈ N clamps to N — trivial, skip early.
                        for &(a, _) in &rules[ti].lhs {
                            let mut r1 = multiset_union(&rules[ti].rhs, &[(a, Cfg::M::ONE)]);
                            crate::multiset::clamp_idempotent(&mut r1);
                            if r1 != rules[ti].rhs {
                                crit.push((op, CpOrigin::AxiomCp, r1, rules[ti].rhs.clone()));
                                if PROOFS {
                                    crit_prem.resize(crit.len(), vec![rule_pair(&rules[ti])]);
                                }
                                #[cfg(debug_assertions)]
                                crit_why.push(cc_mirror::PairWhy::Idem { rule: m_node, a });
                            }
                        }
                    }
                    CompletionClamp::Nilpotent { order } => {
                        // xⁿ = e: for a with multiplicity m in M, superpose M with aⁿ → e
                        // on the lcm M ⊎ {a: n−m}. The rule reduct is N ⊎ {a: n−m}; the
                        // axiom reduct is (M − {a: m}) ⊎ {e}, whose unit drops (stored
                        // monomials never carry the unit). At n=2, m=1 this is literally
                        // Kapur's (f(N ∪ {a}), f((M − {a}) ∪ {e})).
                        for &(a, m) in &rules[ti].lhs {
                            // `order` is a `u8`, so the deficit is below 256 and
                            // representable at every supported multiplicity width.
                            let ord = Cfg::M::try_from_u64(u64::from(order))
                                .expect("a u8 nilpotent order fits every multiplicity width");
                            let k = ord.saturating_sub(m);
                            if k == Cfg::M::ZERO {
                                continue; // m ≡ 0 (mod n) never stored; defensive
                            }
                            let mut r1 = multiset_union(&rules[ti].rhs, &[(a, k)]);
                            crate::multiset::clamp_nilpotent(&mut r1, order);
                            let r2 = crate::multiset::multiset_subtract(&rules[ti].lhs, &[(a, m)]);
                            crit.push((op, CpOrigin::AxiomCp, r1, r2));
                            if PROOFS {
                                crit_prem.resize(crit.len(), vec![rule_pair(&rules[ti])]);
                            }
                            #[cfg(debug_assertions)]
                            crit_why.push(cc_mirror::PairWhy::Nil { rule: m_node, a });
                        }
                    }
                    CompletionClamp::Multiset => {} // plain AC / identity-only: none (Lemma 4.3)
                }
                // The rule's pairs with the group law `{a, inv a} = ∅` (Lean
                // `cp_rule_invGen_left/right`): for `a ∈ M` whose inverse node exists with
                // class `y`, `(N ⊎ {y}, M − {a})`; for `y ∈ M` the class of some `inv(x)`,
                // `(N ⊎ {x}, M − {y})`. Without them `a + c = d` misses `d + neg(a) = c`.
                if let Some(inv) = self.inverse_op(op) {
                    let inverted: &[(Cfg::G, Cfg::G)] = inv_classes
                        .iter()
                        .find(|(o, _)| *o == op)
                        .map_or(&[], |(_, v)| v.as_slice());
                    let order = match self.op_clamp(op) {
                        CompletionClamp::Nilpotent { order } => Some(order),
                        _ => None,
                    };
                    for &(a, _) in &rules[ti].lhs {
                        let inverse_of_a = self.inverse_class(inv, a);
                        let inverted_by_a = inverted
                            .binary_search_by(|p| p.0.cmp(&a))
                            .ok()
                            .map(|i| inverted[i].1);
                        // The first `z` is the class of `inv(a)` when that node exists
                        // (`AxiomPair.invLeft`); the other has `a` as the class of its
                        // inverse node (`AxiomPair.invRight`).
                        #[cfg(debug_assertions)]
                        let mut left = inverse_of_a.is_some();
                        for z in inverse_of_a.into_iter().chain(inverted_by_a) {
                            #[cfg(debug_assertions)]
                            crit_why.push(if std::mem::take(&mut left) {
                                cc_mirror::PairWhy::InvLeft {
                                    rule: m_node,
                                    a,
                                    y: z,
                                }
                            } else {
                                cc_mirror::PairWhy::InvRight {
                                    rule: m_node,
                                    x: z,
                                    y: a,
                                }
                            });
                            let mut r1 = multiset_union(&rules[ti].rhs, &[(z, Cfg::M::ONE)]);
                            if let Some(order) = order {
                                crate::multiset::clamp_nilpotent(&mut r1, order);
                            }
                            let r2 = crate::multiset::multiset_subtract(
                                &rules[ti].lhs,
                                &[(a, Cfg::M::ONE)],
                            );
                            crit.push((op, CpOrigin::AxiomCp, r1, r2));
                            if PROOFS {
                                // The group law's inverse node: `inv(a)` in class `z`, or
                                // `inv(z)` in class `a`.
                                let mut prem = vec![rule_pair(&rules[ti])];
                                for x in [a, z] {
                                    let root = self.classes.find_const(x);
                                    if let Some(n) = self.nodes.plain1.probe(&inv, &[root]) {
                                        prem.push((n, self.classes.find_const(n)));
                                    }
                                }
                                crit_prem.resize(crit.len(), prem);
                            }
                        }
                    }
                }
            }

            // Gather candidate partner nodes from the use-lists of M's distinct children.
            partner_buf.clear();
            for &(x, _) in &rules[ti].lhs {
                if let Some(x_repr) = self.classes.repr_id(self.classes.find_const(x)) {
                    for p in self.classes.iter_uses(x_repr) {
                        partner_buf.push(p);
                    }
                }
            }
            partner_buf.sort_unstable();
            partner_buf.dedup();

            for k in 0..partner_buf.len() {
                let p_node = partner_buf[k];
                // Process each unordered pair once; skip self.
                if p_node <= m_node {
                    continue;
                }
                if self.node_flags(p_node) & inactive != 0 || self.node_op(p_node) != op {
                    continue;
                }
                // The partner must itself be a rule: binary-search the sorted `rules`.
                let Ok(pi) = rules.binary_search_by(|r| r.node.cmp(&p_node)) else {
                    continue;
                };
                // ...and a member of the antichain (a reducible partner will be collapsed).
                if reducible[pi] {
                    continue;
                }
                // Incremental (B): an unordered pair is a *new* critical pair only if at
                // least one of its rules changed since the previous round (S3b). When
                // neither endpoint is in the delta the pair was closed in an earlier round
                // and stays closed; skip it. `full` (round 0) makes `in_delta` always true.
                if !in_delta(m_node) && !in_delta(p_node) {
                    delta_skipped += 1;
                    continue;
                }
                let m = &rules[ti].lhs;
                let a = &rules[pi].lhs;
                // Partners come from the use lists of `m`'s children, which over-approximate
                // the rules sharing a class with `m`: a rule's left-hand side is the node's
                // children read through the clamp (unit drop, nilpotent reduction, inverse
                // cancellation), which can remove a class the stored node still lists as a
                // child. Two disjoint left-hand sides have a trivially joinable critical pair
                // (each reduct rewrites to the other by the other rule), so the pair is skipped
                // rather than assumed absent; containment is handled by the (A′) normalize
                // pass. tests/egg/cc_disjoint_partner.egg (`:identity` with `:nilpotent 3`) reaches a
                // disjoint pair; an earlier `debug_assert` here failed on it in debug builds.
                if multiset_disjoint(a, m) || multiset_subset(a, m) || multiset_subset(m, a) {
                    continue;
                }
                multiset_lcm_into(&mut ab_buf, m, a);
                multiset_subtract_into(&mut sub_buf, &ab_buf, m);
                let mut r1 = multiset_union(&sub_buf, &rules[ti].rhs);
                multiset_subtract_into(&mut sub_buf, &ab_buf, a);
                let mut r2 = multiset_union(&sub_buf, &rules[pi].rhs);
                // Clamp the reducts to the op's normal-form count domain before the pair is
                // closed: idempotent → {0,1} (ACI union), nilpotent → mod-n (symmetric
                // difference). Multiset (plain AC) keeps ℕ counts, no clamp.
                match self.op_clamp(op) {
                    CompletionClamp::Idempotent => {
                        crate::multiset::clamp_idempotent(&mut r1);
                        crate::multiset::clamp_idempotent(&mut r2);
                    }
                    CompletionClamp::Nilpotent { order } => {
                        crate::multiset::clamp_nilpotent(&mut r1, order);
                        crate::multiset::clamp_nilpotent(&mut r2, order);
                    }
                    CompletionClamp::Multiset => {}
                }
                crit.push((op, CpOrigin::Superposition, r1, r2));
                if PROOFS {
                    crit_prem.resize(
                        crit.len(),
                        vec![rule_pair(&rules[ti]), rule_pair(&rules[pi])],
                    );
                }
                #[cfg(debug_assertions)]
                crit_why.push(cc_mirror::PairWhy::Superpose {
                    r1: m_node,
                    r2: p_node,
                });
            }
        }

        // ── Cancelative facet (Kapur §5) ──
        // (C1) Cancel-close every antichain rule of a cancelative op (§5.2): a rule
        // f(M) → f(R) is an equation; canceling the common part C = M ∩ R entails
        // f(M−C) = f(R−C). (C2) Cancelative disjoint superposition (§5.3): for two rules
        // of the same cancelative op, the disjoint join f(M₁⊎M₂) = f(R₁⊎R₂) may not be
        // cancelatively closed; its cancel-closure yields further critical pairs (Kapur's
        // SC2/SC3 examples — without these, orienting the input equations is canonical but
        // NOT a cancelative congruence closure, Thm 5.1/5.2).
        //
        // Empty-side policy after canceling: with a declared identity the empty side IS
        // the unit (f({}) = e) and the pair closes against it. Without one, Kapur's
        // §5.2(iii)(b) applies: an equation f(A) = f(B) whose cancelation empties one side
        // entails f((A−B) ∪ {c}) = f({c}) for EVERY constant c (his SC2 derives
        // f(a,a,b) = a this way). Kapur's constant set C is fixed by purification; ours is
        // incremental, so the closure is generated over the op's CURRENT summand pool (the
        // distinct classes appearing in its active monomials) — a class that appears later
        // is covered by the full confirmation round that sees it, the same net that covers
        // every other delta miss.
        let cancel_close = |a: &[(Cfg::G, Cfg::M)],
                            b: &[(Cfg::G, Cfg::M)]|
         -> Option<(Vec<(Cfg::G, Cfg::M)>, Vec<(Cfg::G, Cfg::M)>)> {
            let c = crate::multiset::multiset_intersect(a, b);
            if c.is_empty() {
                return None;
            }
            Some((
                crate::multiset::multiset_subtract(a, &c),
                crate::multiset::multiset_subtract(b, &c),
            ))
        };
        // The op's summand pool, for the per-constant closure (computed only when an
        // empty-side cancelation actually occurs — rare).
        let summand_pool = |targets: &[(Cfg::O, Vec<(Cfg::G, Cfg::M)>, Cfg::G, Cfg::G)],
                            want: Cfg::O|
         -> Vec<Cfg::G> {
            let mut pool: Vec<Cfg::G> = targets
                .iter()
                .filter(|t| t.0 == want)
                .flat_map(|t| t.1.iter().map(|p| p.0))
                .collect();
            pool.sort_unstable();
            pool.dedup();
            pool
        };
        let push_cancel = |crit: &mut Vec<(
            Cfg::O,
            CpOrigin,
            Vec<(Cfg::G, Cfg::M)>,
            Vec<(Cfg::G, Cfg::M)>,
        )>,
                           op: Cfg::O,
                           has_unit: bool,
                           pool: &[Cfg::G],
                           m: Vec<(Cfg::G, Cfg::M)>,
                           r: Vec<(Cfg::G, Cfg::M)>| {
            if (!m.is_empty() && !r.is_empty()) || has_unit {
                crit.push((op, CpOrigin::Cancellative, m, r));
            } else {
                // §5.2(iii)(b): f(ne ∪ {c}) = f({c}) for every constant c in the pool.
                // Only the right side empties: a left side contained in the right side is
                // below it in degree-lex, so orientation puts it on the right.
                debug_assert!(!m.is_empty(), "cancel-close: the left side emptied");
                let ne = if m.is_empty() { r } else { m };
                for &g in pool {
                    let one = [(g, Cfg::M::ONE)];
                    crit.push((
                        op,
                        CpOrigin::Cancellative,
                        multiset_union(&ne, &one),
                        one.to_vec(),
                    ));
                }
            }
        };
        for ti in 0..rules.len() {
            if reducible[ti] {
                continue;
            }
            let op = rules[ti].op;
            if !self.op_cancellative(op) {
                continue;
            }
            let has_unit = self.unit_node(op).is_some();
            // Lazily computed at most once per rule that needs it; empty-side cases are rare.
            let mut pool: Option<Vec<Cfg::G>> = None;
            let pool_ref = |pool: &mut Option<Vec<Cfg::G>>| -> Vec<Cfg::G> {
                pool.get_or_insert_with(|| summand_pool(&targets, op))
                    .clone()
            };
            // (C1) — regenerated when the rule is in the delta; the full confirmation
            // round is the completeness net, as for (B) and the axiom pairs.
            if in_delta(rules[ti].node)
                && let Some((m, r)) = cancel_close(&rules[ti].lhs, &rules[ti].rhs)
            {
                let needs_pool = (m.is_empty() || r.is_empty()) && !has_unit;
                let pl = if needs_pool {
                    pool_ref(&mut pool)
                } else {
                    Vec::new()
                };
                push_cancel(&mut crit, op, has_unit, &pl, m, r);
                if PROOFS {
                    crit_prem.resize(crit.len(), vec![rule_pair(&rules[ti])]);
                }
                #[cfg(debug_assertions)]
                crit_why.resize(
                    crit.len(),
                    cc_mirror::PairWhy::C1 {
                        rule: rules[ti].node,
                    },
                );
            }
            // (C2) cancelative disjoint superposition — each unordered same-op antichain
            // pair once. O(rules²) but only over the (rare) cancelative ops' rules.
            for pj in ti + 1..rules.len() {
                if reducible[pj] || rules[pj].op != rules[ti].op {
                    continue;
                }
                if !in_delta(rules[ti].node) && !in_delta(rules[pj].node) {
                    continue;
                }
                let u1 = multiset_union(&rules[ti].lhs, &rules[pj].lhs);
                let u2 = multiset_union(&rules[ti].rhs, &rules[pj].rhs);
                if let Some((m, r)) = cancel_close(&u1, &u2) {
                    let needs_pool = (m.is_empty() || r.is_empty()) && !has_unit;
                    let pl = if needs_pool {
                        pool_ref(&mut pool)
                    } else {
                        Vec::new()
                    };
                    push_cancel(&mut crit, op, has_unit, &pl, m, r);
                    if PROOFS {
                        crit_prem.resize(
                            crit.len(),
                            vec![rule_pair(&rules[ti]), rule_pair(&rules[pj])],
                        );
                    }
                    #[cfg(debug_assertions)]
                    crit_why.resize(
                        crit.len(),
                        cc_mirror::PairWhy::C2 {
                            r1: rules[ti].node,
                            r2: rules[pj].node,
                        },
                    );
                }
            }
        }
        #[cfg(debug_assertions)]
        debug_assert_eq!(
            crit.len(),
            crit_why.len(),
            "one mirror tag per critical pair"
        );

        // Critical-pair reducts are normalized to multisets (each step strictly lowers the
        // multiset in degree-lex order against the rule set, so it terminates), then only a
        // genuinely-divergent pair is materialized — this is what stops the runaway
        // (design §6b). See the (B) close loop below.

        if std::env::var_os("AC_COMPLETE_TRACE").is_some() {
            eprintln!(
                "[ac-complete]   active(rules)={} targets(A′)={} crit(B)={}",
                rules.len(),
                targets.len(),
                crit.len()
            );
        }

        let dt_gen = t_gen.elapsed();
        let mut changed = false;
        if overflow.get() {
            self.cc_overflow = true;
            return changed;
        }
        let t_aprime = std::time::Instant::now();
        // (A′) normalize each monomial; materialize+merge its normal form; collapse rules.
        // A node is normalized by all OTHER rules, never by its own node-rule (a rule's
        // LHS is in normal form w.r.t. itself; reducing it by itself would subsume the
        // rule before it can superpose — the §4b regression). So a node is collapsed only
        // when a *different*, strictly-contained rule reduces it (genuine inter-reduction).
        // Borrowed rule views plus reused normalize buffers:
        // the per-target rule set is a `clear`+`extend` refill of `Copy` views into the
        // round's rule table — no deep clones — and the normal form lands in a reused
        // destination buffer. Zero steady-state allocation per target.
        let mut nf_refs: Vec<NfRuleRef<'_, Cfg::G, Cfg::M>> = Vec::with_capacity(rules.len());
        let mut nf_out: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        let mut nf_ping: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        for (op, mset, class, node) in targets {
            // In-round stop: the goal pair joined, or this round's minting
            // blew the node budget — bail mid-apply instead of burning the
            // rest of the round. `rebuild` reads which outcome occurred.
            if self.cc_should_stop() {
                break;
            }
            if work.get() > work_limit {
                self.cc_work_stop = Some(work.get());
                break;
            }
            nf_refs.clear();
            nf_refs.extend(
                rules
                    .iter()
                    .filter(|r| r.op == op && r.node != node)
                    .map(|r| NfRuleRef {
                        lhs: &r.lhs,
                        rhs: &r.rhs,
                    }),
            );
            let target_pairs: Vec<(Cfg::G, Cfg::G)> = if PROOFS {
                rules
                    .iter()
                    .filter(|r| r.op == op && r.node != node)
                    .map(rule_pair)
                    .collect()
            } else {
                Vec::new()
            };
            let applied = std::cell::RefCell::new(Vec::new());
            // Normalize in the op's count domain: idempotent → set (clamp to 1); nilpotent →
            // mod-n; plain AC (MSet) → ℕ.
            // Linear, not indexed: this rule slice is refilled per target (each target is
            // normalized by every rule but its own), so there is no reuse to amortize an
            // index over. Any relative phase cost is workload-dependent and belongs in the
            // Criterion completion benchmark, not in this correctness comment.
            let nf = NfRules::linear(&nf_refs).with_work(&work);
            let nf = if PROOFS {
                nf.with_applied(&applied)
            } else {
                nf
            };
            let normalized = match self.op_clamp(op) {
                CompletionClamp::Idempotent => {
                    try_normalize_set_into(&mut nf_out, &mut nf_ping, &mset, nf)
                }
                CompletionClamp::Nilpotent { order } => {
                    try_normalize_nilpotent_into(&mut nf_out, &mut nf_ping, &mset, nf, order)
                }
                CompletionClamp::Multiset => {
                    try_normalize_ms_into(&mut nf_out, &mut nf_ping, &mset, nf)
                }
            };
            if normalized.is_err() {
                overflow.set(true);
                break;
            }
            // Inverse-pair cancellation on the normal form (group ops): normalization can
            // bring x and inv(x) together in one monomial; cancel before comparing. Track
            // whether it fired: a merge produced by pair cancellation is a group-law
            // inference (`x ∘ inv(x) = e`), not plain rule inter-reduction, and the proof
            // label must say so.
            let mut inverse_cancelled = false;
            let mut inverse_prem = Vec::new();
            if let Some(inv) = self.inverse_op(op) {
                if PROOFS {
                    self.inverse_premises(inv, &nf_out, &mut inverse_prem);
                }
                inverse_cancelled = self.group_cancel_pairs(inv, &mut nf_out);
            }
            let normal = &nf_out;
            // If normalization by the other rules changed the monomial, materialize the normal
            // form and merge. `materialize` calls `add`, which now resolves a degenerate result
            // itself: an emptied monomial (`a ⊕ a → {}`, or `+(a,e)`-style cancellation) becomes
            // the unit, and a single mult-1 summand (`a ⊕ a ⊕ b → {b}`) becomes that class — so
            // this one branch covers the empty/size-1 cases too (a completion target always has
            // `mset.len() ≥ 2`, canonization never stores a degenerate node, so any empty/size-1
            // `normal` differs from `mset` and lands here).
            if *normal != mset {
                let Some(c_prime) = materialize(self, op, normal, &mut mat_buf) else {
                    overflow.set(true);
                    break;
                };
                let just = if inverse_cancelled {
                    Justification::InverseCancel {
                        node_a: c_prime,
                        node_b: node,
                    }
                } else {
                    Justification::ACInterReduction {
                        node_a: c_prime,
                        node_b: node,
                    }
                };
                #[cfg(debug_assertions)]
                self.cc_mirror_tag(cc_mirror::MergeWhy::NormalForm {
                    op,
                    node,
                    reduct: cc_mirror::mono(normal),
                });
                if PROOFS {
                    // The node is its class's member; the rules the normal form used; the
                    // inverse pairs that cancelled.
                    let mut prem = vec![(node, class)];
                    prem.extend(applied.borrow().iter().map(|&k| target_pairs[k as usize]));
                    prem.extend(inverse_prem);
                    self.pending_premises = Some(prem);
                }
                do_merge(self, c_prime, class, just);
                self.pending_premises = None;
                #[cfg(debug_assertions)]
                self.cc_mirror_untag();
                // Collapse: the node was reducible by another rule (proper containment),
                // so retire it from the active AC rule set (design §6b). FLAG_AC_COLLAPSED,
                // NOT subsume — the node stays matchable and a legal child; only
                // completion's active set excludes it. Merge first, mark second. The
                // collapse is a change even when the merge was not: it removes a rule, so
                // the round ran over a rule set it then changed and is no fixpoint round.
                self.set_cc_collapsed(node);
                changed = true;
            }
        }
        let dt_aprime = t_aprime.elapsed();
        if overflow.get() {
            self.cc_overflow = true;
            return changed;
        }
        let t_bclose = std::time::Instant::now();
        // (B) close each critical pair by merging the normal forms of its two reducts.
        // Normalize BOTH reducts to multisets first; if they coincide the pair is already
        // joinable (a trivial critical pair) — skip it, minting no node and no merge.
        // Materializing trivial pairs was a second blowup source: each spurious node became
        // a fresh rule that fed the next round. Only genuinely divergent pairs
        // are materialized and merged.
        let mut trivial = 0usize;
        let mut nontrivial = 0usize;
        let mut trivial_after_nf = 0usize; // trivial pairs that needed full normalize to see it
        // The rule set used to normalize a reduct is the same for every pair of a given op, so
        // build the per-op rule sets ONCE (outside the loop), not per pair — the `Bclose` hoist
        // (perf doc §2). A reduct of op X must normalize ONLY against op-X rules: a different
        // op's LHS is a set of class ids that could spuriously match inside X's monomial. So
        // group `nf_rules` by op. Keyed by the typed op id (not a widened copy of one);
        // lookup is a small linear scan (few ops).
        let mut nf_by_op: Vec<(Cfg::O, Vec<NfRuleRef<'_, Cfg::G, Cfg::M>>)> = Vec::new();
        for r in &rules {
            let entry = match nf_by_op.iter_mut().find(|(o, _)| *o == r.op) {
                Some(e) => &mut e.1,
                None => {
                    nf_by_op.push((r.op, Vec::new()));
                    &mut nf_by_op.last_mut().unwrap().1
                }
            };
            entry.push(NfRuleRef {
                lhs: &r.lhs,
                rhs: &r.rhs,
            });
        }
        // The rules' premise pairs, in the order of `nf_by_op`'s tables.
        let nf_pairs_by_op: Vec<Vec<(Cfg::G, Cfg::G)>> = nf_by_op
            .iter()
            .map(|(o, _)| rules.iter().filter(|r| r.op == *o).map(rule_pair).collect())
            .collect();
        // Index each op's table by LHS-minimum class, hoisted with the table itself. This
        // The index is amortized over all reduct normalizations for the op. Its performance
        // effect is tracked by the Criterion completion benchmark.
        let nf_index_by_op: Vec<NfIndex<Cfg::G>> =
            nf_by_op.iter().map(|(_, v)| NfIndex::build(v)).collect();
        let empty_nf: Vec<NfRuleRef<'_, Cfg::G, Cfg::M>> = Vec::new();
        let crit_generated = crit.len();
        let mut n1_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        let mut n2_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        #[cfg(debug_assertions)]
        let mut crit_why = crit_why.into_iter();
        for (ci, (op, origin, r1, r2)) in crit.into_iter().enumerate() {
            #[cfg(debug_assertions)]
            let why = crit_why.next().expect("one mirror tag per critical pair");
            // Same in-round stops as the (A′) loop above.
            if self.cc_should_stop() {
                break;
            }
            if work.get() > work_limit {
                self.cc_work_stop = Some(work.get());
                break;
            }
            // Cheap raw-equality reject: most critical pairs are trivial (the two reducts
            // already coincide as multisets), so skip the two full normalizations entirely
            // when r1 == r2 already.
            if r1 == r2 {
                trivial += 1;
                continue;
            }
            let table = nf_by_op.iter().position(|(o, _)| *o == op);
            let applied = std::cell::RefCell::new(Vec::new());
            let nf_rules = match table {
                Some(i) => NfRules::indexed(&nf_by_op[i].1, &nf_index_by_op[i]),
                None => NfRules::linear(&empty_nf),
            }
            .with_work(&work);
            let nf_rules = if PROOFS {
                nf_rules.with_applied(&applied)
            } else {
                nf_rules
            };
            // Normalize both reducts in the op's count domain (idempotent → set, nilpotent →
            // mod-n, plain AC → ℕ) before comparing/merging.
            let normalized = match self.op_clamp(op) {
                CompletionClamp::Idempotent => {
                    try_normalize_set_into(&mut n1_buf, &mut nf_ping, &r1, nf_rules).and_then(
                        |()| try_normalize_set_into(&mut n2_buf, &mut nf_ping, &r2, nf_rules),
                    )
                }
                CompletionClamp::Nilpotent { order } => {
                    try_normalize_nilpotent_into(&mut n1_buf, &mut nf_ping, &r1, nf_rules, order)
                        .and_then(|()| {
                            try_normalize_nilpotent_into(
                                &mut n2_buf,
                                &mut nf_ping,
                                &r2,
                                nf_rules,
                                order,
                            )
                        })
                }
                CompletionClamp::Multiset => {
                    try_normalize_ms_into(&mut n1_buf, &mut nf_ping, &r1, nf_rules).and_then(|()| {
                        try_normalize_ms_into(&mut n2_buf, &mut nf_ping, &r2, nf_rules)
                    })
                }
            };
            if normalized.is_err() {
                overflow.set(true);
                break;
            }
            let mut inverse_prem = Vec::new();
            if let Some(inv) = self.inverse_op(op) {
                if PROOFS {
                    self.inverse_premises(inv, &n1_buf, &mut inverse_prem);
                    self.inverse_premises(inv, &n2_buf, &mut inverse_prem);
                }
                self.group_cancel_pairs(inv, &mut n1_buf);
                self.group_cancel_pairs(inv, &mut n2_buf);
            }
            let (n1, n2) = (&n1_buf, &n2_buf);
            if n1 == n2 {
                trivial += 1;
                trivial_after_nf += 1;
                continue;
            }
            nontrivial += 1;
            // `materialize` calls `add`, which resolves a degenerate reduct itself: an emptied
            // reduct (nilpotent cancellation / identity drop) becomes the unit, a single mult-1
            // summand becomes that class. So no empty/size-1 special-casing is needed here.
            let (Some(c1), Some(c2)) = (
                materialize(self, op, n1, &mut mat_buf),
                materialize(self, op, n2, &mut mat_buf),
            ) else {
                overflow.set(true);
                break;
            };
            // The proof label reflects the pair's ORIGIN: pairwise rule superposition
            // (Kapur Def 3.2), the op's own semantic-axiom CP (§4), or cancelative
            // closure (§5.2/§5.3).
            let just = match origin {
                CpOrigin::Superposition => Justification::ACSuperposition {
                    node_a: c1,
                    node_b: c2,
                },
                CpOrigin::AxiomCp => Justification::ACAxiomCP {
                    node_a: c1,
                    node_b: c2,
                },
                CpOrigin::Cancellative => Justification::Cancellative {
                    node_a: c1,
                    node_b: c2,
                },
            };
            #[cfg(debug_assertions)]
            self.cc_mirror_tag(cc_mirror::MergeWhy::Pair {
                op,
                origin: why,
                pair: (cc_mirror::mono(&r1), cc_mirror::mono(&r2)),
                reducts: (cc_mirror::mono(n1), cc_mirror::mono(n2)),
            });
            if PROOFS {
                let mut prem = crit_prem.get(ci).cloned().unwrap_or_default();
                if let Some(t) = table {
                    prem.extend(
                        applied
                            .borrow()
                            .iter()
                            .map(|&k| nf_pairs_by_op[t][k as usize]),
                    );
                }
                prem.extend(inverse_prem);
                self.pending_premises = Some(prem);
            }
            changed |= do_merge(self, c1, c2, just);
            self.pending_premises = None;
            #[cfg(debug_assertions)]
            self.cc_mirror_untag();
        }
        if std::env::var_os("AC_COMPLETE_TRACE").is_some() {
            eprintln!(
                "[ac-complete]   crit(B) trivial={trivial} (raw-eq={}, after-nf={trivial_after_nf}) nontrivial={nontrivial}",
                trivial - trivial_after_nf
            );
            eprintln!(
                "[ac-complete]   full={full} rules={} delta_in_rules={delta_in_rules} delta_skipped_pairs={delta_skipped} crit_generated={crit_generated}",
                rules.len(),
            );
        }
        if std::env::var_os("AC_COMPLETE_TRACE").is_some() {
            eprintln!("[ac-complete]   work={} (budget {work_limit})", work.get());
        }
        if phase_time {
            let dt_bclose = t_bclose.elapsed();
            eprintln!(
                "[ac-phase] rules={} reducible={:.1}ms gen+targets={:.1}ms A'={:.1}ms Bclose={:.1}ms",
                rules.len(),
                dt_reducible.as_secs_f64() * 1e3,
                dt_gen.as_secs_f64() * 1e3,
                dt_aprime.as_secs_f64() * 1e3,
                dt_bclose.as_secs_f64() * 1e3,
            );
        }
        if overflow.get() {
            self.cc_overflow = true;
        }
        changed || reactivated.get()
    }

    /// Always sequential: a mark is a per-member frame push, and the fan-out
    /// loses at every measured size (0.03x at 12k nodes, 0.30x at 200k, 0.68x
    /// at 1.6M; `par_fanout_bench`). The parallel twin stays reachable through
    /// [`Self::mark_with`] for re-measurement.
    pub fn mark(&mut self, shrink: ShrinkPolicy) -> EGraphToken {
        if *PROF_ON {
            let t = std::time::Instant::now();
            let tok = self.mark_with(shrink, false);
            prof_record(&MARK_NS, &MARK_CALLS, t);
            return tok;
        }
        self.mark_with(shrink, false)
    }

    pub fn restore(&mut self, token: EGraphToken) {
        let par = self.fanout_enabled();
        if *PROF_ON {
            let t = std::time::Instant::now();
            self.restore_with(token, par);
            prof_record(&RESTORE_NS, &RESTORE_CALLS, t);
            return;
        }
        self.restore_with(token, par);
    }

    /// `restore(t)` then `pop_scope()`, fused: the SMT-LIB `pop` to the level
    /// below `t`, at the legacy restore's cost (one pop core per column).
    pub fn restore_and_pop(&mut self, token: EGraphToken) {
        let par = self.fanout_enabled();
        if *PROF_ON {
            let t = std::time::Instant::now();
            self.restore_and_pop_with(token, par);
            prof_record(&RESTORE_NS, &RESTORE_CALLS, t);
            return;
        }
        self.restore_and_pop_with(token, par);
    }

    /// Heap bytes of the ONE shared genealogy (H4b.3 measurement): the
    /// counterfactual per-member duplication is this times the number of
    /// semi-persistent columns the members hold (each carried its own
    /// `GenStamps` before H2).
    pub fn fork_history_bytes(&self) -> usize {
        self.history.heap_bytes()
    }

    /// Whether restore fans the member composites out over a `rayon` scope.
    /// `SEMPER_PAR=on` forces the fan-out, `SEMPER_PAR=off` forces sequential;
    /// otherwise the fan-out runs only at or above [`PAR_NODE_MIN`] live nodes,
    /// because on a small graph the dispatch costs more than the members' work
    /// (0.73x at 12k nodes vs 1.62x at 200k; `par_fanout_bench`).
    fn fanout_enabled(&self) -> bool {
        match std::env::var_os("SEMPER_PAR") {
            Some(v) if v == "on" => true,
            Some(v) if v == "off" => false,
            _ => self.node_count() >= PAR_NODE_MIN,
        }
    }

    /// Mark every member composite, sequentially or fanned out over a
    /// `rayon::scope` on disjoint `&mut` field borrows. Each member owns its
    /// stores, logs, and frames, so the fan-out closures touch no shared
    /// state; the rebuild and the tiny map marks run strictly outside it.
    pub fn mark_with(&mut self, shrink: ShrinkPolicy, par: bool) -> EGraphToken {
        self.rebuild();
        assert!(
            self.history.depth() < u32::MAX,
            "mark: frame depth is bounded by the saturation driver"
        );
        let mut members = crate::group_members::EGraphMembers::<Cfg, L, TRACK, PROOFS> {
            sorts: &mut self.sorts,
            ops: &mut self.ops,
            rules: &mut self.rules,
            axioms: &mut self.axioms,
            lits: &mut self.lits,
            classes: &mut self.classes,
            nodes: &mut self.nodes,
            unit_node: &mut self.unit_node,
            inverse_op: &mut self.inverse_op,
            par,
        };
        let group = self
            .history
            .mark_member(&mut members, shrink)
            .expect("mark: every member has headroom and the members are in step");
        let rule_len = ProofLens {
            rule_starts: self.rule_starts.len(),
            rule_premises: self.rule_premises.len(),
            creation_log: self.creation_log.len(),
            build_starts: self.build_starts.len(),
            build_premises: self.build_premises.len(),
            merge_premise_pairs: self.merge_premise_pairs.len(),
            merge_premise_log: self.merge_premise_log.len(),
        };
        self.rule_marks
            .truncate((self.history.depth() as usize).saturating_sub(1));
        self.rule_marks.push(rule_len);
        EGraphToken {
            group,
            completion_outcome: self.completion_outcome,
            rule_len,
        }
    }

    /// Restore every member composite, sequentially or fanned out over a
    /// `rayon::scope` on disjoint `&mut` field borrows (same soundness
    /// argument as [`Self::mark_with`]). The shared bookkeeping (outcome,
    /// worklists, repair watermark) runs strictly after the fan-out joins.
    pub fn restore_with(&mut self, token: EGraphToken, par: bool) {
        // The ONE validity check for the whole member set: the group's
        // `History` validates the token and records the cut once; the members
        // reset structurally to the token's depth (semantics B: the
        // checkpoint's frame stays open).
        let t = std::time::Instant::now();
        let mut members = crate::group_members::EGraphMembers::<Cfg, L, TRACK, PROOFS> {
            sorts: &mut self.sorts,
            ops: &mut self.ops,
            rules: &mut self.rules,
            axioms: &mut self.axioms,
            lits: &mut self.lits,
            classes: &mut self.classes,
            nodes: &mut self.nodes,
            unit_node: &mut self.unit_node,
            inverse_op: &mut self.inverse_op,
            par,
        };
        let ok = self.history.restore_member(&mut members, token.group);
        assert!(
            ok,
            "restore: token minted by this container's own mark, and not already spent"
        );
        if *RESTORE_PROF_ON {
            restore_prof_record(0, t);
        }
        // Roll the outcome back with the graph: the mark-time value describes exactly the
        // restored state (mark() rebuilds first), so a post-restore reader never sees an
        // outcome computed for the discarded scope.
        self.completion_outcome = token.completion_outcome;
        self.truncate_rule_instances(token.rule_len);
        self.rule_marks.truncate(self.history.depth() as usize);
        self.worklist.clear();
        self.key_lowered.clear();
        self.collisions.clear();
        self.normalizations.clear();
        self.touched.clear();
        // Merges captured before this restore belong to the discarded scope.
        // The drain-before-advance discipline keeps this empty in practice;
        // clearing makes restore-safety hold unconditionally.
        self.merged_log.clear();
        // The repair watermark is a pair of counters over the *pre-restore* graph, and
        // restore moves both (touched cleared, classes regrown). Drop it so the next
        // `rebuild` rescans rather than trusting a comparison against a discarded state.
        self.repair_state = None;
    }

    /// `restore_with` then `pop_scope`, fused (design doc 08 §1): every member
    /// runs its own fused pop-restore (one pop core per column), the checkpoint's
    /// member tokens leave the stacks, and `history` cuts at the token's depth.
    pub fn restore_and_pop_with(&mut self, token: EGraphToken, par: bool) {
        // `restore_with` then `pop_scope`, fused: the SMT-LIB pop to the level
        // below `t`, on one pop core per column.
        let t = std::time::Instant::now();
        let mut members = crate::group_members::EGraphMembers::<Cfg, L, TRACK, PROOFS> {
            sorts: &mut self.sorts,
            ops: &mut self.ops,
            rules: &mut self.rules,
            axioms: &mut self.axioms,
            lits: &mut self.lits,
            classes: &mut self.classes,
            nodes: &mut self.nodes,
            unit_node: &mut self.unit_node,
            inverse_op: &mut self.inverse_op,
            par,
        };
        let ok = self
            .history
            .restore_and_pop_member(&mut members, token.group);
        assert!(
            ok,
            "restore_and_pop: token minted by this container's own mark, and not already spent"
        );
        if *RESTORE_PROF_ON {
            restore_prof_record(0, t);
        }
        self.completion_outcome = token.completion_outcome;
        self.truncate_rule_instances(token.rule_len);
        self.rule_marks.truncate(self.history.depth() as usize);
        self.worklist.clear();
        self.key_lowered.clear();
        self.collisions.clear();
        self.normalizations.clear();
        self.touched.clear();
        self.repair_state = None;
    }

    /// Drop the open top scope (the SMT-LIB `pop`): every member undoes and
    /// drops its top frame and the scope's token dies. Panics on an empty
    /// scope stack (the interpreter refuses a pop without push before this).
    pub fn pop_scope(&mut self) {
        assert!(self.history.depth() >= 1, "pop_scope: no open scope");
        let par = self.fanout_enabled();
        let mut members = crate::group_members::EGraphMembers::<Cfg, L, TRACK, PROOFS> {
            sorts: &mut self.sorts,
            ops: &mut self.ops,
            rules: &mut self.rules,
            axioms: &mut self.axioms,
            lits: &mut self.lits,
            classes: &mut self.classes,
            nodes: &mut self.nodes,
            unit_node: &mut self.unit_node,
            inverse_op: &mut self.inverse_op,
            par,
        };
        let ok = self.history.pop_member(&mut members);
        assert!(ok, "pop_scope: the members are in step with the history");
        if let Some(len) = self.rule_marks.pop() {
            self.truncate_rule_instances(len);
        }
        self.worklist.clear();
        self.key_lowered.clear();
        self.collisions.clear();
        self.normalizations.clear();
        self.touched.clear();
        self.repair_state = None;
    }

    /// Proof-mode `add` for plain and commutative operators: keep the evidence
    /// that relates the client's term to the node it is stored as, so that
    /// `explain_deep` alone gives complete explanations about client terms.
    ///
    /// Without it, `add` stores each child's class root and records nothing,
    /// and a later congruence step through the node takes its premises from
    /// those roots: the equality between the child the client gave and that
    /// root is used but never cited (measured in sundance: up to 513 of 1278
    /// conflict explanations on a Verus file failed a congruence-closure check
    /// of the antecedent set, 64 of them not valid even with every level-0
    /// fact assumed). Three cases:
    ///
    /// 1. A given child is not its class root: insert the node with the given
    ///    children (fresh, since stored nodes have root children), then
    ///    recanonicalize it at once. Recanonicalization writes the given
    ///    children to history (the congruence premises `explain_deep` reads)
    ///    and reports a hash-cons collision with an existing congruent node,
    ///    merged here with a `Congruence` justification, as `rebuild` does.
    /// 2. The children are roots and hit a node that has history: that node's
    ///    original children differ from the client's, so the client's term
    ///    gets its own flagged duplicate, merged with a `Congruence`
    ///    justification whose expansion explains the child differences.
    /// 3. A hit on a node without history is the same term.
    ///
    /// Re-adding the same client term returns the node built for it the
    /// first time (`creation_memo`): the hash-cons table cannot find it,
    /// because its stored children are recanonicalized while its history
    /// keeps the given ones.
    fn add_with_creation_evidence(
        &mut self,
        op: Cfg::O,
        given: &[Cfg::G],
        node_flags: u8,
    ) -> Cfg::G {
        let key: Vec<(Cfg::G, usize)> = given.iter().map(|&g| (g, 1)).collect();
        if let Some(&id) = self.creation_memo.get(&(op, key)) {
            return id;
        }
        let canonical: Vec<Cfg::G> = self.g_buf.clone();
        let all_roots = given.iter().zip(canonical.iter()).all(|(g, c)| g == c);
        if !all_roots {
            let result = self.nodes.add(op, given, &self.ops, node_flags);
            // The given children can equal a node's stored children that a later merge left
            // stale, while its history holds different original children: returning that
            // node would make the client's term stand for the original one, and explanations
            // would cite the original children's equalities instead of the given ones. Keep
            // the client's term as its own node, as in case 2.
            if let Added::Existing(n) = result
                && self.node_has_history(n)
            {
                return self.add_creation_dup(op, given, &canonical, n, node_flags);
            }
            let id = self.register_if_fresh(result, op);
            if result.is_fresh() {
                for &child in &canonical {
                    if let Some(repr) = self.classes.repr_id(child) {
                        if !self.classes.atomic(repr)
                            && (0..self.classes.min_width().saturating_sub(1))
                                .any(|col| self.classes.min_monomial(repr, col).is_some())
                        {
                            // A class holding a completion monomial turns `atomic`: from now on
                            // a build keeps it nested (see the `spelling_epoch` field).
                            self.spelling_epoch += 1;
                        }
                        self.classes.add_use(repr, id);
                    }
                }
                self.collisions.clear();
                self.normalizations.clear();
                self.recanonize_parent(id);
                self.merge_creation_collisions();
                let key: Vec<(Cfg::G, usize)> = given.iter().map(|&g| (g, 1)).collect();
                self.remember_creation(op, &key, id);
            }
            return id;
        }
        let result = self.nodes.add(op, &canonical, &self.ops, node_flags);
        match result {
            Added::Existing(n) if self.node_has_history(n) => {
                self.add_creation_dup(op, given, &canonical, n, node_flags)
            }
            _ => {
                let id = self.register_if_fresh(result, op);
                if result.is_fresh() {
                    for &child in &canonical {
                        if let Some(repr) = self.classes.repr_id(child) {
                            if !self.classes.atomic(repr)
                                && (0..self.classes.min_width().saturating_sub(1))
                                    .any(|col| self.classes.min_monomial(repr, col).is_some())
                            {
                                // A class holding a completion monomial turns `atomic`: from now on
                                // a build keeps it nested (see the `spelling_epoch` field).
                                self.spelling_epoch += 1;
                            }
                            self.classes.add_use(repr, id);
                        }
                    }
                }
                id
            }
        }
    }

    /// A flagged duplicate of the existing node `n` holding the client's
    /// `given` children, merged with `n` by a congruence step whose premises
    /// are the differences between `given` and `n`'s original children.
    fn add_creation_dup(
        &mut self,
        op: Cfg::O,
        given: &[Cfg::G],
        canonical: &[Cfg::G],
        n: Cfg::G,
        node_flags: u8,
    ) -> Cfg::G {
        let dup = self
            .nodes
            .add_congruent_dup(op, given, &self.ops, node_flags);
        let id = self.register_if_fresh(Added::Fresh(dup), op);
        for &child in canonical {
            if let Some(repr) = self.classes.repr_id(child) {
                if !self.classes.atomic(repr)
                    && (0..self.classes.min_width().saturating_sub(1))
                        .any(|col| self.classes.min_monomial(repr, col).is_some())
                {
                    // A class holding a completion monomial turns `atomic`: from now on
                    // a build keeps it nested (see the `spelling_epoch` field).
                    self.spelling_epoch += 1;
                }
                self.classes.add_use(repr, id);
            }
        }
        self.collisions.clear();
        self.normalizations.clear();
        self.collisions.push((id, n));
        self.merge_creation_collisions();
        let key: Vec<(Cfg::G, usize)> = given.iter().map(|&g| (g, 1)).collect();
        self.remember_creation(op, &key, id);
        id
    }

    /// Merge the collisions `add_with_creation_evidence` recorded, each with a
    /// `Congruence` justification, as `rebuild_congruence` merges its own.
    fn merge_creation_collisions(&mut self) {
        let pairs = std::mem::take(&mut self.collisions);
        let normals = std::mem::take(&mut self.normalizations);
        let tagged = pairs
            .iter()
            .map(|&(a, b)| (a, b, false))
            .chain(normals.iter().map(|&(a, b)| (a, b, true)));
        for (a, b, normalize) in tagged.collect::<Vec<_>>() {
            let just = if normalize {
                Justification::Normalize { node: a, normal: b }
            } else {
                Justification::Congruence {
                    node_a: a,
                    node_b: b,
                }
            };
            let m = self.merge_in_classes(a, b, Some(just));
            if let Some(m) = m {
                self.fold_min_monomial(
                    m.survivor,
                    m.absorbed,
                    m.absorbed_min_row,
                    m.absorbed_atomic,
                );
                self.worklist.push((m.absorbed_uses, m.survivor));
            }
        }
        self.collisions = pairs;
        self.collisions.clear();
        self.normalizations = normals;
        self.normalizations.clear();
        // A creation merge can change a class root, leaving congruent parents
        // stored under the old root until the next rebuild; a term registered
        // right after would then miss its congruent twin (measured:
        // `conformance::differential_basic_against_semper`, seed 579). Close
        // congruence now, so `add` returns with the graph congruence-closed,
        // as a client registering terms expects.
        //
        // Not while a saturation round is open: the round matches every rule against
        // an index built at its start, and recanonicalizing the nodes it holds would
        // change what later rules of the round match. Plain mode never rebuilds
        // mid-round; the worklist waits for the round's rebuild here too.
        if !self.worklist.is_empty() && !self.round_open {
            self.rebuild_congruence();
        }
    }

    /// Open or close a saturation round (see `round_open`).
    pub(crate) fn set_round_open(&mut self, open: bool) {
        self.round_open = open;
    }

    /// Test support: [`node_has_history`](Self::node_has_history).
    #[doc(hidden)]
    pub fn node_has_history_pub(&self, id: Cfg::G) -> bool {
        self.node_has_history(id)
    }

    /// Whether `id`'s node has saved its original children (the history bit).
    fn node_has_history(&self, id: Cfg::G) -> bool {
        match self.node_ref(id) {
            NodeRef::Plain0(_) | NodeRef::Lit(_) => false,
            NodeRef::Plain1(l) => self.nodes.plain1.get(l).has_history(),
            NodeRef::Plain2(l) => self.nodes.plain2.get(l).has_history(),
            NodeRef::Plain3(l) => self.nodes.plain3.get(l).has_history(),
            NodeRef::SPair(l) => self.nodes.spair.get(l).has_history(),
            NodeRef::PlainN(l) => self.nodes.plain_n.get(l).has_history(),
            NodeRef::Seq(l) => self.nodes.seq.get(l).has_history(),
            NodeRef::MSet(l) => self.nodes.mset.get(l).has_history(),
            NodeRef::Set(l) => self.nodes.set.get(l).has_history(),
        }
    }

    fn register_if_fresh(&mut self, result: Added<Cfg::G>, op: Cfg::O) -> Cfg::G {
        if result.is_fresh() {
            let id = result.id();
            let repr = self.classes.add_singleton(id);
            // Seed the per-class min-monomial pool. A completion node (MSet or Set) is its
            // class's only monomial for its own op, so seed that op's column to itself. A
            // non-completion node instead makes its class `atomic`: the class has a member
            // that is not a monomial, so the size-1 monomial `{class}` is its normal-form
            // representative (the completion rule RHS, §9a). Completion nodes are not atomic
            // by themselves; they become atomic only when referenced as a child (`add_use`).
            match self.ops.completion_column(op) {
                Some(col) => {
                    // Fix the pool row width to nb_completion on first completion-node seed.
                    // Ops are declared before terms (declare-before-build), so the count is
                    // stable here; `set_min_width` is idempotent when unchanged and rejects a
                    // change once rows exist.
                    // One column per completion op, plus the completion order key
                    // (`order_key`) in the last one.
                    self.classes
                        .set_min_width(self.ops.completion_op_count() + 1);
                    self.classes.set_min_monomial(repr, col, id);
                }
                None => self.classes.set_atomic(repr),
            }
            self.touched.push(id);
        }
        result.id()
    }

    /// Semi-naive: node ids created or recanonicalized since the last
    /// `clear_touched` (or `restore`). May contain duplicates; the delta
    /// index builder deduplicates. Superset of all genuinely-changed nodes.
    pub fn touched(&self) -> &[Cfg::G] {
        &self.touched
    }

    /// Clear the touched log (call at a semi-naive round boundary, after the
    /// delta index for the round has been built).
    pub fn clear_touched(&mut self) {
        self.touched.clear();
    }

    // -----------------------------------------------------------------------
    // Read-only inspection
    // -----------------------------------------------------------------------

    pub fn node_count(&self) -> usize {
        self.nodes.routing().len()
    }

    /// The graph's size as `(node count, live class count)`, both O(1). Within one
    /// saturation round's action phase nodes are only created and classes only merged, so
    /// the stamp differs before and after iff a node was created or two classes merged:
    /// creation moves the node count, and a merge without creation moves the class count.
    /// The saturation loops compare it around the action phase to decide the fixpoint,
    /// rather than trusting each action's own count (a `union` whose sides were already
    /// equal can still have built the nodes it names).
    pub fn size_stamp(&self) -> (usize, usize) {
        (
            self.node_count(),
            crate::containers::IndexLike::as_usize(self.classes.num_classes()),
        )
    }

    pub fn class_repr(&self, id: Cfg::G) -> Cfg::G {
        self.classes.find_const(id)
    }

    /// Whether the class whose root is `root` participates in e-matching. Takes
    /// an already-resolved class root (from [`class_repr`](Self::class_repr)) so
    /// the matcher's index build avoids a second `find_const` per node. Defaults
    /// to `true` (matchable) when `root` names no live class. See
    /// [`set_class_matchable`](Self::set_class_matchable).
    pub(crate) fn is_repr_matchable(&self, root: Cfg::G) -> bool {
        match self.classes.repr_id(root) {
            Some(key) => self.classes.matchable(key),
            None => true,
        }
    }

    /// The minimum-monomial node stored for `id`'s class in `id`'s op column (the completion
    /// rule RHS, §9a). Maintained on merge by `fold_min_monomial`. Returns `None` if `id` has
    /// no class or its op has no stored monomial for that class. Read by tests only.
    #[allow(dead_code)]
    pub(crate) fn class_min_monomial(&self, id: Cfg::G) -> Option<Cfg::G> {
        let repr = self.classes.repr_id(self.classes.find_const(id))?;
        let col = self.completion_column(id)?;
        self.classes.min_monomial(repr, col)
    }

    /// The minimum-monomial node stored for the class of `cls` in `op`'s completion column,
    /// for any `cls` (a representative or a member of any kind). `None` if `op` has no
    /// completion column or the column holds no node for that class. Read by diagnostics.
    #[allow(dead_code)]
    pub(crate) fn class_min_monomial_of_op(&self, cls: Cfg::G, op: Cfg::O) -> Option<Cfg::G> {
        let repr = self.classes.repr_id(self.classes.find_const(cls))?;
        let col = self.ops.completion_column(op)?;
        self.classes.min_monomial(repr, col)
    }

    /// Whether `id`'s class is `atomic` (referenced as a child / has a non-AC node, so
    /// `{class}` is its canonical summand form, §9a). `None` if `id` has no class.
    #[allow(dead_code)]
    pub(crate) fn class_atomic(&self, id: Cfg::G) -> Option<bool> {
        let repr = self.classes.repr_id(self.classes.find_const(id))?;
        Some(self.classes.atomic(repr))
    }

    pub fn node_ref(&self, id: Cfg::G) -> NodeRef<Cfg::Ids> {
        self.nodes.routing().get(id)
    }

    pub fn node_op(&self, id: Cfg::G) -> Cfg::O {
        match self.node_ref(id) {
            NodeRef::Plain0(l) => self.nodes.plain0.get(l).op(),
            NodeRef::Plain1(l) => self.nodes.plain1.get(l).op(),
            NodeRef::Plain2(l) => self.nodes.plain2.get(l).op(),
            NodeRef::Plain3(l) => self.nodes.plain3.get(l).op(),
            NodeRef::SPair(l) => self.nodes.spair.get(l).op(),
            NodeRef::PlainN(l) => self.nodes.plain_n.get(l).op(),
            NodeRef::Seq(l) => self.nodes.seq.get(l).op(),
            NodeRef::MSet(l) => self.nodes.mset.get(l).op(),
            NodeRef::Set(l) => self.nodes.set.get(l).op(),
            NodeRef::Lit(l) => self.nodes.lit.get(l).op(),
        }
    }

    pub fn node_op_name(&self, id: Cfg::G) -> &str {
        &self.ops.info(self.node_op(id)).name
    }

    /// Global ids of every AC e-node, ascending (the AC partition is append-only, so local
    /// id order is global-id order). The completion round iterates this instead of all
    /// `node_count()` nodes: it visits only AC nodes, never the non-AC majority (leaves,
    /// `Plain`/`Lit`/other-op nodes). On AC-dense stress graphs this is ~neutral, but on a
    /// general e-graph (mostly non-AC structure) the AC nodes are a small fraction, so the
    /// per-round scan drops from O(total nodes) to O(AC nodes). Includes collapsed/subsumed
    /// AC nodes; the caller filters by flag.
    fn completion_node_ids(&self) -> impl Iterator<Item = Cfg::G> + '_ {
        use crate::containers::DenseId;
        use crate::typed_routing::NodeIds;
        // Both completion partitions: MSet (plain AC or nilpotent) and Set (idempotent/ACI).
        //
        // The bare `from_usize` mints below need no bound check, unlike the global-id scans
        // (see [`node_ids`](Self::node_ids)): these arenas are indexed *by* the local id, so
        // the container's own capacity guard IS the id bound — `IndexLike::max_nat()` for a
        // dense id is its `id_bound()`. A position the arena can hold therefore always has a
        // local id, and `len()` hands one back typed rather than as a raw count.
        let n_mset = self.nodes.mset.len().to_usize();
        let n_set = self.nodes.set.len().to_usize();
        let mset = (0..n_mset).map(move |i| {
            let l = <Cfg::Ids as NodeIds>::LMSet::from_usize(i);
            self.nodes.mset.get(l).global_id()
        });
        let set = (0..n_set).map(move |i| {
            let l = <Cfg::Ids as NodeIds>::LSet::from_usize(i);
            self.nodes.set.get(l).global_id()
        });
        mset.chain(set)
    }

    pub fn node_flags(&self, id: Cfg::G) -> u8 {
        match self.node_ref(id) {
            NodeRef::Plain0(l) => self.nodes.plain0.get(l).flags,
            NodeRef::Plain1(l) => self.nodes.plain1.get(l).flags,
            NodeRef::Plain2(l) => self.nodes.plain2.get(l).flags,
            NodeRef::Plain3(l) => self.nodes.plain3.get(l).flags,
            NodeRef::SPair(l) => self.nodes.spair.get(l).flags,
            NodeRef::PlainN(l) => self.nodes.plain_n.get(l).flags,
            NodeRef::Seq(l) => self.nodes.seq.get(l).flags,
            NodeRef::MSet(l) => self.nodes.mset.get(l).flags,
            NodeRef::Set(l) => self.nodes.set.get(l).flags,
            NodeRef::Lit(l) => self.nodes.lit.get(l).flags,
        }
    }

    /// Set one of the per-node control flags ([`FLAG_SUBSUMED`](crate::node_types::FLAG_SUBSUMED),
    /// [`FLAG_AC_COLLAPSED`](crate::node_types::FLAG_AC_COLLAPSED)) on `id`'s node.
    fn set_node_flag(&mut self, id: Cfg::G, flag: u8) {
        macro_rules! flag {
            ($store:expr, $l:expr) => {{
                let mut n = $store.get($l);
                n.flags |= flag;
                $store.set($l, n);
            }};
        }
        match self.node_ref(id) {
            NodeRef::Plain0(l) => flag!(self.nodes.plain0, l),
            NodeRef::Plain1(l) => flag!(self.nodes.plain1, l),
            NodeRef::Plain2(l) => flag!(self.nodes.plain2, l),
            NodeRef::Plain3(l) => flag!(self.nodes.plain3, l),
            NodeRef::SPair(l) => flag!(self.nodes.spair, l),
            NodeRef::PlainN(l) => flag!(self.nodes.plain_n, l),
            NodeRef::Seq(l) => flag!(self.nodes.seq, l),
            NodeRef::MSet(l) => flag!(self.nodes.mset, l),
            NodeRef::Set(l) => flag!(self.nodes.set, l),
            NodeRef::Lit(l) => flag!(self.nodes.lit, l),
        }
    }

    /// Clear one per-node control flag on `id`'s node. Only the reversible
    /// flags may be cleared (`FLAG_UNMATCHABLE`); `FLAG_SUBSUMED` is monotone.
    fn clear_node_flag(&mut self, id: Cfg::G, flag: u8) {
        debug_assert!(
            flag & crate::node_types::FLAG_SUBSUMED == 0,
            "FLAG_SUBSUMED is monotone"
        );
        macro_rules! unflag {
            ($store:expr, $l:expr) => {{
                let mut n = $store.get($l);
                if n.flags & flag != 0 {
                    n.flags &= !flag;
                    $store.set($l, n);
                }
            }};
        }
        match self.node_ref(id) {
            NodeRef::Plain0(l) => unflag!(self.nodes.plain0, l),
            NodeRef::Plain1(l) => unflag!(self.nodes.plain1, l),
            NodeRef::Plain2(l) => unflag!(self.nodes.plain2, l),
            NodeRef::Plain3(l) => unflag!(self.nodes.plain3, l),
            NodeRef::SPair(l) => unflag!(self.nodes.spair, l),
            NodeRef::PlainN(l) => unflag!(self.nodes.plain_n, l),
            NodeRef::Seq(l) => unflag!(self.nodes.seq, l),
            NodeRef::MSet(l) => unflag!(self.nodes.mset, l),
            NodeRef::Set(l) => unflag!(self.nodes.set, l),
            NodeRef::Lit(l) => unflag!(self.nodes.lit, l),
        }
    }

    /// User-level subsumption: exclude `id` from future pattern matching (the matcher's
    /// indices skip `FLAG_SUBSUMED`). Distinct from AC-collapse — see `FLAG_AC_COLLAPSED`.
    ///
    /// The node is logged as touched: a subsumption can remove a sequence rule's filter
    /// row, and semi-naive matching of sequence rules reads the round's subsumed nodes
    /// from the touched log (Semper design §7.6, "Affected classes", case 2). The
    /// delta index skips the node, as the full index does.
    pub fn subsume(&mut self, id: Cfg::G) {
        self.set_node_flag(id, crate::node_types::FLAG_SUBSUMED);
        self.touched.push(id);
    }

    /// Whether `id`'s e-class participates in e-matching (the generic e-matching
    /// shield; `true` by default). `None` if `id` has no class. Class-level
    /// analogue of the node-level [`is_subsumed`](Self::is_subsumed): where
    /// `subsume` shields one node, this reports whether a whole class is shielded.
    pub fn is_class_matchable(&self, id: Cfg::G) -> Option<bool> {
        let repr = self.classes.repr_id(self.classes.find_const(id))?;
        Some(self.classes.matchable(repr))
    }

    /// Shield (`false`) or un-shield (`true`) `id`'s whole e-class from
    /// e-matching. Resolves `id` to its class root and writes the bit through the
    /// semi-persistent class store, so it is captured and rolls back on
    /// `restore`. Both directions are supported (unlike `subsume`, which is
    /// monotone), because a relevancy client un-shields as terms become relevant.
    /// Shielded classes still participate fully in congruence and merges; only
    /// matching is affected — the matcher's index build skips a shielded class's
    /// nodes (`IndexStore::build`). Soundness-free: shielding only removes
    /// matches. No-op if `id` has no class.
    pub fn set_class_matchable(&mut self, id: Cfg::G, matchable: bool) {
        if let Some(repr) = self.classes.repr_id(self.classes.find_const(id)) {
            self.classes.set_class_matchable(repr, matchable);
        }
    }

    /// AC-completion collapse: retire `id` from the active AC rule set (its child
    /// multiset is reducible by a smaller AC rule, so it is no longer a superposition or
    /// inter-reduction source). The node stays **matchable** and a legal child; only
    /// completion's active set excludes it (design §6b). Distinct from `subsume`.
    pub(crate) fn set_cc_collapsed(&mut self, id: Cfg::G) {
        debug_assert!(
            matches!(self.node_ref(id), NodeRef::MSet(_) | NodeRef::Set(_)),
            "set_cc_collapsed on a non-completion node"
        );
        self.set_node_flag(id, crate::node_types::FLAG_AC_COLLAPSED);
    }

    /// If `id` is a literal node, return its interned value. Otherwise `None`.
    pub fn get_lit_val(&self, id: Cfg::G) -> Option<&L> {
        if let NodeRef::Lit(l) = self.node_ref(id) {
            Some(self.lits.get(self.nodes.lit.get(l).lit))
        } else {
            None
        }
    }

    /// If `id` is a literal node, return its interned LitValId.
    pub fn get_lit_val_id(&self, id: Cfg::G) -> Option<Cfg::V> {
        if let NodeRef::Lit(l) = self.node_ref(id) {
            Some(self.nodes.lit.get(l).lit)
        } else {
            None
        }
    }

    /// Return sort of a node (from its operator's signature).
    pub fn node_sort(&self, id: Cfg::G) -> Cfg::S {
        self.ops.info(self.node_op(id)).return_sort
    }

    /// Debug: verify the `FLAG_CONGRUENT_DUP` invariant — every class keeps at least one
    /// member without the flag.
    ///
    /// Its consumers skip flagged members, so a wholly flagged class would present no
    /// content at all: extraction reports that as infeasible rather than degrading
    /// (`extract.rs`), and the dump would emit an empty class. The invariant is maintained
    /// by never hinting a flagged node (`caches.rs`), which keeps every collision's
    /// survivor unflagged; this is the assertion that the reasoning holds in practice.
    pub fn debug_check_congruent_dup_invariant(&self) {
        use std::collections::BTreeMap;
        let mut total: BTreeMap<Cfg::G, usize> = BTreeMap::new();
        let mut flagged: BTreeMap<Cfg::G, usize> = BTreeMap::new();
        for id in self.node_ids() {
            let repr = self.class_repr(id);
            *total.entry(repr).or_default() += 1;
            if self.node_flags(id) & crate::node_types::FLAG_CONGRUENT_DUP != 0 {
                *flagged.entry(repr).or_default() += 1;
            }
        }
        for (repr, n) in &flagged {
            assert!(
                total[repr] > *n,
                "class {repr:?}: all {n} members carry FLAG_CONGRUENT_DUP, so the class has \
                 no visible member"
            );
        }
    }

    /// Check invariant I5: for every class and completion operator with at least one
    /// active node (neither `FLAG_SUBSUMED` nor `FLAG_AC_COLLAPSED`), the stored minimal
    /// monomial is a node of that class and operator, is not collapsed, and its monomial
    /// is the `monomial_cmp_key`-least among the class's active nodes of the operator. A
    /// stored node that is subsumed is accepted when its monomial is at most the least
    /// active one: it is still the class's least, and orients the same rules. The least
    /// monomial is recomputed here by a scan over all nodes, independently of the
    /// incremental maintenance (`register_if_fresh`, `fold_min_monomial`,
    /// `refresh_min_monomial`), so a maintenance gap shows as a mismatch. Unit and atomic
    /// classes are skipped: their right-hand side is `{}` or `{class}`, not the stored
    /// node. `Err` names the class, the operator, the stored node and monomial, and the
    /// recomputed ones.
    pub fn check_min_monomial_invariant(&self) -> Result<(), String> {
        use crate::node_types::{FLAG_AC_COLLAPSED, FLAG_SUBSUMED};
        use std::collections::BTreeMap;
        let inactive = FLAG_SUBSUMED | FLAG_AC_COLLAPSED;
        // Per (class representative, op): the least active monomial and a node holding it.
        let mut least: BTreeMap<(Cfg::G, Cfg::O), (Cfg::G, Vec<(Cfg::G, Cfg::M)>)> =
            BTreeMap::new();
        let mut buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
        for id in self.node_ids() {
            if !matches!(self.node_ref(id), NodeRef::MSet(_) | NodeRef::Set(_))
                || self.node_flags(id) & inactive != 0
            {
                continue;
            }
            self.node_monomial_into(id, &mut buf);
            let key = (self.class_repr(id), self.node_op(id));
            match least.get_mut(&key) {
                None => {
                    least.insert(key, (id, buf.clone()));
                }
                Some(cur) => {
                    if self.monomial_cmp_key(&buf, &cur.1) == std::cmp::Ordering::Less {
                        *cur = (id, buf.clone());
                    }
                }
            }
        }
        let show = |m: &[(Cfg::G, Cfg::M)]| -> String {
            let parts: Vec<String> = m
                .iter()
                .map(|&(g, k)| format!("{:?}^{}", g, k.to_usize()))
                .collect();
            format!("{{{}}}", parts.join(", "))
        };
        for (&(cls, op), (node, m)) in &least {
            // The right-hand side of a unit class is the empty monomial and that of an
            // atomic class is `{class}` (`class_rhs_into`): neither reads the stored
            // minimal monomial, and a size-1 node `f(x)` merged with `x` by degeneracy
            // sits below every stored one. Both are outside I5.
            if self
                .unit_node(op)
                .is_some_and(|u| self.class_repr(u) == cls)
                || self.class_atomic(cls) == Some(true)
            {
                continue;
            }
            let op_name = &self.ops.info(op).name;
            let Some(stored) = self.class_min_monomial_of_op(cls, op) else {
                return Err(format!(
                    "I5: class {cls:?}, op {op_name}: no stored minimal monomial, least \
                     active node {node:?} = {}",
                    show(m)
                ));
            };
            let flags = self.node_flags(stored);
            if self.class_repr(stored) != cls
                || self.node_op(stored) != op
                || flags & FLAG_AC_COLLAPSED != 0
            {
                self.node_monomial_into(stored, &mut buf);
                return Err(format!(
                    "I5: class {cls:?}, op {op_name}: stored minimal monomial {stored:?} = {} \
                     is {}; least active node {node:?} = {}",
                    show(&buf),
                    if self.class_repr(stored) != cls {
                        "in another class"
                    } else if self.node_op(stored) != op {
                        "a node of another op"
                    } else {
                        "collapsed"
                    },
                    show(m)
                ));
            }
            self.node_monomial_into(stored, &mut buf);
            let cmp = self.monomial_cmp_key(&buf, m);
            let ok = if flags & FLAG_SUBSUMED != 0 {
                cmp != std::cmp::Ordering::Greater
            } else {
                cmp == std::cmp::Ordering::Equal
            };
            if !ok {
                return Err(format!(
                    "I5: class {cls:?}, op {op_name}: stored minimal monomial {stored:?} = {} \
                     is not the least active monomial; least active node {node:?} = {} ({cmp:?})",
                    show(&buf),
                    show(m)
                ));
            }
        }
        Ok(())
    }

    /// Debug: panic when `check_min_monomial_invariant` fails. Run after each
    /// congruence rebuild of the completion loop in debug builds.
    pub fn debug_check_min_monomial_invariant(&self) {
        if let Err(e) = self.check_min_monomial_invariant() {
            panic!("{e}");
        }
    }

    /// Check that no collapsed completion node is irreducible: every node carrying
    /// `FLAG_AC_COLLAPSED` (and not `FLAG_SUBSUMED`) has a monomial, read under the
    /// current union-find, that one of the operator's laws or one of its current rules
    /// reduces. A collapsed node is not a rule, so an irreducible one is an equation
    /// completion never superposes. The laws are the unit as a summand, a count at or
    /// above the nilpotent order, a count above 1 under idempotence, and a summand
    /// together with the class of its existing inverse node. The rules are recomputed
    /// here as completion reads them: every active node whose monomial is greater than
    /// its class's right-hand side (`class_rhs_into`). A rule reduces a monomial when its
    /// left-hand side is a sub-multiset of it. Two cases pass without a reduction: a
    /// degenerate monomial (empty, or one summand of count 1) is an equality with a
    /// class, not a rule; a copy of an active node of the same operator, class and
    /// monomial leaves the equation to that node. `Err` names the node, its class, its
    /// monomial and the operator.
    pub fn check_no_irreducible_collapsed(&self) -> Result<(), String> {
        use crate::node_types::{FLAG_AC_COLLAPSED, FLAG_SUBSUMED};
        use std::collections::BTreeMap;
        type Mono<G, M> = Vec<(G, M)>;
        let mut collapsed: Vec<Cfg::G> = Vec::new();
        let mut rules: BTreeMap<Cfg::O, Vec<Mono<Cfg::G, Cfg::M>>> = BTreeMap::new();
        let mut active: std::collections::BTreeSet<(Cfg::O, Cfg::G, Mono<Cfg::G, Cfg::M>)> =
            std::collections::BTreeSet::new();
        let mut buf: Mono<Cfg::G, Cfg::M> = Vec::new();
        let mut rhs: Mono<Cfg::G, Cfg::M> = Vec::new();
        for id in self.completion_node_ids() {
            let flags = self.node_flags(id);
            if flags & FLAG_SUBSUMED != 0 {
                continue;
            }
            if flags & FLAG_AC_COLLAPSED != 0 {
                collapsed.push(id);
                continue;
            }
            self.node_monomial_into(id, &mut buf);
            if self.class_rhs_into(id, &mut rhs)
                && self.monomial_cmp_key(&buf, &rhs) == std::cmp::Ordering::Greater
            {
                rules.entry(self.node_op(id)).or_default().push(buf.clone());
            }
            active.insert((self.node_op(id), self.class_repr(id), buf.clone()));
        }
        let count = |m: &[(Cfg::G, Cfg::M)], g: Cfg::G| -> usize {
            m.iter()
                .filter(|&&(h, _)| h == g)
                .map(|&(_, k)| k.to_usize())
                .sum()
        };
        let contains = |big: &[(Cfg::G, Cfg::M)], small: &[(Cfg::G, Cfg::M)]| -> bool {
            small.iter().all(|&(g, _)| count(big, g) >= count(small, g))
        };
        for id in collapsed {
            let op = self.node_op(id);
            self.node_monomial_into(id, &mut buf);
            if buf.is_empty() || (buf.len() == 1 && buf[0].1.to_usize() == 1) {
                continue;
            }
            // A copy of an active node of its class: that node carries the equation.
            if active.contains(&(op, self.class_repr(id), buf.clone())) {
                continue;
            }
            let unit = self.unit_node(op).map(|u| self.classes.find_const(u));
            if unit.is_some_and(|u| count(&buf, u) > 0) {
                continue;
            }
            let law_count = match self.op_clamp(op) {
                CompletionClamp::Nilpotent { order } => {
                    buf.iter().any(|&(_, k)| k.to_usize() >= usize::from(order))
                }
                CompletionClamp::Idempotent => buf.iter().any(|&(_, k)| k.to_usize() > 1),
                CompletionClamp::Multiset => false,
            };
            if law_count {
                continue;
            }
            if let Some(inv) = self.inverse_op(op)
                && self.inverse_classes(inv).into_iter().any(|(y, x)| {
                    if y == x {
                        count(&buf, x) >= 2
                    } else {
                        count(&buf, x) > 0 && count(&buf, y) > 0
                    }
                })
            {
                continue;
            }
            if rules
                .get(&op)
                .is_some_and(|rs| rs.iter().any(|lhs| contains(&buf, lhs)))
            {
                continue;
            }
            let parts: Vec<String> = buf
                .iter()
                .map(|&(g, k)| format!("{:?}^{}", g, k.to_usize()))
                .collect();
            return Err(format!(
                "collapsed node {id:?} (class {:?}, op {}) has monomial {{{}}}, which no law \
                 and none of the op's {} current rules reduce",
                self.class_repr(id),
                self.ops.info(op).name,
                parts.join(", "),
                rules.get(&op).map_or(0, Vec::len)
            ));
        }
        Ok(())
    }

    /// Debug: panic when `check_no_irreducible_collapsed` fails. Run after each
    /// congruence rebuild of the completion loop in debug builds, beside
    /// `debug_check_min_monomial_invariant`.
    pub fn debug_check_no_irreducible_collapsed(&self) {
        if let Err(e) = self.check_no_irreducible_collapsed() {
            panic!("{e}");
        }
    }

    /// Debug: verify all nodes in each e-class have the same sort.
    /// Panics on violation. Only useful in tests / debug builds.
    pub fn debug_check_sort_invariant(&self) {
        use std::collections::HashMap;
        let mut class_sort: HashMap<Cfg::G, Cfg::S> = HashMap::new();
        for gid in self.node_ids() {
            let repr = self.find_const(gid);
            let sort = self.node_sort(gid);
            if let Some(&existing) = class_sort.get(&repr) {
                assert_eq!(
                    existing,
                    sort,
                    "sort invariant violated: e-class of '{}' has sort {:?}, but '{}' has sort {:?}",
                    self.node_op_name(repr),
                    existing,
                    self.node_op_name(gid),
                    sort
                );
            } else {
                class_sort.insert(repr, sort);
            }
        }
    }

    pub fn for_each_child(&self, id: Cfg::G, mut f: impl FnMut(Cfg::G, Cfg::M)) -> usize {
        match self.node_ref(id) {
            NodeRef::Plain0(_) => 0,
            NodeRef::Plain1(l) => {
                for &c in &self.nodes.plain1.get(l).children {
                    f(c, Cfg::M::ONE);
                }
                1
            }
            NodeRef::Plain2(l) => {
                for &c in &self.nodes.plain2.get(l).children {
                    f(c, Cfg::M::ONE);
                }
                2
            }
            NodeRef::Plain3(l) => {
                for &c in &self.nodes.plain3.get(l).children {
                    f(c, Cfg::M::ONE);
                }
                3
            }
            NodeRef::SPair(l) => {
                for &c in &self.nodes.spair.get(l).children {
                    f(c, Cfg::M::ONE);
                }
                2
            }
            NodeRef::PlainN(l) => {
                let n = self.nodes.plain_n.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    f(self.nodes.plain_n.pool_get(i), Cfg::M::ONE);
                }
                e - s
            }
            NodeRef::Seq(l) => {
                let n = self.nodes.seq.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    f(self.nodes.seq.pool_get(i), Cfg::M::ONE);
                }
                e - s
            }
            NodeRef::MSet(l) => {
                let n = self.nodes.mset.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    let c = self.nodes.mset.pool_get(i);
                    f(Cfg::mset_child_id(&c), Cfg::mset_child_mult(&c));
                }
                e - s
            }
            NodeRef::Set(l) => {
                let n = self.nodes.set.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    f(self.nodes.set.pool_get(i), Cfg::M::ONE);
                }
                e - s
            }
            NodeRef::Lit(_) => 0,
        }
    }

    /// Read the child at position `pos` from a fixed-arity node. O(1).
    /// Panics if `pos` is out of range or node is variadic/lit.
    pub fn child_at(&self, id: Cfg::G, pos: Cfg::Index) -> Cfg::G {
        // `Cfg::Index`-wide: a position offsets into the node's span in the child pool,
        // which is sized by that word (see `IndexStore::by_child_pos`). `as_usize` is
        // exact for every `IndexLike`, so no check is needed on the way in; an
        // out-of-range position still lands on the arm's bounds check or the `panic!`.
        let p = pos.as_usize();
        match self.node_ref(id) {
            NodeRef::Plain1(l) => self.nodes.plain1.get(l).children[p],
            NodeRef::Plain2(l) => self.nodes.plain2.get(l).children[p],
            NodeRef::Plain3(l) => self.nodes.plain3.get(l).children[p],
            NodeRef::SPair(l) => self.nodes.spair.get(l).children[p],
            NodeRef::PlainN(l) => {
                let n = self.nodes.plain_n.get(l);
                let (s, _) = n.span();
                self.nodes.plain_n.pool_get(s + p)
            }
            NodeRef::Seq(l) => {
                let n = self.nodes.seq.get(l);
                let (s, _) = n.span();
                self.nodes.seq.pool_get(s + p)
            }
            _ => panic!("child_at: not a plain/sequence node or pos out of range"),
        }
    }

    /// Read AC children as `(id, multiplicity)` pairs into `buf`.
    /// `id`'s children as the AC matcher reads them: an MSet node's entries, or a
    /// commutative pair's two children as two entries of multiplicity 1. The pair is
    /// not coalesced, so `(Eq x y)` still matches `Eq(a, a)` with `x = y = a`, as it
    /// did before commutative patterns went through `DecomposeAC`; a coalesced `{a:2}`
    /// would not match two elements of multiplicity 1 under maximum partition.
    pub fn ac_children(&self, id: Cfg::G, buf: &mut Vec<(Cfg::G, Cfg::M)>) {
        if matches!(self.node_ref(id), NodeRef::MSet(_)) {
            self.mset_children(id, buf);
            return;
        }
        buf.clear();
        self.for_each_child(id, |c, _| buf.push((c, Cfg::M::ONE)));
    }

    pub fn mset_children(&self, id: Cfg::G, buf: &mut Vec<(Cfg::G, Cfg::M)>) {
        buf.clear();
        match self.node_ref(id) {
            NodeRef::MSet(l) => {
                let n = self.nodes.mset.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    let c = self.nodes.mset.pool_get(i);
                    buf.push((Cfg::mset_child_id(&c), Cfg::mset_child_mult(&c)));
                }
            }
            _ => panic!("mset_children: not an MSet node"),
        }
    }

    /// Flatten nested same-op AC children of `op` in `self.mset_buf`, to a fixpoint, as
    /// [`flatten_ac_children`](Self::flatten_ac_children) does for ACI: a non-`atomic`
    /// child class whose `min_monomial` is an `op` node is replaced by that node's
    /// children, each with its count times the spliced child's. The product is checked:
    /// `Err(MultOverflow)` when it does not fit the configured width.
    fn flatten_mset_children(&mut self, op: Cfg::O) -> Result<(), MultOverflow> {
        let mut work = std::mem::take(&mut self.mset_flatten_buf);
        let mut out = std::mem::take(&mut self.mset_buf);
        work.clear();
        work.extend(out.iter().rev().copied());
        out.clear();
        // The cap of `flatten_ac_children`, for the same reason: it guards a degenerate
        // cyclic class, measured from the caller's own child count.
        let cap = work
            .len()
            .saturating_add(1)
            .saturating_add(64usize.saturating_mul(self.node_count()));
        let op_col = self.ops.completion_column(op);
        let mut expansions = 0usize;
        let mut result = Ok(());
        while let Some(c) = work.pop() {
            let cls = self.classes.find_const(Cfg::mset_child_id(&c));
            if let Some(col) = op_col
                && let Some(repr) = self.classes.repr_id(cls)
                && !self.classes.atomic(repr)
                && let Some(min_node) = self.classes.min_monomial(repr, col)
                && self.node_op(min_node) == op
                && matches!(self.node_ref(min_node), NodeRef::MSet(_))
            {
                assert!(
                    expansions < cap && out.len() <= cap,
                    "flatten_mset_children exceeded work cap (degenerate cyclic AC class?)"
                );
                expansions += 1;
                if self.record_flatten {
                    self.flatten_witness
                        .push((Cfg::mset_child_id(&c), min_node));
                }
                let k = Cfg::mset_child_mult(&c);
                let mut overflow = false;
                self.for_each_child(min_node, |cg, j| match k.checked_mul(j) {
                    Some(m) => work.push(Cfg::mset_child_with_mult(cg, m)),
                    None => overflow = true,
                });
                if overflow {
                    result = Err(MultOverflow);
                    break;
                }
                continue;
            }
            // The class, not the stored id: a spliced `c` is a stored child of `min_node`,
            // stale until the next rebuild (see `flatten_seq_children`), and a stale id
            // would also escape the coalescing that `normalize_by` does on equal ids.
            out.push(Cfg::mset_child_with_mult(cls, Cfg::mset_child_mult(&c)));
        }
        assert!(
            out.len() <= cap,
            "flatten_mset_children exceeded cap (degenerate cyclic AC class?)"
        );
        self.mset_buf = out;
        self.mset_flatten_buf = work;
        result
    }

    /// Flatten nested same-op ACI children of `op` in `self.g_buf`, to a fixpoint
    /// (`WF_flat`, design §6c). Each element is examined by its class's *canonical summand
    /// form* (`summand_form`, §9a), NOT by its union-find representative (which depends on
    /// merge order and is therefore non-canonical):
    ///
    /// - if the child's class is **non-`atomic`** (a pure `op`-sum), splice in that class's
    ///   `min_monomial` children (each by multiplicity), recursively;
    /// - otherwise (the class is `atomic`: referenced as a child, or has a non-AC node) the
    ///   single atom `{class}` is its canonical summand form, so keep the child as a summand.
    ///
    /// `g_buf` already holds `find`'d ids; a spliced child is `find`'d as it is emitted,
    /// since `min_node`'s stored children may predate this round's unions. Preserves §5b: `+{a,b}` used as `neg`'s child is
    /// `atomic`, so it is kept, not flattened. The semantic invariants make recursive
    /// expansion well-founded; a work/output budget is nevertheless enforced in every build
    /// profile so corrupted cyclic state is refused instead of looping or returning a
    /// partially flattened node.
    fn flatten_ac_children(&mut self, op: Cfg::O) {
        // Move the buffers out to satisfy the borrow checker while reading `self`.
        let mut work = std::mem::take(&mut self.flatten_buf);
        let mut out = std::mem::take(&mut self.g_buf);
        // Seed the worklist with the current children (reverse, so popping preserves
        // a stable order — order doesn't matter for AC but keeps traces readable).
        work.clear();
        work.extend(out.iter().rev().copied());
        out.clear();

        // Safety cap on the children *splicing adds*, which is the only unbounded
        // quantity here. Each splice replaces a child by a strictly smaller monomial, so
        // a well-formed graph drains well under this bound; the cap only guards a
        // degenerate cyclic class, which we must not loop on.
        //
        // Measured from the caller's own child count, not from zero: the seeded children
        // are given, not generated, and a monomial may legitimately be far wider than the
        // graph is deep. Anchoring at zero made a plain `f(a, a, …)` with more children
        // than `1 + 64 * node_count()` trip the assertion below — a large-but-well-formed
        // input diagnosed as a cyclic class.
        let cap = work
            .len()
            .saturating_add(1)
            .saturating_add(64usize.saturating_mul(self.node_count()));
        let op_col = self.ops.completion_column(op);
        let mut expansions = 0usize;
        while let Some(g) = work.pop() {
            let cls = self.classes.find_const(g);
            // A child is a pure `op`-sum to splice iff its class is non-atomic AND its
            // canonical summand for `op`'s column (`min_monomial`) is an AC node of this same
            // `op`. Both reads are representative-independent (per-class pool), never
            // `find`-keyed.
            let mut spliced = false;
            if let Some(col) = op_col
                && let Some(repr) = self.classes.repr_id(cls)
                && !self.classes.atomic(repr)
                && let Some(min_node) = self.classes.min_monomial(repr, col)
                && self.node_op(min_node) == op
                && matches!(self.node_ref(min_node), NodeRef::MSet(_) | NodeRef::Set(_))
            {
                assert!(
                    expansions < cap && out.len() <= cap,
                    "flatten_ac_children exceeded work cap (degenerate cyclic AC class?)"
                );
                expansions += 1;
                if self.record_flatten {
                    self.flatten_witness.push((g, min_node));
                }
                // Expand the canonical summand form; `for_each_child` yields (class, count)
                // for either representation (a Set member counts once).
                self.for_each_child(min_node, |cg, times| {
                    for _ in 0..times.to_usize() {
                        work.push(cg);
                    }
                });
                spliced = true;
            }
            if !spliced {
                // The class, not `g`: a spliced `g` is a stored child of `min_node`,
                // stale until the next rebuild (see `flatten_seq_children`).
                out.push(cls);
            }
        }
        assert!(
            out.len() <= cap,
            "flatten_ac_children exceeded cap (degenerate cyclic AC class?)"
        );

        self.g_buf = out;
        self.flatten_buf = work;
    }

    /// The canonical same-`op` sequence node of `g`'s class, or `None` if the class is not a
    /// **pure `op`-sequence** — i.e. if any member is something other than an `op` `Seq` node.
    ///
    /// This is the A-only counterpart of the AC `summand_form` predicate
    /// (`06-ac-congruence-closure.md` §6c) and it is chosen for the same reason: the answer
    /// must be a function of the class's *membership*, not of whichever node the union-find
    /// picked as representative (a representative-keyed test flattens or not depending on
    /// merge order, so it is not canonical — §6c's representative trap). Two consequences,
    /// both deliberate:
    ///
    /// - **Purity, not AC's `atomic`.** `atomic` cannot serve here: `register_if_fresh` sets
    ///   it on every class without a completion column, which includes every `Seq` class, so
    ///   for A-only ops it is constantly true. Purity plays the same role — a class holding
    ///   only `op`-sequences has no standalone atom form, so spelling it out is forced — and
    ///   it is what keeps a class that is *also* an atom from being spliced. That case is not
    ///   hypothetical: once a rule proves `gmul(b, inv(b)) = I`, `I`'s class holds a `Seq`
    ///   node, and splicing it into every later sequence would rewrite uphill and grow terms
    ///   without bound.
    /// - **The `op`-least member.** A class may hold several distinct `op`-sequences that were
    ///   merged; picking the least node id makes the choice a function of the class, and node
    ///   ids are assigned at creation and never renumbered, so this is merge-order independent.
    ///   Every spelling of the child therefore splices to the same sequence and the parents
    ///   land in one class.
    ///
    /// Cost is one class-ring walk, with an early exit on the first non-`op` member — so an
    /// ordinary atom child (a leaf, a constructor) costs its class's first member, and the
    /// full walk is paid only by classes that really are pure sequences.
    ///
    /// **Purity is monotone-false: it *closes*, it does not merely fail to open.** A union
    /// only adds members, so a class that is a pure `op`-sequence today can stop being one
    /// tomorrow and can never become one again. This test is therefore a function of the
    /// class *at the moment it is asked*, not of the term, and asking it at two different
    /// times is what used to make `(union (F a b) blob)` before `(F (F a b) c)` store the
    /// nested spelling while the reverse order stored the flat one.
    ///
    /// That is why this test is no longer the only one on the build path.
    /// [`push_seq_args`](crate::interpret::Interp::push_seq_args) in the term builder decides
    /// the written nesting from the syntax first, where no class can reach it, and this test
    /// then handles what is left: a child that came back from `add` already flattenable. Do
    /// not try to move the syntactic case here or into `add` — by this point a child is a
    /// plain `Cfg::G`, and a nested application is indistinguishable from a class id that
    /// happens to be a `Seq` node, which is what RHS rest bindings supply.
    fn pure_seq_node(&self, g: Cfg::G, op: Cfg::O) -> Option<Cfg::G> {
        let cls = self.classes.find_const(g);
        let mut best: Option<Cfg::G> = None;
        for n in self.classes.iter_class(cls) {
            // A proof-mode evidence node holds a client's raw spelling; splicing it would
            // put unflattened children back into the list.
            if self.is_evidence_node(n) {
                continue;
            }
            if self.node_op(n) != op || !matches!(self.node_ref(n), NodeRef::Seq(_)) {
                return None;
            }
            if best.is_none_or(|b| n.to_usize() < b.to_usize()) {
                best = Some(n);
            }
        }
        best
    }

    /// Flatten the nested same-op children selected by an A-only (`Seq`) op's
    /// [`AssocDir`](crate::registry::AssocDir), to a fixpoint while preserving order.
    ///
    /// A child is spliced iff [`pure_seq_node`](Self::pure_seq_node) names an `op`-sequence
    /// for its class and it lies on the selected spine: the first child for `Left`, the last
    /// child for `Right`, or any child for `Both`. A non-selected nested child remains one
    /// element, preserving explicit grouping such as `a - (b - c)`.
    ///
    /// `g_buf` already holds `find`'d ids; a spliced element is `find`'d as it is emitted,
    /// since the nested node's stored children may predate this round's unions. The least-node choice makes expansion
    /// well-founded for a valid append-only graph. The same work/output budget as
    /// `flatten_ac_children` is still enforced in every build profile: malformed state such
    /// as `X = {seq(X)}` is refused rather than looping or producing a partial normal form.
    fn flatten_seq_children(&mut self, op: Cfg::O) {
        use crate::registry::AssocDir;

        let dir = match self.ops.info(op).kind {
            OpKind::A { dir, .. } => dir,
            _ => unreachable!("flatten_seq_children requires an A-only operator"),
        };

        // Move the buffers out to satisfy the borrow checker while reading `self`.
        let mut scratch = std::mem::take(&mut self.flatten_buf);
        let mut out = std::mem::take(&mut self.g_buf);
        let cap = out
            .len()
            .saturating_add(1)
            .saturating_add(64usize.saturating_mul(self.node_count()));
        let mut expansions = 0usize;

        match dir {
            AssocDir::Both => {
                // Seed the worklist reversed, so popping yields children in sequence order.
                scratch.clear();
                scratch.extend(out.iter().rev().copied());
                out.clear();
                while let Some(g) = scratch.pop() {
                    let mut spliced = false;
                    if let Some(inner) = self.pure_seq_node(g, op)
                        && let NodeRef::Seq(l) = self.node_ref(inner)
                    {
                        assert!(
                            expansions < cap && out.len() <= cap,
                            "flatten_seq_children exceeded work cap (degenerate cyclic A class?)"
                        );
                        expansions += 1;
                        if self.record_flatten {
                            self.flatten_witness.push((g, inner));
                        }
                        let (s, e) = self.nodes.seq.get(l).span();
                        // Reversed again, so the elements pop back in their stored order.
                        for i in (s..e).rev() {
                            scratch.push(self.nodes.seq.pool_get(i));
                        }
                        spliced = true;
                    }
                    if !spliced {
                        // `find` here, not only at the seed: a spliced element is read
                        // from the nested node's *stored* children, which are stale when
                        // a union of this round has not been rebuilt yet. Kept raw, the
                        // node is stored under a non-canonical key that no later lookup
                        // spells, and `add` registers no use for it (an absorbed id has
                        // no `repr_id`), so no rebuild ever recanonicalizes it
                        // (seq_hashcons_miss_min.egg).
                        out.push(self.classes.find_const(g));
                    }
                }
            }
            AssocDir::Left | AssocDir::Right => loop {
                let edge = match dir {
                    AssocDir::Left => out.first().copied(),
                    AssocDir::Right => out.last().copied(),
                    AssocDir::Both => unreachable!(),
                };
                let Some(edge) = edge else {
                    break;
                };
                let Some(inner) = self.pure_seq_node(edge, op) else {
                    break;
                };
                let NodeRef::Seq(l) = self.node_ref(inner) else {
                    unreachable!("pure_seq_node must return a Seq node");
                };
                assert!(
                    expansions < cap && out.len() <= cap,
                    "flatten_seq_children exceeded work cap (degenerate cyclic A class?)"
                );
                expansions += 1;
                if self.record_flatten {
                    self.flatten_witness.push((edge, inner));
                }
                let (s, e) = self.nodes.seq.get(l).span();

                scratch.clear();
                if dir == AssocDir::Right {
                    scratch.extend_from_slice(&out[..out.len() - 1]);
                }
                // `find` each stored element: see the `Both` arm.
                for i in s..e {
                    scratch.push(self.classes.find_const(self.nodes.seq.pool_get(i)));
                }
                if dir == AssocDir::Left {
                    scratch.extend_from_slice(&out[1..]);
                }
                std::mem::swap(&mut out, &mut scratch);
            },
        }

        assert!(
            out.len() <= cap,
            "flatten_seq_children exceeded cap (degenerate cyclic A class?)"
        );

        scratch.clear();
        self.g_buf = out;
        self.flatten_buf = scratch;
    }

    /// Read ACI children (ids only, no multiplicities) into `buf`.
    pub fn set_children(&self, id: Cfg::G, buf: &mut Vec<Cfg::G>) {
        buf.clear();
        match self.node_ref(id) {
            NodeRef::Set(l) => {
                let n = self.nodes.set.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    buf.push(self.nodes.set.pool_get(i));
                }
            }
            _ => panic!("set_children: not a Set node"),
        }
    }

    /// Read A/PlainN children into `buf` in sequence order.
    pub fn seq_children(&self, id: Cfg::G, buf: &mut Vec<Cfg::G>) {
        buf.clear();
        match self.node_ref(id) {
            NodeRef::PlainN(l) => {
                let n = self.nodes.plain_n.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    buf.push(self.nodes.plain_n.pool_get(i));
                }
            }
            NodeRef::Seq(l) => {
                let n = self.nodes.seq.get(l);
                let (s, e) = n.span();
                for i in s..e {
                    buf.push(self.nodes.seq.pool_get(i));
                }
            }
            _ => panic!("seq_children: not a sequence node"),
        }
    }

    pub fn node_lit(&self, id: Cfg::G) -> Option<Cfg::V> {
        match self.node_ref(id) {
            NodeRef::Lit(l) => Some(self.nodes.lit.get(l).lit),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{OpId, SortId};
    use crate::lit_model::LitModel;
    use crate::literal::NiraLitVal;

    struct Th {
        int: SortId,
        x: OpId,
        y: OpId,
        z: OpId,
        w: OpId,
        f: OpId,
        g: OpId,
        h: OpId,
        eq: OpId,
        plus: OpId,
        and: OpId,
        sub: OpId,
        f4: OpId,
    }

    fn eg<const T: bool, const P: bool>() -> (EGraph31<NiraLitVal, T, P>, Th) {
        let mut eg = EGraph31::new();
        let int = eg.intern_sort("Int");
        let th = Th {
            int,
            x: eg.register_op0("x", int),
            y: eg.register_op0("y", int),
            z: eg.register_op0("z", int),
            w: eg.register_op0("w", int),
            f: eg.register_op1("f", int, int),
            g: eg.register_op2("g", int, int, int),
            h: eg.register_op3("h", int, int, int, int),
            eq: eg.register_c("eq", [int, int], int),
            plus: eg.register_mset("plus", int, int),
            and: eg.register_set("and", int, int),
            sub: eg.register_a("sub", int, int, crate::registry::AssocDir::Left),
            f4: eg.register_opn("f4", &[int, int, int, int], int),
        };
        (eg, th)
    }

    // I5 under in-place recanonization: a child merge into the identity class shrinks a stored
    // node below its class's min-monomial slot. The slot must follow the shrunk node (else the
    // class yields no completion rule), and roll back with the e-graph token.
    #[test]
    fn min_monomial_refreshes_on_recanonization_shrink_and_rolls_back() {
        use crate::registry::{Clamp, OpKind};
        let mut eg = EGraph31::<NiraLitVal, true, false>::new();
        let s = eg.intern_sort("E");
        let zero_op = eg.register_op0("zero", s);
        let zero = eg.add(zero_op, &[]);
        let add = eg.register_kind(
            "add",
            s,
            OpKind::MSet {
                arg_sort: s,
                clamp: Clamp::None,
                identity: None,
                cancellative: false,
            },
        );
        eg.set_unit_node(add, zero);
        // p, q get smaller ids than a, b: at equal size Add{p,q} ≺ Add{a,b} in degree-lex.
        let leaf = |eg: &mut EGraph31<NiraLitVal, true, false>, name: &str| {
            let op = eg.register_op0(name, s);
            eg.add(op, &[])
        };
        let p = leaf(&mut eg, "p");
        let q = leaf(&mut eg, "q");
        let a = leaf(&mut eg, "a");
        let b = leaf(&mut eg, "b");
        let z = leaf(&mut eg, "z");
        let r = leaf(&mut eg, "r");
        let n1 = eg.add(add, &[a, b]);
        let n2 = eg.add(add, &[p, q, r]);
        eg.set_cc(true);
        eg.merge(n1, n2);
        eg.rebuild();
        assert_eq!(eg.class_min_monomial(n1), Some(n1), "size 2 beats size 3");
        let d = eg.add(add, &[a, b, z]);
        let e = eg.add(add, &[p, q, z]);
        eg.rebuild();
        assert_ne!(eg.find(d), eg.find(e), "nothing joins d and e yet");

        let token = eg.mark(ShrinkPolicy::Never);
        eg.merge(r, zero);
        eg.rebuild();
        assert_eq!(
            eg.class_min_monomial(n1),
            Some(n2),
            "the shrunk node Add{{p,q}} is the class's least monomial and must be the slot"
        );
        assert_eq!(
            eg.find(d),
            eg.find(e),
            "a+b+z = p+q+z follows from a+b = p+q+r, r = 0"
        );

        eg.restore(token);
        assert_eq!(
            eg.class_min_monomial(n1),
            Some(n1),
            "the slot refresh must roll back with the e-graph token"
        );
        assert_ne!(eg.find(d), eg.find(e));
    }

    /// Randomized canonization coverage for the AC count-clamp / identity-drop / degenerate-arity
    /// normal form, with completion OFF (these are canonization facts, not completion — see the
    /// design doc "Canonization, not completion"). The oracle is an *independent* reference
    /// normalizer (`ref_normal`), so `add` is checked against a from-scratch computation of what
    /// the canonical class should be, over random inputs — the coverage the hand-written fixtures
    /// lack. Exercises plain AC, nilpotent order 2 AND order 3, idempotent, and identity, and both
    /// the build path (`add`) and the recanonize path (build distinct, then merge children).
    mod canonize_prop {
        use super::*;
        use crate::registry::{Clamp, OpKind};
        use proptest::prelude::*;
        use std::collections::BTreeMap;

        type Cfg31G = crate::id::ENodeId;

        /// Which AC op a random term uses; each is a distinct registered op sharing one sort.
        #[derive(Clone, Copy, Debug)]
        enum Kind {
            PlainAc,      // + : ℕ counts, no unit
            Nilpotent2,   // xor : count mod 2, unit e
            Nilpotent3,   // nz  : count mod 3, unit e
            Idempotent,   // and : count → 1
            IdentityPlus, // ip  : ℕ counts, unit e dropped
        }

        struct Env {
            eg: EGraph31<NiraLitVal, false, false>,
            atoms: Vec<Cfg31G>, // the 4 leaf classes usable as children
            unit: Cfg31G,       // the declared unit `e`
            plain: OpId,
            nil2: OpId,
            nil3: OpId,
            idem: OpId,
            ident: OpId,
        }

        fn op_of(env: &Env, k: Kind) -> OpId {
            match k {
                Kind::PlainAc => env.plain,
                Kind::Nilpotent2 => env.nil2,
                Kind::Nilpotent3 => env.nil3,
                Kind::Idempotent => env.idem,
                Kind::IdentityPlus => env.ident,
            }
        }

        fn make_env() -> Env {
            let mut eg = EGraph31::<NiraLitVal, false, false>::new();
            let s = eg.intern_sort("E");
            let e_op = eg.register_op0("e", s);
            let unit = eg.add(e_op, &[]);
            // The descriptor's `identity: UnitRef` is only read by the sortcheck resolver; the
            // egraph resolves the unit via `set_unit_node` (below), so pass `None` here. The clamp
            // field is what canonization reads.
            let mk = |eg: &mut EGraph31<NiraLitVal, false, false>, name: &str, clamp: Clamp| {
                eg.register_kind(
                    name,
                    s,
                    OpKind::MSet {
                        arg_sort: s,
                        clamp,
                        identity: None,
                        cancellative: false,
                    },
                )
            };
            let plain = mk(&mut eg, "plus", Clamp::None);
            let nil2 = mk(&mut eg, "xr2", Clamp::Nilpotent { order: 2 });
            let nil3 = mk(&mut eg, "xr3", Clamp::Nilpotent { order: 3 });
            let idem = eg.register_kind(
                "andop",
                s,
                OpKind::Set {
                    arg_sort: s,
                    clamp: Clamp::Idempotent,
                    identity: None,
                    cancellative: false,
                },
            );
            let ident = mk(&mut eg, "ip", Clamp::None);
            eg.set_unit_node(nil2, unit);
            eg.set_unit_node(nil3, unit);
            eg.set_unit_node(ident, unit);
            let a = eg.register_op0("a", s);
            let b = eg.register_op0("b", s);
            let c = eg.register_op0("c", s);
            let d = eg.register_op0("d", s);
            let atoms = vec![
                eg.add(a, &[]),
                eg.add(b, &[]),
                eg.add(c, &[]),
                eg.add(d, &[]),
            ];
            Env {
                eg,
                atoms,
                unit,
                plain,
                nil2,
                nil3,
                idem,
                ident,
            }
        }

        /// Independent reference: the canonical class a well-formed AC term over `children` (given
        /// as current class ids) should land in, computed from scratch — the oracle. Mirrors the
        /// *spec*: coalesce by class → drop unit (ops with an identity) → clamp counts → resolve
        /// degeneracy (empty ⇒ unit, single mult-1 ⇒ that child, else a built node).
        fn ref_normal(env: &mut Env, k: Kind, children: &[Cfg31G]) -> Cfg31G {
            let has_unit = matches!(k, Kind::Nilpotent2 | Kind::Nilpotent3 | Kind::IdentityPlus);
            let unit_cls = env.eg.find(env.unit);
            let mut counts: BTreeMap<u32, u32> = BTreeMap::new();
            for &g in children {
                *counts.entry(env.eg.find(g).raw()).or_insert(0) += 1;
            }
            if has_unit {
                counts.remove(&unit_cls.raw());
            }
            match k {
                Kind::Idempotent => {
                    for v in counts.values_mut() {
                        *v = 1;
                    }
                }
                Kind::Nilpotent2 => counts.retain(|_, v| {
                    *v %= 2;
                    *v != 0
                }),
                Kind::Nilpotent3 => counts.retain(|_, v| {
                    *v %= 3;
                    *v != 0
                }),
                Kind::PlainAc | Kind::IdentityPlus => {}
            }
            let total: u32 = counts.values().sum();
            if total == 0 {
                return env.eg.find(env.unit);
            }
            if counts.len() == 1 && *counts.values().next().unwrap() == 1 {
                return env
                    .eg
                    .find(crate::id::ENodeId::new(*counts.keys().next().unwrap()));
            }
            let mut flat: Vec<Cfg31G> = Vec::new();
            for (cls, cnt) in &counts {
                for _ in 0..*cnt {
                    flat.push(crate::id::ENodeId::new(*cls));
                }
            }
            let op = op_of(env, k);
            env.eg.add(op, &flat)
        }

        fn all_kinds() -> impl Strategy<Value = Kind> {
            prop_oneof![
                Just(Kind::PlainAc),
                Just(Kind::Nilpotent2),
                Just(Kind::Nilpotent3),
                Just(Kind::Idempotent),
                Just(Kind::IdentityPlus),
            ]
        }

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(400))]

            /// `add` must agree with the independent reference normalizer, and be permutation-
            /// invariant (AC). Child index 4 selects the unit, so unit-drop is exercised.
            /// Completion is OFF: this is pure canonization.
            #[test]
            fn add_matches_reference(
                k in all_kinds(),
                idxs in proptest::collection::vec(0usize..5, 1..8),
                perm_seed in any::<u64>(),
            ) {
                let mut env = make_env();
                let pick = |i: usize, env: &Env| if i < 4 { env.atoms[i] } else { env.unit };
                let children: Vec<Cfg31G> = idxs.iter().map(|&i| pick(i, &env)).collect();

                let op = op_of(&env, k);
                let built = env.eg.add(op, &children);
                let expected = ref_normal(&mut env, k, &children);
                prop_assert_eq!(
                    env.eg.find(built),
                    env.eg.find(expected),
                    "add vs reference: kind={:?} idxs={:?}", k, idxs
                );

                let mut shuffled = children.clone();
                let n = shuffled.len();
                for i in 0..n {
                    let j = ((perm_seed.wrapping_mul(6364136223846793005).wrapping_add(i as u64))
                        as usize) % n;
                    shuffled.swap(i, j);
                }
                let built2 = env.eg.add(op, &shuffled);
                prop_assert_eq!(env.eg.find(built), env.eg.find(built2), "permutation invariance");
            }

            /// Recanonize path: build a node with distinct children, merge a pair of children,
            /// rebuild (completion OFF → congruence + canonization only). The node's class must
            /// match the reference recomputed with the merge applied.
            #[test]
            fn recanonize_matches_reference(
                k in all_kinds(),
                idxs in proptest::collection::vec(0usize..4, 2..6),
                mi in 0usize..4,
                mj in 0usize..4,
            ) {
                prop_assume!(mi != mj);
                let mut env = make_env();
                let children: Vec<Cfg31G> = idxs.iter().map(|&i| env.atoms[i]).collect();
                let op = op_of(&env, k);
                let node = env.eg.add(op, &children);

                env.eg.merge(env.atoms[mi], env.atoms[mj]);
                env.eg.rebuild();

                let expected = ref_normal(&mut env, k, &children);
                prop_assert_eq!(
                    env.eg.find(node),
                    env.eg.find(expected),
                    "recanonize vs reference: kind={:?} idxs={:?} merge {}->{}", k, idxs, mi, mj
                );
            }

            /// `add_mset` canonicalizes what it is given and assumes nothing of it: ids
            /// made stale by a later merge, any entry order, a class in several entries, a
            /// zero count, the unit as a child, and a nested same-op node (index 5). It must
            /// land where `add` lands on the same children written out one by one, and,
            /// without the nested node, where the independent reference does.
            #[test]
            fn add_mset_matches_add(
                k in prop_oneof![
                    Just(Kind::PlainAc),
                    Just(Kind::Nilpotent2),
                    Just(Kind::Nilpotent3),
                    Just(Kind::IdentityPlus),
                ],
                entries in proptest::collection::vec((0usize..6, 0u32..4), 1..7),
                merge in proptest::option::of((0usize..4, 0usize..4)),
            ) {
                use crate::config::EGraphConfig;
                type C31 = crate::nodes::DefaultConfig;
                let mut env = make_env();
                let op = op_of(&env, k);
                let nested = env.eg.add(op, &[env.atoms[0], env.atoms[1]]);
                // Merge after building, so the atoms' ids are stale.
                if let Some((mi, mj)) = merge {
                    env.eg.merge(env.atoms[mi], env.atoms[mj]);
                    env.eg.rebuild();
                }
                let pick = |i: usize, env: &Env| match i {
                    0..4 => env.atoms[i],
                    4 => env.unit,
                    _ => nested,
                };
                let cs: Vec<_> = entries
                    .iter()
                    .map(|&(i, m)| {
                        C31::mset_child_with_mult(pick(i, &env), crate::multiplicity::Multiplicity(m))
                    })
                    .collect();
                let flat: Vec<Cfg31G> = entries
                    .iter()
                    .flat_map(|&(i, m)| std::iter::repeat_n(pick(i, &env), m as usize))
                    .collect();
                // An empty term needs a unit; plain AC has none.
                prop_assume!(!flat.is_empty() || !matches!(k, Kind::PlainAc));
                let by_mset = env.eg.add_mset(op, &cs).expect("small counts fit");
                let by_add = env.eg.add(op, &flat);
                prop_assert_eq!(
                    env.eg.find(by_mset),
                    env.eg.find(by_add),
                    "add_mset vs add: kind={:?} entries={:?} merge={:?}", k, entries, merge
                );
                if entries.iter().all(|&(i, _)| i != 5) {
                    let expected = ref_normal(&mut env, k, &flat);
                    prop_assert_eq!(env.eg.find(by_mset), env.eg.find(expected));
                }
            }
        }
    }

    #[test]
    fn congruence_plain() {
        let (ref mut eg, th) = eg::<false, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let fx = eg.add(th.f, &[x]);
        let fy = eg.add(th.f, &[y]);
        assert_ne!(eg.find(fx), eg.find(fy));
        eg.merge(x, y);
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fy));
    }

    // Acceptance #1 for the Nelson-Oppen export: `merged_log` captures BOTH the
    // directly-asserted merge and the congruence-derived merge, at the single
    // `merge_in_classes` chokepoint; with capture off it records nothing.
    #[test]
    fn merged_log_captures_direct_and_congruence() {
        let (ref mut eg, th) = eg::<true, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let fx = eg.add(th.f, &[x]);
        let fy = eg.add(th.f, &[y]);

        // Off by default: nothing to drain.
        assert!(!eg.record_merges());
        eg.set_record_merges(true);
        assert!(eg.take_merged_log().is_empty());

        // Direct merge x=y, then rebuild derives the congruence f(x)=f(y).
        let direct = eg.merge(x, y).expect("x and y start in distinct classes");
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fy), "congruence must unify f(x), f(y)");

        let log = eg.take_merged_log();
        assert!(
            log.len() >= 2,
            "expected the direct and the congruence merge, got {log:?}"
        );

        // The direct merge is captured verbatim as merge() returned it.
        assert!(
            log.contains(&direct),
            "direct merge {direct:?} missing from {log:?}"
        );

        // A congruence-derived merge is captured too: a distinct entry whose
        // pre-merge roots now canonicalize into the shared f(x)/f(y) class.
        let froot = eg.find(fx);
        assert!(
            log.iter()
                .any(|&(s, a)| (s, a) != direct && (eg.find(s) == froot || eg.find(a) == froot)),
            "no congruence-derived merge for f(x)=f(y) in {log:?}"
        );

        // Draining is a take: a second drain is empty.
        assert!(eg.take_merged_log().is_empty());

        // With capture off, further merges record nothing.
        eg.set_record_merges(false);
        let z = eg.add(th.z, &[]);
        let fz = eg.add(th.f, &[z]);
        eg.merge(x, z);
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fz));
        assert!(
            eg.take_merged_log().is_empty(),
            "capture off must record nothing"
        );
    }

    #[test]
    fn commutative_dedup() {
        let (ref mut eg, th) = eg::<false, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        assert_eq!(eg.add(th.eq, &[x, y]), eg.add(th.eq, &[y, x]));
    }

    // The per-class min-monomial pool column for the `plus` op tracks the degree-lex-least
    // `plus`-monomial across merges, and rolls back with the e-graph token. A leaf constant is
    // NOT a `plus`-monomial (it has no `plus` column); merging it in makes the class `atomic`
    // rather than lowering the `plus` column. See design §9a and the pool design in
    // `doc/design/05-algebraic-operators.md` §5.3.
    #[test]
    fn min_monomial_tracks_least_and_rolls_back() {
        let (ref mut eg, th) = eg::<true, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        let c = eg.add(th.w, &[]); // a leaf constant, to merge a sum into
        let s_xy = eg.add(th.plus, &[x, y]); // +{x,y}, size 2
        let s_xyz = eg.add(th.plus, &[x, y, z]); // +{x,y,z}, size 3

        // A fresh `plus` node's class holds itself in the `plus` column; a non-completion
        // constant has no completion column at all.
        assert_eq!(eg.class_min_monomial(s_xy), Some(s_xy));
        assert_eq!(eg.class_min_monomial(c), None);

        // Merge the two sums: the smaller monomial (+{x,y}, size 2) wins over +{x,y,z}.
        eg.merge(s_xy, s_xyz);
        let repr_min = eg.class_min_monomial(s_xy).unwrap();
        assert_eq!(eg.class_repr(repr_min), eg.class_repr(s_xy));
        assert_eq!(repr_min, s_xy, "min_monomial should pick the smaller sum");

        // Snapshot, then merge the leaf constant c in: the class becomes `atomic` (a constant
        // is its normal-form representative), while the `plus` column still holds the sum.
        let token = eg.mark(ShrinkPolicy::Never);
        eg.merge(c, s_xy);
        assert_eq!(
            eg.class_atomic(c),
            Some(true),
            "merging a constant in makes the class atomic"
        );
        assert_eq!(
            eg.class_min_monomial(s_xy),
            Some(s_xy),
            "the plus column keeps the least sum after the constant merge"
        );

        // Restore: the post-token merge is undone, atomicity reverts.
        eg.restore(token);
        assert_eq!(
            eg.class_min_monomial(s_xy),
            Some(s_xy),
            "min_monomial must roll back with the e-graph token"
        );
        assert_eq!(
            eg.class_atomic(s_xy),
            Some(false),
            "atomicity must roll back with the e-graph token"
        );
    }

    #[test]
    fn node_matchable_flag_rolls_back_and_class_members_listed() {
        // `FLAG_UNMATCHABLE` is written through the semi-persistent node store:
        // a flag change after a mark is undone by the restore, in both
        // directions. `class_members` lists every node of the class.
        let (ref mut eg, th) = eg::<true, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let fx = eg.add(th.f, &[x]);
        assert!(eg.is_node_matchable(fx));
        eg.set_node_matchable(fx, false);
        let token = eg.mark(ShrinkPolicy::Never);
        eg.set_node_matchable(fx, true);
        assert!(eg.is_node_matchable(fx));
        eg.restore(token);
        assert!(!eg.is_node_matchable(fx), "restore must re-shield the node");
        let token = eg.mark(ShrinkPolicy::Never);
        eg.set_node_matchable(x, false);
        eg.restore(token);
        assert!(eg.is_node_matchable(x), "restore must un-shield the node");
        eg.merge(x, y);
        eg.rebuild();
        let mut m: Vec<_> = eg.class_members(x).collect();
        m.sort();
        let mut want = vec![x, y];
        want.sort();
        assert_eq!(m, want);
    }

    #[test]
    fn congruence_undone_by_restore() {
        let (ref mut eg, th) = eg::<true, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let fx = eg.add(th.f, &[x]);
        let fy = eg.add(th.f, &[y]);
        let token = eg.mark(ShrinkPolicy::Never);
        eg.merge(x, y);
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fy));
        eg.restore(token);
        assert_ne!(eg.find(fx), eg.find(fy));
    }

    #[test]
    fn cascading_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let fx = eg.add(th.f, &[x]);
        let fy = eg.add(th.f, &[y]);
        let ffx = eg.add(th.f, &[fx]);
        let ffy = eg.add(th.f, &[fy]);
        eg.merge(x, y);
        eg.rebuild();
        assert_eq!(eg.find(ffx), eg.find(ffy));
    }

    #[test]
    fn ac_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
        let n1 = eg.add(th.plus, &[a, b]);
        let n2 = eg.add(th.plus, &[a, c]);
        eg.merge(b, c);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    #[test]
    fn aci_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
        let n1 = eg.add(th.and, &[a, b]);
        let n2 = eg.add(th.and, &[a, c]);
        eg.merge(b, c);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    #[test]
    fn aci_dedup_after_merge() {
        let (ref mut eg, th) = eg::<false, false>();
        let a = eg.add(th.x, &[]);
        let b = eg.add(th.y, &[]);
        let ab = eg.add(th.and, &[a, b]);
        let aa = eg.add(th.and, &[a]);
        eg.merge(a, b);
        eg.rebuild();
        assert_eq!(eg.find(ab), eg.find(aa));
    }

    #[test]
    fn hashcons_dedup() {
        let (ref mut eg, th) = eg::<false, false>();
        let x = eg.add(th.x, &[]);
        assert_eq!(eg.add(th.f, &[x]), eg.add(th.f, &[x]));
        assert_eq!(eg.len(), 2);
    }

    #[test]
    fn add_canonicalizes() {
        let (ref mut eg, th) = eg::<false, false>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let fx = eg.add(th.f, &[x]);
        eg.merge(x, y);
        assert_eq!(fx, eg.add(th.f, &[y]));
    }

    #[test]
    fn rebuild_empty() {
        let (ref mut eg, _) = eg::<false, false>();
        eg.rebuild();
    }

    #[test]
    fn add_after_restore() {
        let (ref mut eg, th) = eg::<true, false>();
        let x = eg.add(th.x, &[]);
        let token = eg.mark(ShrinkPolicy::Never);
        eg.add(th.f, &[x]);
        assert_eq!(eg.len(), 2);
        eg.restore(token);
        assert_eq!(eg.len(), 1);
        let gxx = eg.add(th.g, &[x, x]);
        assert_eq!(gxx, eg.add(th.g, &[x, x]));
    }

    #[test]
    fn rebuild_after_restore() {
        let (ref mut eg, th) = eg::<true, false>();
        let (x, y, z) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
        let (fx, fy, fz) = (eg.add(th.f, &[x]), eg.add(th.f, &[y]), eg.add(th.f, &[z]));
        let token = eg.mark(ShrinkPolicy::Never);
        eg.merge(x, y);
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fy));
        eg.restore(token);
        assert_ne!(eg.find(fx), eg.find(fy));
        eg.merge(x, z);
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fz));
        assert_ne!(eg.find(fx), eg.find(fy));
    }

    // -- Proofs --

    #[test]
    fn explain_non_equivalent() {
        let (ref mut eg, th) = eg::<false, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let mut buf = ProofBuf::new();
        assert!(!eg.explain(x, y, &mut buf));
    }

    #[test]
    fn explain_axiom() {
        let (ref mut eg, th) = eg::<false, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        eg.merge_justified(
            x,
            y,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(42),
            },
        );
        let mut buf = ProofBuf::new();
        eg.explain(x, y, &mut buf);
        assert!(buf.steps.iter().any(|&(_, _, j)| j
            == Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(42)
            }));
    }

    #[test]
    fn explain_chain() {
        let (ref mut eg, th) = eg::<false, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        eg.merge_justified(
            x,
            y,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(1),
            },
        );
        eg.merge_justified(
            y,
            z,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(2),
            },
        );
        let mut buf = ProofBuf::new();
        eg.explain(x, z, &mut buf);
        for (from, to, just) in &buf.steps {
            eprintln!("  {:?} ≡ {:?}  by {:?}", from, to, just);
        }
        assert!(buf.steps.len() >= 2);
    }

    #[test]
    fn lca_batch_explanations_match_regular_explanations() {
        let (ref mut eg, th) = eg::<false, true>();
        let nodes = [
            eg.add(th.x, &[]),
            eg.add(th.y, &[]),
            eg.add(th.z, &[]),
            eg.add(th.w, &[]),
        ];
        for (i, &(a, b)) in [
            (nodes[0], nodes[1]),
            (nodes[2], nodes[3]),
            (nodes[1], nodes[2]),
        ]
        .iter()
        .enumerate()
        {
            eg.merge_justified(
                a,
                b,
                Justification::Axiom {
                    axiom_id: crate::id::AxiomId::new(i as u32),
                },
            );
        }

        let table = crate::lca::LcaTable::build(
            eg.classes
                .proof_parent()
                .expect("PROOFS=true has a proof forest"),
            eg.len(),
        );
        for node in nodes {
            let representative = eg.find_const(node);
            let lca = table
                .lca(node, representative)
                .expect("equivalent nodes share a proof tree");
            let mut ordinary = ProofBuf::new();
            let mut indexed = ProofBuf::new();
            assert!(eg.explain(node, representative, &mut ordinary));
            assert!(
                eg.classes
                    .explain_with_lca(node, representative, lca, &mut indexed)
            );
            assert_eq!(indexed.steps, ordinary.steps);
        }
    }

    #[test]
    fn dump_all_proofs_covers_every_node() {
        let (ref mut eg, th) = eg::<false, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        eg.merge_justified(
            x,
            y,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(7),
            },
        );
        eg.merge_justified(
            y,
            z,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(8),
            },
        );

        let mut dump = Vec::new();
        let stats = eg.dump_all_proofs(&mut dump).expect("proof dump");
        assert_eq!(stats.terms, eg.len());
        assert_eq!(stats.nontrivial_proofs, 2);
        assert!(stats.steps >= 2);

        let text = String::from_utf8(dump).expect("UTF-8 proof dump");
        assert!(text.starts_with("# semi-persistent-proof-dump v2\n"));
        assert_eq!(
            text.lines()
                .filter(|line| line.starts_with("term "))
                .count(),
            3
        );
        assert!(text.contains("axiom id=7"));
        assert!(text.contains("axiom id=8"));
        assert!(text.contains("summary terms 3 nontrivial 2"));
    }

    #[test]
    fn dump_all_proofs_rejects_proof_disabled_graph() {
        let (ref mut eg, th) = eg::<false, false>();
        eg.add(th.x, &[]);
        let err = eg
            .dump_all_proofs(Vec::new())
            .expect_err("PROOFS=false must reject proof dumps");
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput);
    }

    #[test]
    fn explain_after_restore() {
        let (ref mut eg, th) = eg::<true, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let token = eg.mark(ShrinkPolicy::Never);
        eg.merge_justified(
            x,
            y,
            Justification::Axiom {
                axiom_id: crate::id::AxiomId::new(0),
            },
        );
        let mut buf = ProofBuf::new();
        assert!(eg.explain(x, y, &mut buf));
        eg.restore(token);
        buf.clear();
        assert!(!eg.explain(x, y, &mut buf));
    }

    /// Regression: `union()` on a PROOFS=true UF must panic, not silently
    /// leave a stale justification.
    #[test]
    #[should_panic(expected = "union() called on a PROOFS=true UnionFind")]
    fn union_without_justification_panics_on_proofs() {
        let (ref mut eg, th) = eg::<false, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        eg.merge(x, y); // must panic
    }

    /// Every step returned by `explain()` must carry the justification that
    /// was explicitly provided via `merge_justified`, never a stale default.
    #[test]
    fn explain_no_stale_justifications() {
        let (ref mut eg, th) = eg::<false, true>();
        let x = eg.add(th.x, &[]);
        let y = eg.add(th.y, &[]);
        let z = eg.add(th.z, &[]);
        let ax1 = crate::id::AxiomId::new(10);
        let ax2 = crate::id::AxiomId::new(20);
        eg.merge_justified(x, y, Justification::Axiom { axiom_id: ax1 });
        eg.merge_justified(y, z, Justification::Axiom { axiom_id: ax2 });
        let mut buf = ProofBuf::new();
        eg.explain(x, z, &mut buf);
        for &(_, _, just) in &buf.steps {
            match just {
                Justification::Axiom { axiom_id } => {
                    assert!(
                        axiom_id == ax1 || axiom_id == ax2,
                        "unexpected axiom_id {axiom_id:?} in proof step"
                    );
                }
                Justification::Congruence { .. } => {}
                Justification::Rewrite { .. } => {}
                Justification::Normalize { .. } | Justification::Build { .. } => {}
                Justification::Filler => unreachable!("filler is never a real proof step"),
                Justification::ACSuperposition { .. }
                | Justification::ACInterReduction { .. }
                | Justification::ACAxiomCP { .. }
                | Justification::Cancellative { .. }
                | Justification::InverseCancel { .. } => {
                    panic!("algebraic justification in a non-completion test")
                }
                Justification::Assumption { .. } => {
                    panic!("assumption justification in a non-euf test")
                }
            }
        }
    }

    // -- Rebuild coverage ---------------------------------------------------

    /// Plain3 congruence: h(x,y,z) ≡ h(w,y,z) after merge(x,w)
    #[test]
    fn congruence_plain3() {
        let (ref mut eg, th) = eg::<false, false>();
        let (x, y, z, w) = (
            eg.add(th.x, &[]),
            eg.add(th.y, &[]),
            eg.add(th.z, &[]),
            eg.add(th.w, &[]),
        );
        let n1 = eg.add(th.h, &[x, y, z]);
        let n2 = eg.add(th.h, &[w, y, z]);
        eg.merge(x, w);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    /// C-node congruence: eq(a,b) and eq(w,c) collide after merge(a,w), merge(b,c)
    #[test]
    fn commutative_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c, w) = (
            eg.add(th.x, &[]),
            eg.add(th.y, &[]),
            eg.add(th.z, &[]),
            eg.add(th.w, &[]),
        );
        let e1 = eg.add(th.eq, &[a, b]);
        let e2 = eg.add(th.eq, &[w, c]);
        eg.merge(a, w);
        eg.merge(b, c);
        eg.rebuild();
        assert_eq!(eg.find(e1), eg.find(e2));
    }

    /// C-node: find changes order but no collision (just reindex)
    #[test]
    fn commutative_reorder_no_collision() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b) = (eg.add(th.x, &[]), eg.add(th.y, &[]));
        let e = eg.add(th.eq, &[a, b]);
        eg.merge(a, b);
        eg.rebuild();
        let _ = eg.find(e);
    }

    /// PlainN congruence: f4(a,b,c,d) ≡ f4(a,e,c,d) after merge(b,e)
    #[test]
    fn plain_n_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let a = eg.add(th.x, &[]);
        let b = eg.add(th.y, &[]);
        let c = eg.add(th.z, &[]);
        let d = eg.add(th.w, &[]);
        let e_op = eg.register_op0("e", th.int);
        let e = eg.add(e_op, &[]);
        let n1 = eg.add(th.f4, &[a, b, c, d]);
        let n2 = eg.add(th.f4, &[a, e, c, d]);
        eg.merge(b, e);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    /// A-node congruence (associative, ordered)
    #[test]
    fn a_congruence() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
        let n1 = eg.add(th.sub, &[a, b]);
        let n2 = eg.add(th.sub, &[a, c]);
        eg.merge(b, c);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    /// The flattening guard must count expansion work, not only emitted output.
    /// A malformed self-expansion emits nothing, so the former `out.len()` guard
    /// never advanced and this call looped forever. Production construction cannot
    /// create this state; mutating the private child pool models defensive handling
    /// of corrupted data at the exact boundary the guard protects.
    #[test]
    #[should_panic(expected = "flatten_seq_children exceeded work cap")]
    fn associative_flatten_refuses_nonprogressing_cycle() {
        let (ref mut eg, th) = eg::<false, false>();
        let a = eg.add(th.x, &[]);
        let seq = eg.add(th.sub, &[a, a]);
        let NodeRef::Seq(local) = eg.node_ref(seq) else {
            panic!("associative node must use the Seq partition");
        };
        let (start, end) = eg.nodes.seq.get(local).span();
        assert_eq!(end - start, 2);
        eg.nodes.seq.pool_set(start, seq);
        eg.nodes.seq.pool_set(start + 1, seq);

        eg.g_buf.clear();
        eg.g_buf.push(seq);
        eg.flatten_seq_children(th.sub);
    }

    /// AC: different multiplicities after merge → no false collision
    #[test]
    fn ac_multiplicity_no_false_collision() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c, d) = (
            eg.add(th.x, &[]),
            eg.add(th.y, &[]),
            eg.add(th.z, &[]),
            eg.add(th.w, &[]),
        );
        let n1 = eg.add(th.plus, &[a, b, c]); // plus(a,b,c)
        let n2 = eg.add(th.plus, &[a, d]); // plus(a,d)
        eg.merge(b, d);
        eg.merge(c, d);
        eg.rebuild();
        // n1 → plus(a,2*repr_d), n2 → plus(a,repr_d) — NOT equal
        assert_ne!(eg.find(n1), eg.find(n2));
    }

    /// AC shrink: plus(a,a,b) after merge(a,b) → plus((repr,3))
    #[test]
    fn ac_shrink_after_merge() {
        let (ref mut eg, th) = eg::<false, false>();
        let a = eg.add(th.x, &[]);
        let b = eg.add(th.y, &[]);
        let n1 = eg.add(th.plus, &[a, a, b]); // plus((a,2),(b,1))
        let n2 = eg.add(th.plus, &[a, a, a]); // plus((a,3))
        eg.merge(a, b);
        eg.rebuild();
        assert_eq!(eg.find(n1), eg.find(n2));
    }

    /// Multiple merges before rebuild: worklist starts with >1 entry
    #[test]
    fn multiple_merges_before_rebuild() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b, c, d) = (
            eg.add(th.x, &[]),
            eg.add(th.y, &[]),
            eg.add(th.z, &[]),
            eg.add(th.w, &[]),
        );
        let fa = eg.add(th.f, &[a]);
        let fb = eg.add(th.f, &[b]);
        let fc = eg.add(th.f, &[c]);
        let fd = eg.add(th.f, &[d]);
        eg.merge(a, b);
        eg.merge(c, d);
        eg.rebuild();
        assert_eq!(eg.find(fa), eg.find(fb));
        assert_eq!(eg.find(fc), eg.find(fd));
        assert_ne!(eg.find(fa), eg.find(fc));
    }

    /// Diamond: g(a,b) uses both a and b; merge a and b
    #[test]
    fn diamond_fan_in() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b) = (eg.add(th.x, &[]), eg.add(th.y, &[]));
        let gab = eg.add(th.g, &[a, b]);
        eg.merge(a, b);
        eg.rebuild();
        let _ = eg.find(gab);
    }

    /// Fan-out: many parents of different kinds share the same child
    #[test]
    fn fan_out_many_parents() {
        let (ref mut eg, th) = eg::<false, false>();
        let a = eg.add(th.x, &[]);
        let b = eg.add(th.y, &[]);
        let p0 = eg.add(th.f, &[a]);
        let p1 = eg.add(th.g, &[a, a]);
        let p2 = eg.add(th.eq, &[a, a]);
        let p3 = eg.add(th.plus, &[a, b]);
        let p4 = eg.add(th.and, &[a, b]);
        eg.merge(a, b);
        eg.rebuild();
        for &p in &[p0, p1, p2, p3, p4] {
            let _ = eg.find(p);
        }
    }

    /// Deep cascade: merge at leaf propagates through 4 levels
    #[test]
    fn deep_cascade_4_levels() {
        let (ref mut eg, th) = eg::<false, false>();
        let (a, b) = (eg.add(th.x, &[]), eg.add(th.y, &[]));
        let fa = eg.add(th.f, &[a]);
        let fb = eg.add(th.f, &[b]);
        let ffa = eg.add(th.f, &[fa]);
        let ffb = eg.add(th.f, &[fb]);
        let fffa = eg.add(th.f, &[ffa]);
        let fffb = eg.add(th.f, &[ffb]);
        let ffffa = eg.add(th.f, &[fffa]);
        let ffffb = eg.add(th.f, &[fffb]);
        eg.merge(a, b);
        eg.rebuild();
        assert_eq!(eg.find(ffffa), eg.find(ffffb));
    }

    #[test]
    fn egraph63_smoke() {
        let mut eg = EGraph63::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);
        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        let fx = eg.add(f, &[x]);
        let fy = eg.add(f, &[y]);
        eg.merge(x, y);
        eg.rebuild();
        assert_eq!(eg.find(fx), eg.find(fy));
    }

    #[test]
    fn from_model_registers_builtins() {
        use crate::literal::NiraModel;
        let model = NiraModel;
        let eg = EGraph31::<NiraLitVal, false, false>::from_model(&model);
        for sort_desc in model.sorts() {
            let id = eg.sorts().id_by_name(sort_desc.name).unwrap();
            assert!(
                eg.sorts().is_builtin(id),
                "sort '{}' should be builtin",
                sort_desc.name
            );
        }
        for op_desc in model.ops() {
            let id = eg.ops().id_by_name(op_desc.name).unwrap();
            assert!(
                eg.ops().is_builtin(id),
                "op '{}' should be builtin",
                op_desc.name
            );
        }
    }

    #[test]
    #[should_panic(expected = "already registered")]
    fn from_model_rejects_op_collision() {
        use crate::literal::NiraModel;
        let mut eg = EGraph31::<NiraLitVal, false, false>::from_model(&NiraModel);
        let int = eg.intern_sort("Int");
        // "+" is a builtin op from NiraModel, registering again should panic
        eg.register_op2("+", int, int, int);
    }

    // Multiple MSet symbols are now supported (per-op min-monomial pool, step 4): rebuild with
    // two AC ops registered no longer panics. (End-to-end independence is checked by the
    // `ac_complete_multi_mset.egg` fixture.)
    #[test]
    fn cc_allows_two_mset_symbols() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let _plus = eg.register_mset("plus", int, int);
        let _times = eg.register_mset("times", int, int);
        eg.set_cc(true);
        eg.rebuild(); // two MSet ops => allowed, completes each independently
    }

    // One MSet op plus a Set (ACI) op is fine.
    #[test]
    fn cc_allows_one_mset_symbol() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let _plus = eg.register_mset("plus", int, int);
        let _and = eg.register_set("and", int, int);
        eg.set_cc(true);
        eg.rebuild();
    }
}

/// Run all core e-graph tests with both 31-bit and 63-bit configs.
#[cfg(test)]
mod dual_config_tests {
    use crate::canon::{MSetCanon, VarCanon};
    use crate::config::EGraphConfig;
    use crate::containers::ShrinkPolicy;
    use crate::egraph::EGraph;
    use crate::literal::NiraLitVal;
    use crate::union_find::{Justification, ProofBuf};

    struct Th<Cfg: EGraphConfig> {
        x: Cfg::O,
        y: Cfg::O,
        z: Cfg::O,
        w: Cfg::O,
        f: Cfg::O,
        h: Cfg::O,
        eq: Cfg::O,
        plus: Cfg::O,
        and: Cfg::O,
        sub: Cfg::O,
        f4: Cfg::O,
        lit_op: Cfg::O,
    }

    fn setup<Cfg: EGraphConfig, const T: bool, const P: bool>()
    -> (EGraph<Cfg, NiraLitVal, T, P>, Th<Cfg>)
    where
        MSetCanon: VarCanon<Cfg::G, Cfg::C>,
        Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
    {
        let mut eg = EGraph::new();
        let int = eg.intern_sort("Int");
        let th = Th {
            x: eg.register_op0("x", int),
            y: eg.register_op0("y", int),
            z: eg.register_op0("z", int),
            w: eg.register_op0("w", int),
            f: eg.register_op1("f", int, int),
            h: eg.register_op3("h", int, int, int, int),
            eq: eg.register_c("eq", [int, int], int),
            plus: eg.register_mset("plus", int, int),
            and: eg.register_set("and", int, int),
            sub: eg.register_a("sub", int, int, crate::registry::AssocDir::Left),
            f4: eg.register_opn("f4", &[int, int, int, int], int),
            lit_op: eg.register_lit("lit", int),
        };
        (eg, th)
    }

    macro_rules! dual {
        ($(fn $name:ident<$Cfg:ident>() $body:block)*) => {$(
            mod $name {
                use super::*;
                fn run<$Cfg: EGraphConfig>() where MSetCanon: VarCanon<$Cfg::G, $Cfg::C>, $Cfg::Policy: crate::config::StorePolicy<$Cfg, false>, $Cfg::Policy: crate::config::StorePolicy<$Cfg, true> $body
                #[test] fn bits31() { run::<crate::nodes::DefaultConfig>(); }
                #[test] fn bits63() { run::<crate::nodes::Config64>(); }
            }
        )*};
    }

    dual! {
        fn congruence_plain<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let fx = eg.add(th.f, &[x]);
            let fy = eg.add(th.f, &[y]);
            eg.merge(x, y);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fy));
        }

        fn commutative_dedup<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            assert_eq!(eg.add(th.eq, &[x, y]), eg.add(th.eq, &[y, x]));
        }

        fn cascading_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let fx = eg.add(th.f, &[x]);
            let fy = eg.add(th.f, &[y]);
            let ffx = eg.add(th.f, &[fx]);
            let ffy = eg.add(th.f, &[fy]);
            eg.merge(x, y);
            eg.rebuild();
            assert_eq!(eg.find(ffx), eg.find(ffy));
        }

        fn ac_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
            let n1 = eg.add(th.plus, &[a, b]);
            let n2 = eg.add(th.plus, &[a, c]);
            eg.merge(b, c);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn aci_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
            let n1 = eg.add(th.and, &[a, b]);
            let n2 = eg.add(th.and, &[a, c]);
            eg.merge(b, c);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn aci_dedup_after_merge<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let a = eg.add(th.x, &[]);
            let b = eg.add(th.y, &[]);
            let ab = eg.add(th.and, &[a, b]);
            let aa = eg.add(th.and, &[a]);
            eg.merge(a, b);
            eg.rebuild();
            assert_eq!(eg.find(ab), eg.find(aa));
        }

        fn hashcons_dedup<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let x = eg.add(th.x, &[]);
            assert_eq!(eg.add(th.f, &[x]), eg.add(th.f, &[x]));
            assert_eq!(eg.len(), 2);
        }

        fn add_canonicalizes<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let fx = eg.add(th.f, &[x]);
            eg.merge(x, y);
            assert_eq!(fx, eg.add(th.f, &[y]));
        }

        fn congruence_undone_by_restore<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, true, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let fx = eg.add(th.f, &[x]);
            let fy = eg.add(th.f, &[y]);
            let token = eg.mark(ShrinkPolicy::Never);
            eg.merge(x, y);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fy));
            eg.restore(token);
            assert_ne!(eg.find(fx), eg.find(fy));
        }

        fn rebuild_after_restore<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, true, false>();
            let (x, y, z) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
            let (fx, fy, fz) = (eg.add(th.f, &[x]), eg.add(th.f, &[y]), eg.add(th.f, &[z]));
            let token = eg.mark(ShrinkPolicy::Never);
            eg.merge(x, y);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fy));
            eg.restore(token);
            assert_ne!(eg.find(fx), eg.find(fy));
            eg.merge(x, z);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fz));
            assert_ne!(eg.find(fx), eg.find(fy));
        }

        fn congruence_plain3<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (x, y, z, w) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]), eg.add(th.w, &[]));
            let n1 = eg.add(th.h, &[x, y, z]);
            let n2 = eg.add(th.h, &[w, y, z]);
            eg.merge(x, w);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn commutative_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b, c, w) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]), eg.add(th.w, &[]));
            let e1 = eg.add(th.eq, &[a, b]);
            let e2 = eg.add(th.eq, &[w, c]);
            eg.merge(a, w);
            eg.merge(b, c);
            eg.rebuild();
            assert_eq!(eg.find(e1), eg.find(e2));
        }

        fn a_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b, c) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]));
            let n1 = eg.add(th.sub, &[a, b]);
            let n2 = eg.add(th.sub, &[a, c]);
            eg.merge(b, c);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn ac_shrink_after_merge<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let a = eg.add(th.x, &[]);
            let b = eg.add(th.y, &[]);
            let n1 = eg.add(th.plus, &[a, a, b]);
            let n2 = eg.add(th.plus, &[a, a, a]);
            eg.merge(a, b);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn deep_cascade_4_levels<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b) = (eg.add(th.x, &[]), eg.add(th.y, &[]));
            let fa = eg.add(th.f, &[a]);
            let fb = eg.add(th.f, &[b]);
            let ffa = eg.add(th.f, &[fa]);
            let ffb = eg.add(th.f, &[fb]);
            let fffa = eg.add(th.f, &[ffa]);
            let fffb = eg.add(th.f, &[ffb]);
            let ffffa = eg.add(th.f, &[fffa]);
            let ffffb = eg.add(th.f, &[fffb]);
            eg.merge(a, b);
            eg.rebuild();
            assert_eq!(eg.find(ffffa), eg.find(ffffb));
        }

        fn multiple_merges_before_rebuild<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b, c, d) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]), eg.add(th.w, &[]));
            let fa = eg.add(th.f, &[a]);
            let fb = eg.add(th.f, &[b]);
            let fc = eg.add(th.f, &[c]);
            let fd = eg.add(th.f, &[d]);
            eg.merge(a, b);
            eg.merge(c, d);
            eg.rebuild();
            assert_eq!(eg.find(fa), eg.find(fb));
            assert_eq!(eg.find(fc), eg.find(fd));
            assert_ne!(eg.find(fa), eg.find(fc));
        }

        fn explain_proof<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, true>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let z = eg.add(th.z, &[]);
            eg.merge_justified(x, y, Justification::Axiom { axiom_id: crate::id::AxiomId::new(1) });
            eg.merge_justified(y, z, Justification::Axiom { axiom_id: crate::id::AxiomId::new(2) });
            let mut buf = ProofBuf::new();
            eg.explain(x, z, &mut buf);
            assert!(buf.steps.len() >= 2);
        }

        fn explain_deep_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, true>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let fx = eg.add(th.f, &[x]);
            let fy = eg.add(th.f, &[y]);
            eg.merge_justified(x, y, Justification::Axiom { axiom_id: crate::id::AxiomId::new(10) });
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fy));
            let mut buf = ProofBuf::new();
            assert!(eg.explain_deep(fx, fy, &mut buf));
            assert!(buf.steps.iter().any(|(_, _, j)| matches!(j, Justification::Congruence { .. })));
            assert!(buf.steps.iter().any(|(_, _, j)| *j == Justification::Axiom { axiom_id: crate::id::AxiomId::new(10) }));
        }

        fn plain_n_congruence<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (x, y, z, w) = (eg.add(th.x, &[]), eg.add(th.y, &[]), eg.add(th.z, &[]), eg.add(th.w, &[]));
            let n1 = eg.add(th.f4, &[x, y, z, w]);
            let n2 = eg.add(th.f4, &[x, y, z, x]);
            eg.merge(w, x);
            eg.rebuild();
            assert_eq!(eg.find(n1), eg.find(n2));
        }

        fn a_not_commutative<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            let (a, b) = (eg.add(th.x, &[]), eg.add(th.y, &[]));
            let ab = eg.add(th.sub, &[a, b]);
            let ba = eg.add(th.sub, &[b, a]);
            assert_ne!(eg.find(ab), eg.find(ba));
        }

        fn lit_node<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            use crate::literal::NiraLitVal;
            use num_bigint::BigInt;
            let v1 = eg.intern_lit(NiraLitVal::Int(BigInt::from(42)));
            let v2 = eg.intern_lit(NiraLitVal::Int(BigInt::from(42)));
            assert_eq!(v1, v2);
            let n1 = eg.add_lit(th.lit_op, v1);
            let n2 = eg.add_lit(th.lit_op, v1);
            assert_eq!(n1, n2);
            let v3 = eg.intern_lit(NiraLitVal::Int(BigInt::from(99)));
            let n3 = eg.add_lit(th.lit_op, v3);
            assert_ne!(n1, n3);
        }

        fn is_empty_check<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, false, false>();
            // setup registers ops which add nodes, but is_empty checks node count
            let before = eg.len();
            let x = eg.add(th.x, &[]);
            assert_eq!(eg.len(), before + 1);
            let _ = x;
        }

        fn nested_mark_restore<Cfg>() {
            let (ref mut eg, th) = setup::<Cfg, true, false>();
            let x = eg.add(th.x, &[]);
            let y = eg.add(th.y, &[]);
            let z = eg.add(th.z, &[]);
            let fx = eg.add(th.f, &[x]);
            let fy = eg.add(th.f, &[y]);
            let fz = eg.add(th.f, &[z]);
            let t1 = eg.mark(ShrinkPolicy::Never);
            eg.merge(x, y);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fy));
            let t2 = eg.mark(ShrinkPolicy::Never);
            eg.merge(x, z);
            eg.rebuild();
            assert_eq!(eg.find(fx), eg.find(fz));
            eg.restore(t2);
            assert_eq!(eg.find(fx), eg.find(fy));
            assert_ne!(eg.find(fx), eg.find(fz));
            eg.restore(t1);
            assert_ne!(eg.find(fx), eg.find(fy));
            assert_ne!(eg.find(fx), eg.find(fz));
        }
    }
}
