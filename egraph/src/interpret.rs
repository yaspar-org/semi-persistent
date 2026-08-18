// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Layer 7: Command language interpreter.
//!
//! Parses and executes egglog programs against the e-graph.

use crate::apply::PreparedRule;
use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::containers::ShrinkPolicy;
use crate::egraph::{EGraph, EGraphToken};
use crate::lit_model::LitModel;
use crate::literal::LitVal;
use crate::sortcheck::{CCommand, CTerm};
use crate::union_find::Justification;

/// Error during interpretation.
#[derive(Debug)]
pub enum InterpError {
    /// Unknown sort name.
    UnknownSort(String),
    /// Unknown operator / function name.
    UnknownOp(String),
    /// Sort mismatch or arity error in a declaration.
    DeclError(String),
    /// Rule compilation failed.
    CompileError(crate::resolve::ResolveError),
    /// `(check ...)` assertion failed.
    CheckFailed(String),
    /// `(extract ...)` could not produce a term from the named class.
    ExtractFailed(crate::extract::ExtractError),
    /// `(pop)` without matching `(push)`.
    PopWithoutPush,
}

impl From<crate::resolve::ResolveError> for InterpError {
    fn from(e: crate::resolve::ResolveError) -> Self {
        InterpError::CompileError(e)
    }
}

impl std::fmt::Display for InterpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InterpError::UnknownSort(s) => write!(f, "unknown sort: {s}"),
            InterpError::UnknownOp(s) => write!(f, "unknown operator: {s}"),
            InterpError::DeclError(s) => write!(f, "declaration error: {s}"),
            InterpError::CompileError(e) => write!(f, "compile error: {e}"),
            InterpError::CheckFailed(s) => write!(f, "check failed: {s}"),
            InterpError::ExtractFailed(e) => write!(f, "extract failed: {e}"),
            InterpError::PopWithoutPush => write!(f, "pop without matching push"),
        }
    }
}

struct Mark<Cfg: EGraphConfig, O> {
    token: EGraphToken,
    rules_len: usize,
    globals_len: usize,
    _phantom: std::marker::PhantomData<(Cfg, O)>,
}

/// How AC congruence completion participates in a program run.
///
/// - `Off`: canonization and plain congruence only. Checks decide equality of
///   materialized canonical forms; AC-entailed equalities through erased
///   intermediate sums are not derived (the documented completeness gap,
///   `ac-congruence-completeness.md` Part I).
/// - `Eager`: every rebuild runs completion to fixpoint (the `--derive-ac-eqs`
///   behavior). Complete, but interleaving completion with saturation rules
///   re-runs it on a growing atom pool every round, which diverges on
///   rule-sets that keep minting new atoms.
/// - `Lazy`: saturation runs with completion off; an equality check that plain
///   congruence cannot decide runs goal-directed completion inside a
///   semi-persistent transaction shared across consecutive equality checks.
///   The queried pair is the completion goal: every pass stops with
///   `CompletionOutcome::GoalMet` the moment the pair joins, a second phase
///   alternates default-ruleset rule rounds with completion passes when the
///   graph's own closure does not decide the pair, and the node-growth budget
///   is checked inside a round's apply loops. The first non-equality-check
///   command restores the mark, so the O(touched) restore discards everything
///   the checks derived. Same decision procedure as `Eager` per query, paid
///   only when a query needs it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum AcMode {
    #[default]
    Off,
    Eager,
    Lazy,
}

pub struct Interpreter<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
> {
    pub eg: EGraph<Cfg, L, TRACK, PROOFS>,
    pub model: M,
    rules: Vec<PreparedRule<Cfg::O, Cfg::S, L>>,
    globals: crate::resolve::GlobalCtx<Cfg::S, Cfg::G>,
    marks: Vec<Mark<Cfg, Cfg::O>>,
    shrink_policy: ShrinkPolicy,
    strategy: crate::saturate::SaturationStrategy,
    ac_mode: AcMode,
    /// Alternation budget for a lazy check's second phase (rule rounds
    /// interleaved with completion fixpoints inside the transaction).
    lazy_ac_rounds: usize,
    /// The shared lazy-check transaction: `Some(mark)` while a run of
    /// consecutive equality checks accumulates completion state. Closed (and
    /// the graph restored) by the first non-check command or program end.
    lazy_txn: Option<EGraphToken>,
    /// Outcome of the most recent `(run …)` command (iterations, saturated, match steps).
    /// `None` until the first run. Exposed for diagnostics and benchmarking.
    last_sat: Option<crate::saturate::SatResult>,
    /// Wall time of the most recent `(run …)`, measured around the driver call.
    last_run_time: Option<std::time::Duration>,
    /// Index build scratch, owned here rather than by the saturation call.
    ///
    /// `(run 1)` is one round, so a scratch allocated per call would be built
    /// and dropped without ever being reused — which is exactly the shape of
    /// the E6 incremental cycle, twenty `(run 1)`s over one base. Holding it
    /// here carries the span arenas' allocation and their generation stamp
    /// across commands. Nothing has to be invalidated between runs, including
    /// across `(push)`/`(pop)`: a build bumps the stamp and writes only the
    /// keys its own stream carries, so whatever a previous run left in the
    /// table reads as empty.
    index_scratch: crate::index::IndexScratch<Cfg>,
}

impl<Cfg: EGraphConfig, L: LitVal, M: LitModel<Value = L>, const TRACK: bool, const PROOFS: bool>
    Interpreter<Cfg, L, M, TRACK, PROOFS>
where
    Cfg::O: std::hash::Hash,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    pub fn new(model: M) -> Self {
        let eg = EGraph::from_model(&model);
        Self {
            eg,
            model,
            rules: Vec::new(),
            globals: crate::resolve::GlobalCtx::new(),
            marks: Vec::new(),
            shrink_policy: ShrinkPolicy::Never,
            strategy: crate::saturate::SaturationStrategy::default(),
            ac_mode: AcMode::Off,
            lazy_ac_rounds: 32,
            lazy_txn: None,
            last_sat: None,
            last_run_time: None,
            index_scratch: crate::index::IndexScratch::new(),
        }
    }

    /// Create an interpreter with pre-built registries (from sortcheck).
    pub fn with_registries(
        model: M,
        sorts: crate::registry::SortRegistry<Cfg::S, TRACK>,
        ops: crate::registry::OpRegistry<Cfg::O, Cfg::S, TRACK>,
    ) -> Self {
        let eg = EGraph::with_registries(sorts, ops);
        Self {
            eg,
            model,
            rules: Vec::new(),
            globals: crate::resolve::GlobalCtx::new(),
            marks: Vec::new(),
            shrink_policy: ShrinkPolicy::Never,
            strategy: crate::saturate::SaturationStrategy::default(),
            ac_mode: AcMode::Off,
            lazy_ac_rounds: 32,
            lazy_txn: None,
            last_sat: None,
            last_run_time: None,
            index_scratch: crate::index::IndexScratch::new(),
        }
    }

    /// Set the shrink policy used by `push`/`pop`.
    pub fn set_shrink_policy(&mut self, policy: ShrinkPolicy) {
        self.shrink_policy = policy;
    }

    /// Select the saturation strategy used by `(run …)`.
    pub fn set_strategy(&mut self, strategy: crate::saturate::SaturationStrategy) {
        self.strategy = strategy;
    }

    /// Outcome of the most recent `(run …)` command, or `None` if none has run.
    pub fn last_sat(&self) -> Option<&crate::saturate::SatResult> {
        self.last_sat.as_ref()
    }

    /// Wall time of the most recent `(run …)`, or `None` if none has run. Measured around
    /// the saturation driver only — building the `:until` goal's terms is not included.
    pub fn last_run_time(&self) -> Option<std::time::Duration> {
        self.last_run_time
    }

    /// Enable/disable the AC congruence-completion pass (default off; see
    /// `EGraph::set_cc`). Equivalent to `set_ac_mode(Eager)` / `set_ac_mode(Off)`.
    pub fn set_cc(&mut self, enabled: bool) {
        self.set_ac_mode(if enabled { AcMode::Eager } else { AcMode::Off });
    }

    /// Select how AC completion participates in the run (see [`AcMode`]).
    /// `Lazy` keeps the e-graph's completion flag off; completion runs only
    /// inside the transaction a lazy check opens.
    pub fn set_ac_mode(&mut self, mode: AcMode) {
        self.ac_mode = mode;
        self.eg.set_cc(mode == AcMode::Eager);
    }

    /// Alternation budget for a lazy check's second phase (default 32 rounds).
    pub fn set_lazy_ac_rounds(&mut self, rounds: usize) {
        self.lazy_ac_rounds = rounds;
    }

    /// Select the merge survivor policy (see `EGraph::set_union_by`).
    pub fn set_union_by(&mut self, u: crate::egraph::UnionBy) {
        self.eg.set_union_by(u);
    }

    /// Open the shared lazy-check transaction if it is not already open: mark
    /// the graph, then enable completion. Consecutive equality checks keep it
    /// open and accumulate completion/alternation state; the first non-check
    /// command (or the end of the program) closes it via `lazy_txn_close`,
    /// and the O(touched) restore discards everything the checks derived.
    fn lazy_txn_open(&mut self) {
        if self.lazy_txn.is_none() {
            self.lazy_txn = Some(self.eg.mark(self.shrink_policy));
            self.eg.set_cc(true);
        }
    }

    /// Close the shared lazy-check transaction (no-op when none is open).
    fn lazy_txn_close(&mut self) {
        if let Some(token) = self.lazy_txn.take() {
            self.eg.set_cc(false);
            self.eg.set_cc_goal(None);
            self.eg.restore(token);
        }
    }

    /// Decide whether `a` and `b` are AC-entailed equal, inside the shared
    /// semi-persistent transaction (`lazy_txn_open`): every node the decision
    /// mints is discarded when the transaction closes, and consecutive checks
    /// continue from the accumulated state instead of re-deriving.
    ///
    /// Two phases, both goal-directed: the pair is installed as the
    /// completion goal (`set_cc_goal`), so every completion pass — including
    /// the ones inside the alternation — stops mid-closure the moment the
    /// pair joins. First, one completion rebuild on the current graph — with
    /// no rules interleaving, the case the termination argument (Dickson
    /// antichain over a fixed atom pool) covers — decides pure AC congruence
    /// consequences. Second, if the pair is still apart and the program has
    /// rules, the saturation driver runs the default ruleset with the pair as
    /// its `:until` goal and completion on, so rounds alternate rule matching
    /// with completion passes, bounded by `lazy_ac_rounds` and by the
    /// node-growth budget (checked in-round, not only between rounds).
    ///
    /// Returns `(equal, inconclusive)`. `inconclusive` means a budget stopped
    /// the search first; a `false` verdict with `inconclusive == false` is a
    /// joint fixpoint of rules and completion that never joined the pair, so
    /// the equality is not derivable by this program's rules plus ground AC
    /// congruence.
    fn lazy_ac_decide(&mut self, a: Cfg::G, b: Cfg::G) -> (bool, bool) {
        self.lazy_txn_open();
        self.eg.set_cc_goal(Some((a, b)));
        self.eg.rebuild();
        let mut equal = self.eg.find(a) == self.eg.find(b);
        let aborted = |eg: &EGraph<Cfg, L, TRACK, PROOFS>| {
            matches!(
                eg.completion_outcome(),
                Some(crate::egraph::CompletionOutcome::AbortedGrowthLimit { .. })
            )
        };
        let mut inconclusive = !equal && aborted(&self.eg);
        if !equal && !inconclusive && !self.rules.is_empty() {
            let spec = crate::saturate::RunSpec {
                limit: self.lazy_ac_rounds,
                ruleset: None,
                until: Some(crate::saturate::RunGoal {
                    left: a,
                    right: b,
                    equal: true,
                }),
            };
            let result = match self.strategy {
                crate::saturate::SaturationStrategy::Naive => self.eg.saturate_spec_in(
                    &self.rules,
                    &self.model,
                    &spec,
                    &self.globals,
                    &mut self.index_scratch,
                ),
                crate::saturate::SaturationStrategy::SemiNaive => self.eg.saturate_semi_spec_in(
                    &self.rules,
                    &self.model,
                    &spec,
                    &self.globals,
                    &mut self.index_scratch,
                ),
            };
            equal = self.eg.find(a) == self.eg.find(b);
            inconclusive = !equal && (aborted(&self.eg) || !result.saturated);
        }
        self.eg.set_cc_goal(None);
        (equal, inconclusive)
    }

    /// Enable/disable the runtime reduced-basis invariant checks (default off; see
    /// `EGraph::set_basis_checks`). Diagnostic only: superlinear brute-force checks.
    pub fn set_basis_checks(&mut self, enabled: bool) {
        self.eg.set_basis_checks(enabled);
    }

    fn alloc_axiom_id(&mut self, lhs: Cfg::G, rhs: Cfg::G) -> crate::id::AxiomId {
        let name = format!("axiom_{}", self.eg.axioms().len());
        self.eg.register_axiom(&name, lhs, rhs)
    }

    fn bind_global(&mut self, name: String, id: Cfg::G, sort: Cfg::S) {
        self.globals.insert(name, sort, id);
    }

    /// Look up a global binding by name.
    pub fn global(&mut self, name: &str) -> Option<(Cfg::G, Cfg::S)> {
        self.globals
            .get(name)
            .map(|(_, sort, id)| (self.eg.find(id), sort))
    }

    // ── Checked pipeline ──────────────────────────────────────────────

    /// Run a pre-checked program (output of `sortcheck_program`).
    pub fn run_checked(&mut self, cmds: &[CCommand<Cfg::O, Cfg::S, L>]) -> Result<(), InterpError> {
        // Match steps are only counted while the (thread-local) counter is armed, and it is
        // off by default because arming it costs a load per match step. A program that asks
        // for stats has asked to pay that.
        if cmds.iter().any(|c| matches!(c, CCommand::PrintStats(_))) {
            crate::ematch::set_match_step_counting(true);
        }
        for cmd in cmds {
            // The lazy-check transaction is shared across a run of consecutive
            // equality checks (each check continues the accumulated
            // completion/alternation state instead of re-deriving); any other
            // command must see the untouched graph, so the transaction closes
            // first. `(check t)` closes it too: a bare check materializes its
            // term permanently, which an open transaction would discard.
            if !matches!(cmd, CCommand::CheckEq(..) | CCommand::CheckNeq(..)) {
                self.lazy_txn_close();
            }
            let r = self.exec_checked(cmd);
            if r.is_err() {
                self.lazy_txn_close();
            }
            r?;
        }
        self.lazy_txn_close();
        Ok(())
    }

    /// Reject a rule whose multiplicity literals exceed the configured width, before it
    /// can be saturated with. See [`crate::apply::check_mult_literals`] for why this has
    /// to happen at install rather than at match/apply time.
    fn check_rule_mults(
        name: &str,
        rule: &PreparedRule<Cfg::O, Cfg::S, L>,
    ) -> Result<(), InterpError> {
        crate::apply::check_mult_literals::<Cfg, _, _, _>(rule).map_err(|n| {
            InterpError::DeclError(format!(
                "rule `{name}`: multiplicity literal {n} exceeds the configured \
                 multiplicity width (EGraphConfig::M holds at most {})",
                <Cfg::M as crate::multiplicity::MultiplicityLike>::MAX
            ))
        })?;
        crate::apply::check_rhs_mult_exprs(rule)
            .map_err(|msg| InterpError::DeclError(format!("rule `{name}`: {msg}")))
    }

    fn exec_checked(&mut self, cmd: &CCommand<Cfg::O, Cfg::S, L>) -> Result<(), InterpError> {
        match cmd {
            CCommand::Decl(_) => {
                // Already registered into egraph during sortcheck. No-op.
            }
            CCommand::Let(name, ct) => {
                let (id, sort) = self.build_cterm(ct);
                self.bind_global(name.clone(), id, sort);
            }
            CCommand::Insert(ct) => {
                self.build_cterm(ct);
            }
            CCommand::Union(a, b) => {
                let (a_id, _) = self.build_cterm(a);
                let (b_id, _) = self.build_cterm(b);
                if PROOFS {
                    let axiom_id = self.alloc_axiom_id(a_id, b_id);
                    self.eg
                        .merge_justified(a_id, b_id, Justification::Axiom { axiom_id });
                } else {
                    self.eg.merge(a_id, b_id);
                }
                self.eg.rebuild();
            }
            CCommand::Check(ct) => {
                self.build_cterm(ct);
            }
            CCommand::CheckEq(a, b) => {
                let before = self.eg.node_count();
                let (a_id, _) = self.build_cterm(a);
                let (b_id, _) = self.build_cterm(b);
                // Install the goal before any rebuild: with the shared
                // transaction open, the term-build rebuild runs completion,
                // and the goal keeps it from running past the answer.
                if self.ac_mode == AcMode::Lazy {
                    self.eg.set_cc_goal(Some((a_id, b_id)));
                }
                if self.eg.node_count() > before {
                    self.eg.rebuild();
                }
                if self.eg.find(a_id) != self.eg.find(b_id) {
                    if self.ac_mode == AcMode::Lazy {
                        match self.lazy_ac_decide(a_id, b_id) {
                            (true, _) => return Ok(()),
                            (false, aborted) => {
                                return Err(InterpError::CheckFailed(if aborted {
                                    "terms are not equal (lazy AC completion hit its growth \
                                     budget before deciding; inconclusive)"
                                        .into()
                                } else {
                                    "terms are not equal (lazy AC completion converged)".into()
                                }));
                            }
                        }
                    }
                    return Err(InterpError::CheckFailed("terms are not equal".into()));
                }
                self.eg.set_cc_goal(None);
            }
            CCommand::CheckNeq(a, b) => {
                let before = self.eg.node_count();
                let (a_id, _) = self.build_cterm(a);
                let (b_id, _) = self.build_cterm(b);
                if self.ac_mode == AcMode::Lazy {
                    self.eg.set_cc_goal(Some((a_id, b_id)));
                }
                if self.eg.node_count() > before {
                    self.eg.rebuild();
                }
                if self.eg.find(a_id) == self.eg.find(b_id) {
                    self.eg.set_cc_goal(None);
                    return Err(InterpError::CheckFailed("terms are equal".into()));
                }
                // Lazy mode makes `!=` stronger, not weaker: distinct classes may
                // still be AC-entailed equal through erased intermediate sums, so
                // the disequality is confirmed under completion before it passes.
                if self.ac_mode == AcMode::Lazy && self.lazy_ac_decide(a_id, b_id).0 {
                    return Err(InterpError::CheckFailed(
                        "terms are equal (derived by lazy AC completion)".into(),
                    ));
                }
            }
            CCommand::Extract(ct) => {
                let before = self.eg.node_count();
                let (id, _) = self.build_cterm(ct);
                if self.eg.node_count() > before {
                    self.eg.rebuild();
                }
                // An extract that cannot produce a term is a program error, not a printed
                // remark: the class is named and the reason distinguished (every node
                // `:unextractable`, versus no grounded node at all).
                match crate::extract::extract_best(&self.eg, id) {
                    Ok(t) => println!("{t}"),
                    Err(e) => return Err(InterpError::ExtractFailed(e)),
                }
            }
            CCommand::Rewrite {
                query,
                rhs,
                root_vid,
                subsume,
                ruleset,
            } => {
                let name = format!("rewrite_{}", self.eg.rules().len());
                let rule_id = self.eg.register_rule(&name, "", "");
                let compiled_rhs = crate::apply::compile_rhs(rhs);
                let mut actions = vec![crate::apply::CompiledAction::Union(
                    rule_id,
                    crate::apply::RhsOp::FetchNode(*root_vid),
                    compiled_rhs,
                )];
                if *subsume {
                    actions.push(crate::apply::CompiledAction::Subsume(*root_vid));
                }
                let rule = PreparedRule {
                    rule_id,
                    query: query.clone(),
                    actions,
                    ruleset: *ruleset,
                };
                Self::check_rule_mults(&name, &rule)?;
                self.rules.push(rule);
            }
            CCommand::Rule {
                query,
                actions,
                ruleset,
            } => {
                let name = format!("rule_{}", self.eg.rules().len());
                let rule_id = self.eg.register_rule(&name, "", "");
                let compiled: Vec<_> = actions
                    .iter()
                    .map(|a| crate::apply::compile_action(a, rule_id))
                    .collect();
                let rule = PreparedRule {
                    rule_id,
                    query: query.clone(),
                    actions: compiled,
                    ruleset: *ruleset,
                };
                Self::check_rule_mults(&name, &rule)?;
                self.rules.push(rule);
            }
            CCommand::Run {
                ruleset,
                limit,
                until,
            } => {
                // A `:until` goal is over ground terms, so it is built once, before the run,
                // and only its classes move afterwards. Building it can add nodes, which is
                // why the graph is rebuilt before the driver sees it.
                let goal = match until {
                    None => None,
                    Some(g) => {
                        let before = self.eg.node_count();
                        let (l, _) = self.build_cterm(&g.left);
                        let (r, _) = self.build_cterm(&g.right);
                        if self.eg.node_count() > before {
                            self.eg.rebuild();
                        }
                        Some(crate::saturate::RunGoal {
                            left: l,
                            right: r,
                            equal: g.equal,
                        })
                    }
                };
                let spec = crate::saturate::RunSpec {
                    limit: *limit as usize,
                    ruleset: *ruleset,
                    until: goal,
                };
                let t0 = std::time::Instant::now();
                let result = match self.strategy {
                    crate::saturate::SaturationStrategy::Naive => self.eg.saturate_spec_in(
                        &self.rules,
                        &self.model,
                        &spec,
                        &self.globals,
                        &mut self.index_scratch,
                    ),
                    crate::saturate::SaturationStrategy::SemiNaive => {
                        self.eg.saturate_semi_spec_in(
                            &self.rules,
                            &self.model,
                            &spec,
                            &self.globals,
                            &mut self.index_scratch,
                        )
                    }
                };
                self.last_run_time = Some(t0.elapsed());
                self.last_sat = Some(result);
            }
            CCommand::PrintSize(op) => {
                let counts = self.eg.op_node_counts();
                match op {
                    Some(o) => println!("{}", counts[o.to_usize()]),
                    None => {
                        // Ops with no nodes are omitted: the builtin literal and primitive
                        // ops would otherwise dominate the listing on every program.
                        let mut total = 0;
                        for (name, n) in self.eg.ops().names().zip(counts.iter()) {
                            if *n > 0 {
                                println!("{name}: {n}");
                            }
                            total += n;
                        }
                        println!("total: {total}");
                    }
                }
            }
            CCommand::PrintStats(file) => {
                let stats = self.stats_snapshot();
                match file {
                    None => print!("{}", stats.render_text()),
                    Some(path) => std::fs::write(path, stats.render_json()).map_err(|e| {
                        InterpError::DeclError(format!("print-stats :file '{path}': {e}"))
                    })?,
                }
            }
            CCommand::Push(shrink) => {
                let policy = if *shrink {
                    ShrinkPolicy::IfOverallocated {
                        factor: 4,
                        headroom: 2,
                    }
                } else {
                    self.shrink_policy
                };
                self.marks.push(Mark {
                    token: self.eg.mark(policy),
                    rules_len: self.rules.len(),
                    globals_len: self.globals.len(),
                    _phantom: std::marker::PhantomData,
                });
            }
            CCommand::AntiUnify {
                left,
                right,
                playouts,
                algorithm,
            } => {
                let before = self.eg.node_count();
                let (l_id, _) = self.build_cterm(left);
                let (r_id, _) = self.build_cterm(right);
                if self.eg.node_count() > before {
                    self.eg.rebuild();
                }

                let alg = match algorithm.as_str() {
                    "exact" => crate::au::session::AuAlgorithm::Exact,
                    "uct" => crate::au::session::AuAlgorithm::Uct,
                    other => {
                        return Err(InterpError::CheckFailed(format!(
                            "unknown AU algorithm '{other}' (expected exact or uct)"
                        )));
                    }
                };

                let snap = crate::au::egraph_api::AuSnapshot::new(&self.eg)
                    .map_err(|e| InterpError::CheckFailed(format!("{e}")))?;

                let config = crate::au::session::AuConfig {
                    algorithm: alg,
                    playouts: *playouts,
                    ..Default::default()
                };

                let result = crate::au::session::anti_unify(&snap, l_id, r_id, &config)
                    .map_err(|e| InterpError::CheckFailed(format!("{e}")))?;

                let op_namer = |op: &crate::au::terms::TermOp<Cfg::O, Cfg::V>| match op {
                    crate::au::terms::TermOp::EGraph(o) => self.eg.ops().info(*o).name.clone(),
                    crate::au::terms::TermOp::Literal(_, v) => {
                        format!("{}", self.eg.lits().get(*v))
                    }
                    crate::au::terms::TermOp::Variants => "Variants".to_string(),
                };
                let rendered = result.pretty_print_with(op_namer, 80);
                let cr = crate::au::session::compression_ratio(
                    &snap,
                    snap.class_of(l_id).unwrap(),
                    snap.class_of(r_id).unwrap(),
                    result.size,
                );

                let completion_status = match result.completion {
                    crate::au::session::Completion::Exact => "exact",
                    crate::au::session::Completion::BudgetExhausted { .. } => "budget",
                };
                println!(
                    "(anti-unify :size {} :cr {:.4} :completion {}\n  {})",
                    result.size,
                    cr,
                    completion_status,
                    rendered.replace('\n', "\n  ")
                );
            }
            CCommand::CheckAu {
                left,
                right,
                max_size,
                playouts,
                algorithm,
            } => {
                let before = self.eg.node_count();
                let (l_id, _) = self.build_cterm(left);
                let (r_id, _) = self.build_cterm(right);
                if self.eg.node_count() > before {
                    self.eg.rebuild();
                }

                let alg = match algorithm.as_str() {
                    "exact" => crate::au::session::AuAlgorithm::Exact,
                    "uct" => crate::au::session::AuAlgorithm::Uct,
                    other => {
                        return Err(InterpError::CheckFailed(format!(
                            "unknown AU algorithm '{other}' (expected exact or uct)"
                        )));
                    }
                };

                let snap = crate::au::egraph_api::AuSnapshot::new(&self.eg)
                    .map_err(|e| InterpError::CheckFailed(format!("{e}")))?;

                let config = crate::au::session::AuConfig {
                    algorithm: alg,
                    playouts: *playouts,
                    ..Default::default()
                };

                let result = crate::au::session::anti_unify(&snap, l_id, r_id, &config)
                    .map_err(|e| InterpError::CheckFailed(format!("{e}")))?;

                if result.size > *max_size {
                    return Err(InterpError::CheckFailed(format!(
                        "anti-unifier size {} exceeds max_size {}",
                        result.size, max_size
                    )));
                }
            }
            CCommand::Pop => {
                let mark = self.marks.pop().ok_or(InterpError::PopWithoutPush)?;
                self.eg.restore(mark.token);
                self.rules.truncate(mark.rules_len);
                self.globals.truncate(mark.globals_len);
            }
        }
        Ok(())
    }

    /// The numbers `(print-stats)` reports: the graph as it stands now, plus the counters of
    /// the most recent run (zeroed when no run has happened).
    fn stats_snapshot(&self) -> RunStats {
        let sat = self.last_sat.as_ref();
        RunStats {
            nodes: self.eg.len(),
            classes: self.eg.class_count(),
            iterations: sat.map_or(0, |s| s.iterations),
            match_steps: sat.map_or(0, |s| s.match_steps),
            wall_time_ms: self.last_run_time.map_or(0.0, |d| d.as_secs_f64() * 1000.0),
            saturated: sat.is_some_and(|s| s.saturated),
            goal_met: sat.is_some_and(|s| s.goal_met),
        }
    }

    /// Build a `CTerm` in the e-graph. No string lookups, no sort checks.
    fn build_cterm(&mut self, ct: &CTerm<Cfg::O, Cfg::S, L>) -> (Cfg::G, Cfg::S) {
        match ct {
            CTerm::Lit(val, sort) => {
                let lit_op = self.eg.ops().lit_op_for_sort(*sort).unwrap();
                let vid = self.eg.intern_lit(val.clone());
                let id = self.eg.add_lit(lit_op, vid);
                (id, *sort)
            }
            CTerm::App { op, sort, children } => {
                let child_ids: Vec<Cfg::G> =
                    children.iter().map(|c| self.build_cterm(c).0).collect();
                let id = self.eg.add(*op, &child_ids);
                (id, *sort)
            }
            CTerm::Global(name, sort) => {
                let (_, _, id) = self.globals.get(name).expect("global not found at runtime");
                (self.eg.find(id), *sort)
            }
        }
    }
}

/// The `(print-stats)` reading: e-graph size now, and the last run's counters.
///
/// Both renderings are hand-rolled. The text form is for a human reading a terminal; the
/// JSON form is what the comparison harness parses, and it is small and fixed enough that a
/// serialization dependency would buy nothing.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct RunStats {
    pub nodes: usize,
    pub classes: usize,
    pub iterations: usize,
    pub match_steps: u64,
    pub wall_time_ms: f64,
    pub saturated: bool,
    pub goal_met: bool,
}

impl RunStats {
    pub fn render_text(&self) -> String {
        format!(
            "nodes: {}\nclasses: {}\niterations: {}\nmatch-steps: {}\nwall-time-ms: {:.3}\n\
             saturated: {}\ngoal-met: {}\n",
            self.nodes,
            self.classes,
            self.iterations,
            self.match_steps,
            self.wall_time_ms,
            self.saturated,
            self.goal_met,
        )
    }

    pub fn render_json(&self) -> String {
        format!(
            "{{\"nodes\":{},\"classes\":{},\"iterations\":{},\"match_steps\":{},\
             \"wall_time_ms\":{:.3},\"saturated\":{},\"goal_met\":{}}}\n",
            self.nodes,
            self.classes,
            self.iterations,
            self.match_steps,
            self.wall_time_ms,
            self.saturated,
            self.goal_met,
        )
    }
}
