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
    /// A rule applied a partial primitive operation outside its domain while a
    /// `(run …)` or `(check …)` was saturating: division by zero, an overflow
    /// under checked arithmetic, a multiplicity too wide for the configuration.
    ///
    /// Separate from `CompileError` because nothing about the rule is wrong:
    /// it sortchecks, and the operands only exist once it matches. The engine
    /// cannot pick a value on the program's behalf, so the run stops here and
    /// the driver exits nonzero.
    EvalFailed(crate::lit_model::EvalError),
    /// A ground term the configuration cannot build: a written multiplicity too wide for
    /// it, an AC node whose canonical form needs one, or a sequence over the width bound.
    TermError(String),
    /// A count past the configured multiplicity width, met while building or rebuilding:
    /// reported as `multiplicity overflow: …` with the width and its maximum.
    MultOverflow(String),
}

impl From<crate::resolve::ResolveError> for InterpError {
    fn from(e: crate::resolve::ResolveError) -> Self {
        InterpError::CompileError(e)
    }
}

impl From<crate::lit_model::EvalError> for InterpError {
    fn from(e: crate::lit_model::EvalError) -> Self {
        InterpError::EvalFailed(e)
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
            InterpError::EvalFailed(e) => write!(f, "{e}"),
            InterpError::TermError(m) if m.starts_with(crate::multiplicity::OVERFLOW) => {
                write!(f, "{m}")
            }
            InterpError::TermError(m) => write!(f, "term: {m}"),
            InterpError::MultOverflow(m) => write!(f, "{m}"),
        }
    }
}

fn parse_au_cycle_mode(value: &str) -> Result<crate::au::space::CycleMode, InterpError> {
    match value {
        "sides" => Ok(crate::au::space::CycleMode::AncestorOnly),
        "sides-current" => Ok(crate::au::space::CycleMode::CurrentInclusive),
        "pair" => Ok(crate::au::space::CycleMode::Pair),
        other => Err(InterpError::CheckFailed(format!(
            "unknown AU cycle mode '{other}' (expected sides, sides-current, or pair)"
        ))),
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
///   `06-ac-congruence-closure.md` Part I).
/// - `Eager`: every rebuild attempts completion (the `--derive-ac-eqs`
///   behavior). `CompletionOutcome::Converged` reports an unchanged full
///   implementation round, not a semantic-completeness certificate; the growth
///   budget can stop earlier with `AbortedGrowthLimit`. Interleaving
///   completion with saturation rules re-runs it on a growing atom pool every
///   round. A rule set that continually mints new atoms can prevent the
///   combined loop from reaching a fixpoint; the node-growth budget may stop an
///   individual completion rebuild first.
/// - `Lazy`: saturation runs with completion off; an equality check that plain
///   congruence cannot decide runs goal-directed completion inside a
///   semi-persistent transaction shared across consecutive equality checks.
///   The queried pair is the completion goal: every pass stops with
///   `CompletionOutcome::GoalMet` the moment the pair joins, a second phase
///   alternates default-ruleset rule rounds with completion passes when the
///   graph's own closure does not decide the pair, and the node-growth budget
///   is checked inside a round's apply loops. The first non-equality-check
///   command restores the mark, discarding everything the checks derived.
///   Restore work includes container diff replay/capture-state reconstruction
///   and incremental or full hash-index repair. Lazy and eager share the
///   completion implementation, but different stopping points and lazy's
///   bounded rule/completion alternation mean they are not claimed to be
///   equivalent decision procedures.
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
> where
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    pub eg: EGraph<Cfg, L, TRACK, PROOFS>,
    pub model: M,
    /// The rule list `(run)` schedules: ordinary rules and sequence rules, in program
    /// order (`saturate::Rule`).
    rules: Vec<crate::saturate::Rule<Cfg::O, Cfg::S, L>>,
    globals: crate::resolve::GlobalCtx<Cfg::S, Cfg::G>,
    marks: Vec<Mark<Cfg, Cfg::O>>,
    shrink_policy: ShrinkPolicy,
    strategy: crate::saturate::SaturationStrategy,
    ac_mode: AcMode,
    /// Alternation budget for a lazy check's second phase (rule rounds
    /// interleaved with completion fixpoints inside the transaction).
    lazy_ac_rounds: usize,
    /// `--cost-bits`: the width of a cost model's values.
    cost_bits: crate::cost_models::CostBits,
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
    /// Every warning the program raised so far, in order; each is also printed.
    warnings: Vec<String>,
}

impl<Cfg: EGraphConfig, L: LitVal, M: LitModel<Value = L>, const TRACK: bool, const PROOFS: bool>
    Interpreter<Cfg, L, M, TRACK, PROOFS>
where
    Cfg::O: std::hash::Hash,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
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
            cost_bits: Default::default(),
            lazy_txn: None,
            last_sat: None,
            last_run_time: None,
            index_scratch: crate::index::IndexScratch::new(),
            warnings: Vec::new(),
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
            cost_bits: Default::default(),
            lazy_txn: None,
            last_sat: None,
            last_run_time: None,
            index_scratch: crate::index::IndexScratch::new(),
            warnings: Vec::new(),
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

    /// The warnings the program has raised so far, in order.
    pub fn warnings(&self) -> &[String] {
        &self.warnings
    }

    fn warn(&mut self, w: String) {
        eprintln!("warning: {w}");
        self.warnings.push(w);
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

    /// The width of a cost model's values (`--cost-bits`, default `big`, no cap).
    pub fn set_cost_bits(&mut self, bits: crate::cost_models::CostBits) {
        self.cost_bits = bits;
    }

    /// Select the merge survivor policy (see `EGraph::set_union_by`).
    pub fn set_union_by(&mut self, u: crate::egraph::UnionBy) {
        self.eg.set_union_by(u);
    }

    /// Open the shared lazy-check transaction if it is not already open: mark
    /// the graph, then enable completion. Consecutive equality checks keep it
    /// open and accumulate completion/alternation state; the first non-check
    /// command (or the end of the program) closes it via `lazy_txn_close`,
    /// and restore discards everything the checks derived. Restore cost is the
    /// sum of fork-history walks, diff replay, truncation/regrowth, capture-state
    /// reconstruction (including bitmap clearing where applicable), and
    /// incremental or full transient-index repair.
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
    /// no rules interleaving, the case the conditional termination argument
    /// (Dickson antichain over a fixed atom pool) targets — searches for pure AC
    /// congruence consequences. Second, if the pair is still apart and the program has
    /// rules, the saturation driver runs the default ruleset with the pair as
    /// its `:until` goal and completion on, so rounds alternate rule matching
    /// with completion passes, bounded by `lazy_ac_rounds` and by the
    /// node-growth budget (checked in-round, not only between rounds).
    ///
    /// Returns `(equal, inconclusive)`. `inconclusive` means a budget stopped
    /// the search first. A `false` verdict with `inconclusive == false` reached
    /// this driver's operational joint fixpoint without joining the pair. It is
    /// not a semantic non-derivability theorem: matching is over materialized
    /// nodes, and AC scalar-subterm matching remains incomplete.
    fn lazy_ac_decide(&mut self, a: Cfg::G, b: Cfg::G) -> Result<(bool, bool), InterpError> {
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
        // The ordinary rules only: the completion check never ran the sequence rules.
        let ordinary: Vec<&PreparedRule<Cfg::O, Cfg::S, L>> = self
            .rules
            .iter()
            .filter_map(|r| match r {
                crate::saturate::Rule::Ordinary(r) => Some(r),
                crate::saturate::Rule::Sequence(_) => None,
            })
            .collect();
        if !equal && !inconclusive && !ordinary.is_empty() {
            let spec = crate::saturate::RunSpec {
                limit: self.lazy_ac_rounds,
                ruleset: None,
                until: Some(crate::saturate::RunGoal {
                    left: a,
                    right: b,
                    equal: true,
                }),
            };
            // Ordinary rules only, so the fault is an `EvalError`.
            let result = self
                .eg
                .saturate_rules_in(
                    self.strategy,
                    &ordinary,
                    &self.model,
                    &spec,
                    &self.globals,
                    &mut self.index_scratch,
                )
                .map_err(crate::saturate::SatError::into_eval);
            // The completion goal is cleared on the fault path too: it is state
            // on the e-graph, and a caller that reports the error and keeps the
            // interpreter alive must not inherit a goal from a run that ended.
            let result = match result {
                Ok(r) => r,
                Err(e) => {
                    self.eg.set_cc_goal(None);
                    return Err(e.into());
                }
            };
            equal = self.eg.find(a) == self.eg.find(b);
            inconclusive = !equal && (aborted(&self.eg) || !result.saturated);
        }
        self.eg.set_cc_goal(None);
        Ok((equal, inconclusive))
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
    /// The runtime global bindings (`let` names and their classes).
    pub fn globals(&self) -> &crate::resolve::GlobalCtx<Cfg::S, Cfg::G> {
        &self.globals
    }

    pub fn run_checked(&mut self, cmds: &[CCommand<Cfg::O, Cfg::S, L>]) -> Result<(), InterpError> {
        // Each push query already tallies steps in its MatchPool. Arming the
        // thread-local counter folds that tally in once per query; it does not
        // add a flag read to every matching step.
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
            // A rebuild that met a multiplicity past the configured width (a union that
            // makes two children of one AC node sum past it, or completion) left that
            // node as it was: the run reports it and stops.
            if let Some(e) = self.eg.take_width_error() {
                self.lazy_txn_close();
                let _ = e;
                return Err(InterpError::MultOverflow(
                    crate::multiplicity::overflow_message::<Cfg::M>(
                        "a union or completion made two counted children of one AC node sum past the width",
                    ),
                ));
            }
        }
        self.lazy_txn_close();
        Ok(())
    }

    /// `:flatten` acts on n-ary atoms only, so on a rule with none it has no effect (a
    /// `:comm` atom, `RAtom::Comm`, is never flattened, so it does not count). The
    /// rule is still installed: the tag is harmless, and a program that adds an n-ary
    /// atom later should not have to add it back.
    fn warn_flatten_without_effect(&mut self, name: &str, rule: &PreparedRule<Cfg::O, Cfg::S, L>) {
        use crate::resolve::RAtom;
        let nary = rule.query.atoms.iter().any(|a| {
            matches!(
                a,
                RAtom::AExact { .. }
                    | RAtom::APrefix { .. }
                    | RAtom::ASuffix { .. }
                    | RAtom::ABoth { .. }
                    | RAtom::ACExact { .. }
                    | RAtom::ACSub { .. }
                    | RAtom::ACIExact { .. }
                    | RAtom::ACISub { .. }
                    | RAtom::Collect { .. }
            )
        });
        if rule.query.flatten && !nary {
            self.warn(format!(
                "{name}: :flatten has no effect: the rule's pattern has no associative, AC, \
                 or ACI operator"
            ));
        }
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
                "rule `{name}`: multiplicity overflow: the literal {n} exceeds the configured \
                 multiplicity width (EGraphConfig::M holds at most {})",
                <Cfg::M as crate::multiplicity::MultiplicityLike>::MAX
                    .map_or_else(|| "any count".to_string(), |m| m.to_string())
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
                let (id, sort) = self.build_cterm(ct)?;
                self.bind_global(name.clone(), id, sort);
            }
            CCommand::Insert(ct) => {
                self.build_cterm(ct)?;
            }
            CCommand::Union(a, b) => {
                let (a_id, _) = self.build_cterm(a)?;
                let (b_id, _) = self.build_cterm(b)?;
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
                self.build_cterm(ct)?;
            }
            CCommand::CheckEq(a, b) => {
                let (a_id, _) = self.build_cterm(a)?;
                let (b_id, _) = self.build_cterm(b)?;
                // Install the goal before any rebuild: with the shared
                // transaction open, the term-build rebuild runs completion,
                // and the goal keeps it from running past the answer.
                if self.ac_mode == AcMode::Lazy {
                    self.eg.set_cc_goal(Some((a_id, b_id)));
                }
                // A budget-limited run can leave congruence work pending even
                // when both queried terms already hash-cons. Equality commands
                // are closure boundaries, so node growth is not a sufficient
                // reason to decide whether to rebuild.
                self.eg.rebuild();
                if self.eg.find(a_id) != self.eg.find(b_id) {
                    if self.ac_mode == AcMode::Lazy {
                        match self.lazy_ac_decide(a_id, b_id)? {
                            (true, _) => return Ok(()),
                            (false, aborted) => {
                                return Err(InterpError::CheckFailed(if aborted {
                                    "terms are not equal (lazy AC completion hit its growth \
                                     budget before deciding; inconclusive)"
                                        .into()
                                } else {
                                    "equality was not derived at the lazy AC operational \
                                     fixpoint"
                                        .into()
                                }));
                            }
                        }
                    }
                    return Err(InterpError::CheckFailed("terms are not equal".into()));
                }
                self.eg.set_cc_goal(None);
            }
            CCommand::CheckNeq(a, b) => {
                let (a_id, _) = self.build_cterm(a)?;
                let (b_id, _) = self.build_cterm(b)?;
                if self.ac_mode == AcMode::Lazy {
                    self.eg.set_cc_goal(Some((a_id, b_id)));
                }
                self.eg.rebuild();
                if self.eg.find(a_id) == self.eg.find(b_id) {
                    self.eg.set_cc_goal(None);
                    return Err(InterpError::CheckFailed("terms are equal".into()));
                }
                // Lazy mode searches beyond plain congruence before accepting `!=`:
                // distinct classes may still join through completion. Reaching the
                // implemented operational fixpoint without a join is the command's
                // acceptance criterion, not a semantic non-disequality theorem.
                if self.ac_mode == AcMode::Lazy {
                    match self.lazy_ac_decide(a_id, b_id)? {
                        (true, _) => {
                            return Err(InterpError::CheckFailed(
                                "terms are equal (derived by lazy AC completion)".into(),
                            ));
                        }
                        (false, true) => {
                            return Err(InterpError::CheckFailed(
                                "disequality is inconclusive (lazy AC completion hit its \
                                 growth or alternation budget before deciding)"
                                    .into(),
                            ));
                        }
                        (false, false) => {}
                    }
                }
            }
            CCommand::Extract(ct) => {
                let (id, _) = self.build_cterm(ct)?;
                // Extraction must see pending congruence from a preceding
                // budget-limited run even when `ct` was already materialized.
                self.eg.rebuild();
                // An extract that cannot produce a term is a program error, not a printed
                // remark: the class is named and the reason distinguished (every node
                // `:unextractable`, versus no grounded node at all).
                match crate::extract::extract_best(&self.eg, id) {
                    Ok(t) => println!("{t}"),
                    Err(e) => return Err(InterpError::ExtractFailed(e)),
                }
            }
            CCommand::ExtractWith {
                term,
                model,
                rung,
                budget,
                solver,
                file,
                proof,
                band,
            } => {
                let (id, _) = self.build_cterm(term)?;
                self.eg.rebuild();
                crate::cost_models::run(
                    &self.eg,
                    id,
                    model,
                    rung,
                    *budget,
                    solver,
                    file.as_deref(),
                    proof.as_deref(),
                    *band,
                    self.cost_bits,
                )
                .map_err(|e| InterpError::CheckFailed(format!("extract :cost: {e}")))?;
            }
            CCommand::CollectionRule(r) => {
                // Registered like an ordinary rule, so the unions it makes carry
                // `Justification::Rewrite` with its id.
                let mut r = (**r).clone();
                r.rule_id = Some(self.eg.register_rule(&r.name, "", ""));
                for w in &r.seq_rhs.warnings {
                    self.warn(format!("{}: {w}", r.name));
                }
                if std::env::var_os("SEMPER_SEQ_PLAN").is_some() {
                    for line in &r.seq_rhs.plan {
                        eprintln!("plan: {}: {line}", r.name);
                    }
                }
                self.rules
                    .push(crate::saturate::Rule::Sequence(std::sync::Arc::new(r)));
            }
            CCommand::DumpEGraph { root, file } => {
                let (id, _) = self.build_cterm(root)?;
                // The dump has to describe a congruence-closed graph, for the same
                // reason extraction does: a stale parent key would name a class the
                // consumer cannot resolve.
                self.eg.rebuild();
                let (json, _stats) = self.eg.to_egraph_json(id);
                std::fs::write(file, json).map_err(|e| {
                    InterpError::DeclError(format!("dump-egraph :file '{file}': {e}"))
                })?;
            }
            CCommand::Rewrite {
                query,
                rhs_locals,
                rhs,
                root_vid,
                subsume,
                ruleset,
                span,
            } => {
                let name = format!("rewrite_{}", self.eg.rules().len());
                let rule_id = self.eg.register_rule(&name, "", "");
                let compiled_rhs = crate::apply::compile_rhs(rhs);
                let mut actions = vec![crate::apply::CompiledAction::Union(
                    rule_id,
                    crate::apply::RhsOp::FetchNode(crate::resolve::RhsNodeRef::Query(*root_vid)),
                    compiled_rhs,
                )];
                if *subsume {
                    actions.push(crate::apply::CompiledAction::Subsume(*root_vid));
                }
                let rule = PreparedRule {
                    rule_id,
                    query: query.clone(),
                    rhs_locals: *rhs_locals,
                    actions,
                    ruleset: *ruleset,
                    span: *span,
                };
                Self::check_rule_mults(&name, &rule)?;
                self.warn_flatten_without_effect(&name, &rule);
                self.rules.push(crate::saturate::Rule::Ordinary(rule));
            }
            CCommand::Rule {
                query,
                rhs_locals,
                actions,
                ruleset,
                span,
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
                    rhs_locals: *rhs_locals,
                    actions: compiled,
                    ruleset: *ruleset,
                    span: *span,
                };
                Self::check_rule_mults(&name, &rule)?;
                self.warn_flatten_without_effect(&name, &rule);
                self.rules.push(crate::saturate::Rule::Ordinary(rule));
            }
            CCommand::Run {
                ruleset,
                limit,
                until,
            } => {
                // A `:until` goal is built once. New goal nodes are rebuilt
                // before timing starts; the driver rebuilds unconditionally
                // before every goal observation, including when these terms
                // already existed in a dirty graph.
                let goal = match until {
                    None => None,
                    Some(g) => {
                        let before = self.eg.node_count();
                        let (l, _) = self.build_cterm(&g.left)?;
                        let (r, _) = self.build_cterm(&g.right)?;
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
                // A limit beyond `usize` cannot be reached: run to saturation.
                let spec = crate::saturate::RunSpec {
                    limit: usize::try_from(*limit).unwrap_or(usize::MAX),
                    ruleset: *ruleset,
                    until: goal,
                };
                let t0 = std::time::Instant::now();
                // Sequence rules are entries of the rule list: each round applies the
                // ordinary rules, then the sequence rules on the same snapshot (Semper
                // design §7.6), naive or semi-naive with the ordinary rules.
                let result = self.eg.saturate_rules_in(
                    self.strategy,
                    &self.rules,
                    &self.model,
                    &spec,
                    &self.globals,
                    &mut self.index_scratch,
                );
                // The elapsed time is recorded before the fault is propagated:
                // the run did take that long, and `(print-stats)` after a caught
                // error should not read a stale duration from an earlier run.
                self.last_run_time = Some(t0.elapsed());
                let r = result.map_err(|e| match e {
                    crate::saturate::SatError::Eval(e) => InterpError::EvalFailed(e),
                    crate::saturate::SatError::Sequence(m) => InterpError::DeclError(m),
                })?;
                r.sequence.warn();
                let skipped = self.eg.take_no_value();
                if skipped > 0 {
                    self.warn(format!(
                        "{skipped} rule action(s) not applied: the right-hand side was an \
                         application with no children of an operator without :identity, \
                         which has no meaning"
                    ));
                }
                self.last_sat = Some(r);
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
                cycle_mode,
            } => {
                let (l_id, _) = self.build_cterm(left)?;
                let (r_id, _) = self.build_cterm(right)?;
                self.eg.rebuild();

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
                    cycle_mode: parse_au_cycle_mode(cycle_mode)?,
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
                cycle_mode,
            } => {
                let (l_id, _) = self.build_cterm(left)?;
                let (r_id, _) = self.build_cterm(right)?;
                self.eg.rebuild();

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
                    cycle_mode: parse_au_cycle_mode(cycle_mode)?,
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
                // SMT-LIB pop: back to the checkpoint, then drop its scope —
                // fused, so it costs one pop core per column (design doc 08 §1;
                // the verified `restore` alone keeps the scope open).
                self.eg.restore_and_pop(mark.token);
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

    /// Build a `CTerm` in the e-graph. Apps need no name lookup or sort check;
    /// `CTerm::Global` intentionally retains and looks up its source name.
    ///
    /// `Err` is a ground term the configuration cannot build
    /// ([`EGraph::add_with_counts`](crate::egraph::EGraph::add_with_counts)).
    fn build_cterm(
        &mut self,
        ct: &CTerm<Cfg::O, Cfg::S, L>,
    ) -> Result<(Cfg::G, Cfg::S), InterpError> {
        Ok(match ct {
            CTerm::Lit(val, sort) => {
                let lit_op = self.eg.ops().lit_op_for_sort(*sort).unwrap();
                let vid = self.eg.intern_lit(val.clone());
                let id = self.eg.add_lit(lit_op, vid);
                (id, *sort)
            }
            CTerm::App { op, sort, children } => {
                // Associativity on the term as *written*, before the child ids exist.
                //
                // For an A-only operator, `(F (F a b) c)` and `(F a b c)` are the same term,
                // and this is the only place that fact is visible: here `children` is the
                // syntax tree, so a nested same-op argument is a nested *application*.
                // `EGraph::add` cannot make this decision, because by then a child is a
                // `Cfg::G` and a nested application is indistinguishable from a class id that
                // merely happens to be a `Seq` node — an RHS rest binding hands `add` exactly
                // such ids, and splicing those rewrites uphill (`seq(a,b)` to
                // `seq(unit,a,b)` and again every round, `a_singleton_collapse.egg`).
                //
                // The class-level test in `flatten_seq_children` still runs after this and is
                // still needed: it flattens a child that came back from `add` already
                // flattenable. What this adds is order independence for the written nesting,
                // which that test cannot give — a class stops being a *pure* sequence as soon
                // as anything is unioned into it, so `(union (F a b) blob)` before
                // `(F (F a b) c)` used to store the nested spelling and never rejoin
                // `(F a b c)`, while the two statements the other way round flattened it.
                //
                // A `Global` argument is deliberately not spliced: a name is opaque here, and
                // resolving it would read the graph again, which is what this avoids.
                let dir = match self.eg.ops().info(*op).kind {
                    crate::registry::OpKind::A { dir, .. } => Some(dir),
                    _ => None,
                };
                // Each child with its count: `x:k` is one counted child of an AC
                // application, the class once under ACI, and `k` positions otherwise.
                let mut kids: Vec<(Cfg::G, Option<&num_bigint::BigUint>)> =
                    Vec::with_capacity(children.len());
                match dir {
                    None => {
                        for c in children {
                            kids.push(self.build_counted(c)?);
                        }
                    }
                    Some(dir) => self.push_seq_args(children, *op, dir, &mut kids)?,
                }
                let id = self
                    .eg
                    .add_with_counts(*op, &kids)
                    .map_err(InterpError::TermError)?;
                (id, *sort)
            }
            CTerm::Counted(t, _) => self.build_cterm(t)?,
            CTerm::Global(name, sort) => {
                let (_, _, id) = self.globals.get(name).expect("global not found at runtime");
                (self.eg.find(id), *sort)
            }
        })
    }

    /// A child and its count: `x:k` written, or `None` for 1.
    fn build_counted<'c>(
        &mut self,
        c: &'c CTerm<Cfg::O, Cfg::S, L>,
    ) -> Result<(Cfg::G, Option<&'c num_bigint::BigUint>), InterpError> {
        Ok(match c {
            CTerm::Counted(t, k) => (self.build_cterm(t)?.0, Some(k)),
            _ => (self.build_cterm(c)?.0, None),
        })
    }

    /// Build the argument list of an A-only application, splicing a nested same-`op`
    /// application on the declared spine instead of building it as one child.
    ///
    /// Recursive, so `(F (F (F a b) c) d)` yields `[a, b, c, d)]` in one pass. See the note in
    /// [`build_cterm`](Self::build_cterm) for why this belongs here and not in `EGraph::add`.
    fn push_seq_args<'c>(
        &mut self,
        children: &'c [CTerm<Cfg::O, Cfg::S, L>],
        op: Cfg::O,
        dir: crate::registry::AssocDir,
        out: &mut Vec<(Cfg::G, Option<&'c num_bigint::BigUint>)>,
    ) -> Result<(), InterpError> {
        use crate::registry::AssocDir;
        let last = children.len().saturating_sub(1);
        for (i, c) in children.iter().enumerate() {
            // Off the declared spine a nested application is explicit grouping that the
            // operator does not flatten: for a left fold `a - (b - c)` is not `a - b - c`.
            let on_spine = match dir {
                AssocDir::Both => true,
                AssocDir::Left => i == 0,
                AssocDir::Right => i == last,
            };
            match c {
                CTerm::App {
                    op: inner_op,
                    children: inner,
                    ..
                } if on_spine && *inner_op == op => self.push_seq_args(inner, op, dir, out)?,
                _ => out.push(self.build_counted(c)?),
            }
        }
        Ok(())
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
