// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Layer 7: Command language interpreter.
//!
//! Parses and executes egglog programs against the e-graph.

use crate::apply::PreparedRule;
use crate::canon::{ACCanon, VarCanon};
use crate::config::EGraphConfig;
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
}

impl<Cfg: EGraphConfig, L: LitVal, M: LitModel<Value = L>, const TRACK: bool, const PROOFS: bool>
    Interpreter<Cfg, L, M, TRACK, PROOFS>
where
    Cfg::O: std::hash::Hash,
    ACCanon: VarCanon<Cfg::G, Cfg::C>,
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
        }
    }

    /// Set the shrink policy used by `push`/`pop`.
    pub fn set_shrink_policy(&mut self, policy: ShrinkPolicy) {
        self.shrink_policy = policy;
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
        for cmd in cmds {
            self.exec_checked(cmd)?;
        }
        Ok(())
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
                let (a_id, _) = self.build_cterm(a);
                let (b_id, _) = self.build_cterm(b);
                if self.eg.find(a_id) != self.eg.find(b_id) {
                    return Err(InterpError::CheckFailed("terms are not equal".into()));
                }
            }
            CCommand::CheckNeq(a, b) => {
                let (a_id, _) = self.build_cterm(a);
                let (b_id, _) = self.build_cterm(b);
                if self.eg.find(a_id) == self.eg.find(b_id) {
                    return Err(InterpError::CheckFailed("terms are equal".into()));
                }
            }
            CCommand::Extract(ct) => {
                let (id, _) = self.build_cterm(ct);
                match crate::extract::extract_best(&self.eg, id) {
                    Some(t) => println!("{t}"),
                    None => println!("(extract: no term found)"),
                }
            }
            CCommand::Rewrite {
                query,
                rhs,
                root_vid,
                subsume,
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
                self.rules.push(PreparedRule {
                    rule_id,
                    query: query.clone(),
                    actions,
                });
            }
            CCommand::Rule { query, actions } => {
                let name = format!("rule_{}", self.eg.rules().len());
                let rule_id = self.eg.register_rule(&name, "", "");
                let compiled: Vec<_> = actions
                    .iter()
                    .map(|a| crate::apply::compile_action(a, rule_id))
                    .collect();
                self.rules.push(PreparedRule {
                    rule_id,
                    query: query.clone(),
                    actions: compiled,
                });
            }
            CCommand::Run(n) => {
                self.eg
                    .saturate(&self.rules, &self.model, *n as usize, &self.globals);
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
            CCommand::Pop => {
                let mark = self.marks.pop().ok_or(InterpError::PopWithoutPush)?;
                self.eg.restore(mark.token);
                self.rules.truncate(mark.rules_len);
                self.globals.truncate(mark.globals_len);
            }
        }
        Ok(())
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
