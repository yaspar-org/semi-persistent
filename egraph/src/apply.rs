// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Compiled RHS terms and apply function.
//!
//! All variable references use the typed dense ids from LHS resolve
//! for O(1) lookup into Match / MatchSet. The apply function walks
//! the compiled RHS tree bottom-up, building e-graph terms via `eg.add()`.

use crate::ast::{
    GlobalVarId, LitValVarId, MsetVarId, RhsLocalMultVarId, RhsLocalVarId, SeqVarId, SetVarId,
};
use crate::containers::DenseId;
use crate::resolve::{RRhsChild, RRhsTerm, RhsMultRef, RhsNodeRef};

// ---------------------------------------------------------------------------
// Compiled RHS types
// ---------------------------------------------------------------------------

/// Instruction that produces one `Cfg::G` when evaluated against a Match.
#[derive(Clone, Debug)]
pub enum RhsOp<O, V> {
    /// Fetch bound e-node id from match.
    FetchNode(RhsNodeRef),
    /// Create literal node via `eg.add_lit()`.
    Lit(O, V),
    /// Reconstruct `@sort(val)` lit node from a bound LitValVarId.
    LitVar(O, LitValVarId),
    /// Reconstruct an `@i64(k)` lit node from a bound AC multiplicity variable.
    MultVar(O, RhsMultRef),
    /// Build `(op args...)` via `eg.add()`. Args may expand to multiple children.
    App { op: O, args: Vec<RhsArg<O, V>> },
    /// Evaluate a prim op on bound lit values or multiplicities, intern result.
    PrimApp {
        op: O,
        args: Vec<crate::resolve::RPrimArg>,
    },
    /// Fetch a global e-class id from the runtime global bindings.
    FetchGlobal(GlobalVarId),
}

/// An argument to `App` — produces one or many children.
#[derive(Clone, Debug)]
pub enum RhsArg<O, V> {
    /// Single child.
    One(RhsOp<O, V>),
    /// One child contributed `mult` times (variadic ops only). Multiplicity 0
    /// omits the child without evaluating it, so nothing is materialized.
    OneMult {
        body: Box<RhsOp<O, V>>,
        mult: crate::resolve::ResolvedMultExpr,
    },
    /// Splice sequence rest into children.
    SpliceSeq(SeqVarId),
    /// Splice set rest into children.
    SpliceSet(SetVarId),
    /// Splice multiset rest into children (each element repeated by its multiplicity).
    SpliceMset(MsetVarId),
    /// Set comprehension: map body over set rest.
    SetComp {
        body: Box<RhsOp<O, V>>,
        var: RhsLocalVarId,
        source: SetVarId,
        filter: Option<Box<RhsOp<O, V>>>,
    },
    /// Multiset comprehension: map body over mset rest, with output multiplicity.
    MsetComp {
        body: Box<RhsOp<O, V>>,
        mult: crate::resolve::ResolvedMultExpr,
        var: RhsLocalVarId,
        mult_var: RhsLocalMultVarId,
        source: MsetVarId,
        filter: Option<Box<RhsOp<O, V>>>,
    },
    /// Sequence comprehension: map body over seq rest.
    SeqComp {
        body: Box<RhsOp<O, V>>,
        var: RhsLocalVarId,
        source: SeqVarId,
        filter: Option<Box<RhsOp<O, V>>>,
    },
}

// ---------------------------------------------------------------------------
// Compile: RRhsTerm → RhsOp (all IDs already resolved)
// ---------------------------------------------------------------------------

pub fn compile_rhs<O: Clone, S, V: Clone>(term: &RRhsTerm<O, S, V>) -> RhsOp<O, V> {
    match term {
        RRhsTerm::Var(vid) => RhsOp::FetchNode(*vid),
        RRhsTerm::Lit { op, value, .. } => RhsOp::Lit(op.clone(), value.clone()),
        RRhsTerm::LitVar { op, val } => RhsOp::LitVar(op.clone(), *val),
        RRhsTerm::MultVar { op, var } => RhsOp::MultVar(op.clone(), *var),
        RRhsTerm::App { op, children } => {
            let args: Vec<RhsArg<O, V>> = children.iter().map(|c| compile_rhs_arg(c)).collect();
            RhsOp::App {
                op: op.clone(),
                args,
            }
        }
        RRhsTerm::PrimApp { op, args, .. } => RhsOp::PrimApp {
            op: op.clone(),
            args: args.clone(),
        },
        RRhsTerm::FetchGlobal(gid) => RhsOp::FetchGlobal(*gid),
    }
}

fn compile_rhs_arg<O: Clone, S, V: Clone>(child: &RRhsChild<O, S, V>) -> RhsArg<O, V> {
    match child {
        RRhsChild::Term(t) => RhsArg::One(compile_rhs(t)),
        RRhsChild::TermMult { body, mult } => RhsArg::OneMult {
            body: Box::new(compile_rhs(body)),
            mult: mult.clone(),
        },
        RRhsChild::SpliceSeq(id) => RhsArg::SpliceSeq(*id),
        RRhsChild::SpliceSet(id) => RhsArg::SpliceSet(*id),
        RRhsChild::SpliceMset(id) => RhsArg::SpliceMset(*id),
        RRhsChild::SetComp {
            body,
            var,
            source,
            filter,
        } => RhsArg::SetComp {
            body: Box::new(compile_rhs(body)),
            var: *var,
            source: *source,
            filter: filter.as_ref().map(|f| Box::new(compile_rhs(f))),
        },
        RRhsChild::MsetComp {
            body,
            mult,
            var,
            mult_var,
            source,
            filter,
        } => RhsArg::MsetComp {
            body: Box::new(compile_rhs(body)),
            mult: mult.clone(),
            var: *var,
            mult_var: *mult_var,
            source: *source,
            filter: filter.as_ref().map(|f| Box::new(compile_rhs(f))),
        },
        RRhsChild::SeqComp {
            body,
            var,
            source,
            filter,
        } => RhsArg::SeqComp {
            body: Box::new(compile_rhs(body)),
            var: *var,
            source: *source,
            filter: filter.as_ref().map(|f| Box::new(compile_rhs(f))),
        },
    }
}

// ---------------------------------------------------------------------------
// Compiled actions and rules
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub enum CompiledAction<O, V> {
    Union(crate::id::RuleId, RhsOp<O, V>, RhsOp<O, V>),
    Insert(RhsOp<O, V>),
    Set {
        func: O,
        args: Vec<RhsOp<O, V>>,
        value: RhsOp<O, V>,
    },
    Subsume(crate::ast::VarId),
}

/// Identifier of a declared ruleset: its index in the program's declaration order. `None`
/// wherever a `RulesetId` is optional means the default ruleset — the one an untagged rule
/// joins and a bare `(run N)` runs.
pub type RulesetId = u32;

#[derive(Clone, Debug)]
pub struct PreparedRule<O, S, V> {
    pub rule_id: crate::id::RuleId,
    pub query: crate::resolve::ResolvedQuery<O, S, V>,
    pub rhs_locals: crate::resolve::RhsLocalShape,
    pub actions: Vec<CompiledAction<O, V>>,
    /// The ruleset this rule belongs to (`:ruleset name`), or `None` for the default one.
    /// The saturation driver runs the rules whose ruleset equals the one asked for.
    pub ruleset: Option<RulesetId>,
}

// ---------------------------------------------------------------------------
// Install-time multiplicity-width validation
// ---------------------------------------------------------------------------

/// Reject a rule whose surface multiplicity literals do not fit the configured
/// [`EGraphConfig::M`], naming the offending value.
///
/// Multiplicity literals are parsed and resolved at the `u64` surface width, which is
/// independent of the width a given config stores. The two use sites cannot both fail
/// gracefully at match/apply time:
///
/// * on the **RHS** (`MsetComp`'s output multiplicity), `n` says how many copies of the
///   body to emit; there is no error channel inside `apply`, and emitting fewer copies
///   than asked would silently change what the rule means.
/// * on the **LHS** (`RMult::Exact` and a `RMult::Var` bound), a literal above the
///   stored width can never equal a stored multiplicity, so the pattern is dead — sound,
///   but silently so, which is exactly the failure that hides a mis-sized config.
///
/// Checking once at install turns both into one diagnosable error, and is what licenses
/// the `expect` at the RHS narrowing site.
pub fn check_mult_literals<Cfg: crate::config::EGraphConfig, O, S, V>(
    rule: &PreparedRule<O, S, V>,
) -> Result<(), u64> {
    for atom in &rule.query.atoms {
        let elems: &[(crate::resolve::PatVar, crate::resolve::RMult)] = match atom {
            crate::resolve::RAtom::ACExact { elems, .. }
            | crate::resolve::RAtom::ACSub { elems, .. } => elems,
            _ => continue,
        };
        for (_, m) in elems {
            match m {
                crate::resolve::RMult::Exact(n) => check_one::<Cfg>(*n)?,
                crate::resolve::RMult::Var {
                    constraint: Some((_, n)),
                    ..
                } => check_one::<Cfg>(*n)?,
                crate::resolve::RMult::Var { .. } => {}
            }
        }
    }
    for (_, lo, hi) in &rule.query.mult_intervals {
        check_one::<Cfg>(*lo)?;
        // An open upper bound is `u64::MAX`, not a literal the rule spelled out; only a
        // bound the author actually wrote can be too wide for the configuration.
        if *hi != u64::MAX {
            check_one::<Cfg>(*hi)?;
        }
    }
    for action in &rule.actions {
        match action {
            CompiledAction::Union(_, a, b) => {
                check_op_mults::<Cfg, _, _>(a)?;
                check_op_mults::<Cfg, _, _>(b)?;
            }
            CompiledAction::Insert(t) => check_op_mults::<Cfg, _, _>(t)?,
            CompiledAction::Set { args, value, .. } => {
                for a in args {
                    check_op_mults::<Cfg, _, _>(a)?;
                }
                check_op_mults::<Cfg, _, _>(value)?;
            }
            CompiledAction::Subsume(_) => {}
        }
    }
    Ok(())
}

#[inline]
fn check_one<Cfg: crate::config::EGraphConfig>(n: u64) -> Result<(), u64> {
    match <Cfg::M as MultiplicityLike>::try_from_u64(n) {
        Some(_) => Ok(()),
        None => Err(n),
    }
}

fn check_op_mults<Cfg: crate::config::EGraphConfig, O, V>(op: &RhsOp<O, V>) -> Result<(), u64> {
    let args = match op {
        RhsOp::App { args, .. } => args,
        _ => return Ok(()),
    };
    for arg in args {
        match arg {
            RhsArg::One(inner) => check_op_mults::<Cfg, _, _>(inner)?,
            RhsArg::OneMult { body, mult } => {
                // A literal count above the stored width can never be
                // represented; multiplicity 0 is legal here (omission).
                if let crate::resolve::ResolvedMultExpr::Lit(n) = mult
                    && *n > 0
                {
                    check_one::<Cfg>(*n)?;
                }
                check_op_mults::<Cfg, _, _>(body)?;
            }
            RhsArg::MsetComp {
                body, mult, filter, ..
            } => {
                if let crate::resolve::ResolvedMultExpr::Lit(n) = mult {
                    check_one::<Cfg>(*n)?;
                }
                check_op_mults::<Cfg, _, _>(body)?;
                if let Some(f) = filter {
                    check_op_mults::<Cfg, _, _>(f)?;
                }
            }
            RhsArg::SetComp { body, filter, .. } | RhsArg::SeqComp { body, filter, .. } => {
                check_op_mults::<Cfg, _, _>(body)?;
                if let Some(f) = filter {
                    check_op_mults::<Cfg, _, _>(f)?;
                }
            }
            RhsArg::SpliceSeq(_) | RhsArg::SpliceSet(_) | RhsArg::SpliceMset(_) => {}
        }
    }
    Ok(())
}

pub fn compile_action<O: Clone, S, V: Clone>(
    action: &crate::resolve::ResolvedAction<O, S, V>,
    rule_id: crate::id::RuleId,
) -> CompiledAction<O, V> {
    use crate::resolve::ResolvedAction;
    match action {
        ResolvedAction::Union(a, b) => {
            CompiledAction::Union(rule_id, compile_rhs(a), compile_rhs(b))
        }
        ResolvedAction::Insert(t) => CompiledAction::Insert(compile_rhs(t)),
        ResolvedAction::Set { func, args, value } => CompiledAction::Set {
            func: func.clone(),
            args: args.iter().map(|a| compile_rhs(a)).collect(),
            value: compile_rhs(value),
        },
    }
}

/// Compile a `(rewrite LHS RHS :when [guards...])` into a `PreparedRule`.
pub fn compile_rewrite<O, S, L, M, const TRACK: bool>(
    name: &str,
    lhs_src: &str,
    rhs_src: &str,
    lhs: &crate::surface_ast::SurfacePattern,
    rhs: &crate::ast::RhsTerm,
    when: &[crate::surface_ast::SurfacePattern],
    subsume: bool,
    ops: &crate::registry::OpRegistry<O, S, TRACK>,
    sorts: &crate::registry::SortRegistry<S, TRACK>,
    rules: &mut crate::registry::RuleRegistry<TRACK>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, impl Copy>,
) -> Result<PreparedRule<O, S, L>, crate::resolve::ResolveError>
where
    O: crate::DenseId + std::hash::Hash + Copy,
    S: crate::DenseId + Copy,
    L: crate::literal::LitVal,
    M: crate::lit_model::LitModel<Value = L>,
{
    let rule_id = rules.register(name, lhs_src, rhs_src);
    let mut body = vec![lhs.clone()];
    body.extend_from_slice(when);
    let fq = crate::sortcheck::flatten_surface(&body, ops).map_err(|e| {
        crate::resolve::ResolveError {
            msg: e,
            span: crate::ast::Span::Dummy,
            extra_spans: Vec::new(),
        }
    })?;
    let root_name = &fq.root_vars[0];
    let rq = crate::resolve::resolve(&fq, ops, sorts, model, globals)?;

    let root_vid = rq
        .shape
        .find_var(root_name)
        .expect("root var must be in shape");
    let root_sort = rq.var_sorts[root_vid.idx()];
    let mut rhs_ctx = crate::resolve::RhsResolveCtx::new(&rq.shape, &rq.var_sorts);
    let resolved_rhs =
        crate::resolve::resolve_rhs(rhs, root_sort, ops, sorts, model, &mut rhs_ctx, globals)?;
    let compiled_rhs = compile_rhs(&resolved_rhs);
    let rhs_locals = rhs_ctx.local_shape();

    let mut actions = vec![CompiledAction::Union(
        rule_id,
        RhsOp::FetchNode(RhsNodeRef::Query(root_vid)),
        compiled_rhs,
    )];
    if subsume {
        actions.push(CompiledAction::Subsume(root_vid));
    }

    Ok(PreparedRule {
        rule_id,
        query: rq,
        rhs_locals,
        actions,
        ruleset: None,
    })
}

/// Compile a `(rule (body...) (head...))` into a `PreparedRule`.
pub fn compile_rule<O, S, L, M, const TRACK: bool>(
    name: &str,
    body: &[crate::surface_ast::SurfacePattern],
    head: &[crate::ast::Action],
    ops: &crate::registry::OpRegistry<O, S, TRACK>,
    sorts: &crate::registry::SortRegistry<S, TRACK>,
    rules: &mut crate::registry::RuleRegistry<TRACK>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, impl Copy>,
) -> Result<PreparedRule<O, S, L>, crate::resolve::ResolveError>
where
    O: crate::DenseId + std::hash::Hash + Copy,
    S: crate::DenseId + Copy,
    L: crate::literal::LitVal,
    M: crate::lit_model::LitModel<Value = L>,
{
    let rule_id = rules.register(name, "", "");
    let fq =
        crate::sortcheck::flatten_surface(body, ops).map_err(|e| crate::resolve::ResolveError {
            msg: e,
            span: crate::ast::Span::Dummy,
            extra_spans: Vec::new(),
        })?;
    let rq = crate::resolve::resolve(&fq, ops, sorts, model, globals)?;

    let mut rhs_ctx = crate::resolve::RhsResolveCtx::new(&rq.shape, &rq.var_sorts);
    let mut actions = Vec::with_capacity(head.len());
    for a in head {
        let ra = crate::resolve::resolve_action(a, ops, sorts, model, &mut rhs_ctx, globals)?;
        actions.push(compile_action(&ra, rule_id));
    }
    let rhs_locals = rhs_ctx.local_shape();

    Ok(PreparedRule {
        rule_id,
        query: rq,
        rhs_locals,
        actions,
        ruleset: None,
    })
}

// ---------------------------------------------------------------------------
// Eval: execute compiled RHS against a Match and e-graph
// ---------------------------------------------------------------------------

use crate::EGraphConfig;
use crate::canon::{MSetCanon, VarCanon};
use crate::egraph::EGraph;
use crate::ematch::{MatchPool, run_query_scheduled_into};
use crate::index::IndexStore;
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;
use smallvec::SmallVec;

/// Inline capacity for a node's child list during RHS instantiation.
///
/// 16 rather than the 4 of `leapfrog::CursorVec`, because the two lists have
/// different length distributions. A cursor vector holds one entry per query
/// atom; a child list holds one per *child*, and a variadic RHS that splices a
/// rest variable (`(add (mul y x) ..r)`) produces as many children as the
/// matched node had. The capacity 16 is a historical AC-workload tuning choice;
/// it is not a portable knee. Beyond the inline capacity the list spills to the
/// heap and stays correct. Retuning requires the Criterion rule-application
/// workload and its allocation counters.
type ChildVec<Cfg> = SmallVec<[<Cfg as EGraphConfig>::G; 16]>;

/// Inline capacity for a primitive application's argument list. Primitives here
/// are arithmetic and comparison, so two covers all of them.
const PRIM_ARGS: usize = 2;

/// Evaluation environment for one matched query row.
///
/// The query match is read-only. Comprehension binders use separate local
/// arrays indexed by the RHS-only IDs allocated during resolution.
pub(crate) struct RhsEnv<'a, Cfg: EGraphConfig, Q: ?Sized> {
    query: &'a Q,
    local_nodes: Vec<Option<Cfg::G>>,
    local_mults: Vec<Option<Cfg::M>>,
}

impl<'a, Cfg, Q> RhsEnv<'a, Cfg, Q>
where
    Cfg: EGraphConfig,
    Q: crate::ematch::MatchView<Cfg> + ?Sized,
{
    fn new(query: &'a Q, shape: crate::resolve::RhsLocalShape) -> Self {
        Self {
            query,
            local_nodes: vec![None; shape.node_count],
            local_mults: vec![None; shape.mult_count],
        }
    }

    fn node(&self, node: RhsNodeRef) -> Cfg::G {
        match node {
            RhsNodeRef::Query(id) => self.query.get(id),
            RhsNodeRef::Local(id) => self.local_nodes[id.idx()]
                .expect("RHS invariant violated: unbound local node reference"),
        }
    }

    fn mult(&self, mult: RhsMultRef) -> Cfg::M {
        match mult {
            RhsMultRef::Query(id) => self.query.get_mult(id),
            RhsMultRef::Local(id) => self.local_mults[id.idx()]
                .expect("RHS invariant violated: unbound local multiplicity reference"),
        }
    }

    fn bind_local_node(&mut self, id: RhsLocalVarId, value: Cfg::G) -> Option<Cfg::G> {
        self.local_nodes[id.idx()].replace(value)
    }

    fn restore_local_node(&mut self, id: RhsLocalVarId, previous: Option<Cfg::G>) {
        self.local_nodes[id.idx()] = previous;
    }

    fn bind_local_mult(&mut self, id: RhsLocalMultVarId, value: Cfg::M) -> Option<Cfg::M> {
        self.local_mults[id.idx()].replace(value)
    }

    fn restore_local_mult(&mut self, id: RhsLocalMultVarId, previous: Option<Cfg::M>) {
        self.local_mults[id.idx()] = previous;
    }

    fn locals_are_unbound(&self) -> bool {
        self.local_nodes.iter().all(Option::is_none) && self.local_mults.iter().all(Option::is_none)
    }
}

/// A bound AC multiplicity read as an i64 literal value. Resolution only admits
/// multiplicity variables in i64 positions, so the model must carry an i64
/// sort; a count above `i64::MAX` cannot arise from a real node's children.
fn mult_as_lit<L: LitVal, M: crate::lit_model::LitModel<Value = L>>(model: &M, k: u64) -> L {
    let desc = model
        .sorts()
        .iter()
        .find(|s| s.name == "i64")
        .expect("multiplicity in RHS: model has no i64 sort");
    (desc.parse)(&k.to_string()).expect("multiplicity in RHS does not fit i64")
}

fn eval<Cfg, L, M, Q, S: Copy, const T: bool, const P: bool>(
    op: &RhsOp<Cfg::O, L>,
    env: &mut RhsEnv<'_, Cfg, Q>,
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> Cfg::G
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    Q: crate::ematch::MatchView<Cfg> + ?Sized,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    match op {
        RhsOp::FetchNode(node) => eg.find(env.node(*node)),
        RhsOp::FetchGlobal(gid) => eg.find(globals.binding(*gid)),
        RhsOp::Lit(op, val) => {
            let id = eg.lits_mut().intern(val.clone());
            eg.add_lit(*op, id)
        }
        RhsOp::LitVar(op, lvid) => {
            let val_id = env.query.get_lit_val(*lvid);
            eg.add_lit(*op, val_id)
        }
        RhsOp::MultVar(op, mid) => {
            let val = mult_as_lit(model, env.mult(*mid).to_u64());
            let id = eg.lits_mut().intern(val);
            eg.add_lit(*op, id)
        }
        RhsOp::App { op: o, args } => {
            let mut children = ChildVec::<Cfg>::new();
            for arg in args {
                eval_arg(arg, env, eg, model, globals, &mut children);
            }
            eg.add(*o, &children)
        }
        RhsOp::PrimApp { op, args } => {
            // Gather bound lit values (or multiplicities as i64) from the match
            let raw_vals: SmallVec<[L; PRIM_ARGS]> = args
                .iter()
                .map(|arg| match arg {
                    crate::resolve::RPrimArg::LitVal(vid) => {
                        let lit_val_id = env.query.get_lit_val(*vid);
                        eg.lits().get(lit_val_id).clone()
                    }
                    crate::resolve::RPrimArg::Mult(mid) => {
                        mult_as_lit(model, env.mult(*mid).to_u64())
                    }
                })
                .collect();
            let refs: SmallVec<[&L; PRIM_ARGS]> = raw_vals.iter().collect();
            let prim = &model.ops()[op.to_usize()];
            let result = (prim.eval)(&refs);
            let result_id = eg.lits_mut().intern(result);
            // Find the @-prefixed lit op for the return sort
            let lit_op = eg
                .ops()
                .lit_op_for_sort(eg.ops().info(*op).return_sort)
                .expect("no lit op for prim op return sort");
            eg.add_lit(lit_op, result_id)
        }
    }
}

fn eval_arg<Cfg, L, M, Q, S: Copy, const T: bool, const P: bool>(
    arg: &RhsArg<Cfg::O, L>,
    env: &mut RhsEnv<'_, Cfg, Q>,
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    out: &mut ChildVec<Cfg>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    Q: crate::ematch::MatchView<Cfg> + ?Sized,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    match arg {
        // A bound node used directly as a child needs no canonicalization here:
        // `out` is `EGraph::add`'s child slice and `add` canonicalizes every
        // child itself — which is also why the splice arms below hand it raw
        // match bindings. Going through `eval` would `find` each child twice.
        RhsArg::One(RhsOp::FetchNode(node)) => out.push(env.node(*node)),
        RhsArg::One(RhsOp::FetchGlobal(gid)) => out.push(globals.binding(*gid)),
        RhsArg::One(inner) => out.push(eval(inner, env, eg, model, globals)),
        RhsArg::OneMult { body, mult } => {
            // Multiplicity 0 omits the child without evaluating it, so an
            // omitted term is never materialized (the k-1 = 0 case of a
            // multiplicity variant). Underflow and division by zero were rejected
            // at install by the interval check; the checked ops here are the
            // second line, like the checked literal primitives.
            let k = eval_mult_expr::<Cfg, Q>(mult, env);
            if k > 0 {
                let id = eval(body, env, eg, model, globals);
                for _ in 0..k {
                    out.push(id);
                }
            }
        }
        RhsArg::SpliceSeq(sid) => out.extend_from_slice(env.query.seq_slice(*sid)),
        RhsArg::SpliceSet(sid) => out.extend_from_slice(env.query.set_slice(*sid)),
        RhsArg::SpliceMset(mid) => {
            for c in env.query.mset_slice(*mid) {
                let id = Cfg::mset_child_id(c);
                let mult = Cfg::mset_child_mult(c);
                // A repetition count, not a stored multiplicity: widening to
                // `usize` is lossless for every supported width.
                for _ in 0..mult.to_usize() {
                    out.push(id);
                }
            }
        }
        RhsArg::SeqComp {
            body,
            var,
            source,
            filter,
        } => {
            let source = env.query.seq_slice(*source).to_vec();
            for child in source {
                let previous = env.bind_local_node(*var, child);
                let passes = filter.as_ref().is_none_or(|filter| {
                    let value = eval(filter, env, eg, model, globals);
                    check_filter_truthy(eg, model, value)
                });
                if passes {
                    out.push(eval(body, env, eg, model, globals));
                }
                env.restore_local_node(*var, previous);
            }
        }
        RhsArg::SetComp {
            body,
            var,
            source,
            filter,
        } => {
            let source = env.query.set_slice(*source).to_vec();
            for child in source {
                let previous = env.bind_local_node(*var, child);
                let passes = filter.as_ref().is_none_or(|filter| {
                    let value = eval(filter, env, eg, model, globals);
                    check_filter_truthy(eg, model, value)
                });
                if passes {
                    out.push(eval(body, env, eg, model, globals));
                }
                env.restore_local_node(*var, previous);
            }
        }
        RhsArg::MsetComp {
            body,
            mult: out_mult,
            var,
            mult_var,
            source,
            filter,
        } => {
            let source = env.query.mset_slice(*source).to_vec();
            for child in source {
                let previous_node = env.bind_local_node(*var, Cfg::mset_child_id(&child));
                let previous_mult = env.bind_local_mult(*mult_var, Cfg::mset_child_mult(&child));
                let passes = filter.as_ref().is_none_or(|filter| {
                    let value = eval(filter, env, eg, model, globals);
                    check_filter_truthy(eg, model, value)
                });
                if passes {
                    let count = eval_mult_expr::<Cfg, Q>(out_mult, env);
                    if count != 0 {
                        let result = eval(body, env, eg, model, globals);
                        // Install-time checks guarantee that every emitted
                        // multiplicity fits the configured storage width.
                        let count = Cfg::M::try_from_u64(count)
                            .expect("RHS multiplicity exceeds the configured width");
                        for _ in 0..count.to_usize() {
                            out.push(result);
                        }
                    }
                }
                env.restore_local_mult(*mult_var, previous_mult);
                env.restore_local_node(*var, previous_node);
            }
        }
    }
}

/// Evaluate an RHS multiplicity expression over the match's bound
/// multiplicities, in checked u64 arithmetic. Underflow and division by zero
/// are rejected statically at rule install ([`check_rhs_mult_exprs`]); the
/// checked ops here are the second line, and panic like the checked literal
/// primitives do.
fn eval_mult_expr<Cfg, Q>(e: &crate::resolve::ResolvedMultExpr, env: &RhsEnv<'_, Cfg, Q>) -> u64
where
    Cfg: EGraphConfig,
    Q: crate::ematch::MatchView<Cfg> + ?Sized,
{
    use crate::resolve::{MultPrimOp as P, ResolvedMultExpr as E};
    match e {
        E::Lit(n) => *n,
        E::Var(v) => env.mult(*v).to_u64(),
        E::Prim { op, args } => {
            let a = eval_mult_expr::<Cfg, Q>(&args[0], env);
            let b = eval_mult_expr::<Cfg, Q>(&args[1], env);
            match op {
                P::Add => a
                    .checked_add(b)
                    .expect("u64::+ overflow in RHS multiplicity"),
                P::Sub => a
                    .checked_sub(b)
                    .expect("u64::- underflow in RHS multiplicity"),
                P::Mul => a
                    .checked_mul(b)
                    .expect("u64::* overflow in RHS multiplicity"),
                P::Div => a
                    .checked_div(b)
                    .expect("u64::/ by zero in RHS multiplicity"),
                P::Rem => a
                    .checked_rem(b)
                    .expect("u64::% by zero in RHS multiplicity"),
                P::Min => a.min(b),
                P::Max => a.max(b),
            }
        }
    }
}

/// Interval bounds of an RHS multiplicity expression, from the rule's LHS
/// multiplicity constraints (`ResolvedQuery::mult_intervals`; an unannotated
/// `x:k` is `[1, u64::MAX]`). Errors on the two expressions that could be
/// *wrong* at runtime rather than merely large: a subtraction that cannot be
/// proved non-negative, and a division or remainder whose divisor could be
/// zero. Additions and products saturate in the bound computation; a runtime
/// overflow still traps in [`eval_mult_expr`].
fn mult_expr_bounds(
    e: &crate::resolve::ResolvedMultExpr,
    intervals: &[(crate::ast::MultVarId, u64, u64)],
) -> Result<(u64, u64), String> {
    use crate::resolve::{MultPrimOp as P, ResolvedMultExpr as E};
    Ok(match e {
        E::Lit(n) => (*n, *n),
        E::Var(RhsMultRef::Query(v)) => intervals
            .iter()
            .find(|(id, _, _)| id == v)
            .map(|(_, lo, hi)| (*lo, *hi))
            .unwrap_or((1, u64::MAX)),
        E::Var(RhsMultRef::Local(_)) => (1, u64::MAX),
        E::Prim { op, args } => {
            let (lo_a, hi_a) = mult_expr_bounds(&args[0], intervals)?;
            let (lo_b, hi_b) = mult_expr_bounds(&args[1], intervals)?;
            match op {
                P::Add => (lo_a.saturating_add(lo_b), hi_a.saturating_add(hi_b)),
                P::Sub => {
                    if lo_a < hi_b {
                        return Err(format!(
                            "u64::- can underflow: the left side is at least {lo_a} but \
                             the right side can reach {hi_b}; constrain the multiplicity \
                             on the LHS (e.g. `x:k>=2`) so the subtraction cannot go \
                             negative"
                        ));
                    }
                    (lo_a - hi_b, hi_a.saturating_sub(lo_b))
                }
                P::Mul => (lo_a.saturating_mul(lo_b), hi_a.saturating_mul(hi_b)),
                P::Div | P::Rem => {
                    if lo_b == 0 {
                        return Err(format!(
                            "{} divisor can be zero; constrain it on the LHS",
                            op.name()
                        ));
                    }
                    match op {
                        P::Div => (lo_a / hi_b.max(1), hi_a / lo_b),
                        _ => (0, hi_b - 1),
                    }
                }
                P::Min => (lo_a.min(lo_b), hi_a.min(hi_b)),
                P::Max => (lo_a.max(lo_b), hi_a.max(hi_b)),
            }
        }
    })
}

/// Static safety check for every RHS multiplicity expression in a rule's
/// actions, against the rule's LHS multiplicity intervals. Rejection here is
/// what licenses the `expect`s in `eval_mult_expr` for underflow and
/// division by zero; overflow stays a runtime trap because any expression
/// over an unbounded `k` could overflow and rejecting them all would ban
/// `k+1`.
pub fn check_rhs_mult_exprs<O, S, V>(rule: &PreparedRule<O, S, V>) -> Result<(), String> {
    fn walk_op<O, V>(
        op: &RhsOp<O, V>,
        intervals: &[(crate::ast::MultVarId, u64, u64)],
    ) -> Result<(), String> {
        let RhsOp::App { args, .. } = op else {
            return Ok(());
        };
        for arg in args {
            match arg {
                RhsArg::One(inner) => walk_op(inner, intervals)?,
                RhsArg::OneMult { body, mult } => {
                    mult_expr_bounds(mult, intervals)?;
                    walk_op(body, intervals)?;
                }
                RhsArg::MsetComp {
                    body, mult, filter, ..
                } => {
                    mult_expr_bounds(mult, intervals)?;
                    walk_op(body, intervals)?;
                    if let Some(f) = filter {
                        walk_op(f, intervals)?;
                    }
                }
                RhsArg::SetComp { body, filter, .. } | RhsArg::SeqComp { body, filter, .. } => {
                    walk_op(body, intervals)?;
                    if let Some(f) = filter {
                        walk_op(f, intervals)?;
                    }
                }
                RhsArg::SpliceSeq(_) | RhsArg::SpliceSet(_) | RhsArg::SpliceMset(_) => {}
            }
        }
        Ok(())
    }
    let iv = &rule.query.mult_intervals;
    for action in &rule.actions {
        match action {
            CompiledAction::Union(_, a, b) => {
                walk_op(a, iv)?;
                walk_op(b, iv)?;
            }
            CompiledAction::Insert(t) => walk_op(t, iv)?,
            CompiledAction::Set { args, value, .. } => {
                for a in args {
                    walk_op(a, iv)?;
                }
                walk_op(value, iv)?;
            }
            CompiledAction::Subsume(_) => {}
        }
    }
    Ok(())
}

fn check_filter_truthy<Cfg, L, M, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
    _model: &M,
    id: Cfg::G,
) -> bool
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let value = eg
        .get_lit_val(id)
        .expect("RHS invariant violated: comprehension filter did not evaluate to a literal node");
    M::is_truthy(value)
}

fn apply_action<Cfg, L, M, Q, S: Copy, const T: bool, const P: bool>(
    action: &CompiledAction<Cfg::O, L>,
    env: &mut RhsEnv<'_, Cfg, Q>,
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> usize
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    Q: crate::ematch::MatchView<Cfg> + ?Sized,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    match action {
        CompiledAction::Union(rule_id, a, b) => {
            let va = eval(a, env, eg, model, globals);
            let vb = eval(b, env, eg, model, globals);
            if eg.find(va) != eg.find(vb) {
                if P {
                    eg.merge_justified(
                        va,
                        vb,
                        crate::union_find::Justification::Rewrite { rule_id: *rule_id },
                    );
                } else {
                    eg.merge(va, vb);
                }
                1
            } else {
                0
            }
        }
        CompiledAction::Insert(t) => {
            eval(t, env, eg, model, globals);
            1
        }
        CompiledAction::Set {
            func: _,
            args: _,
            value: _,
        } => {
            todo!("lattice set not yet implemented")
        }
        CompiledAction::Subsume(var) => {
            let node = env.node(RhsNodeRef::Query(*var));
            eg.subsume(node);
            1
        }
    }
}

pub(crate) fn apply_rule_actions<Cfg, L, M, Q, S, const T: bool, const P: bool>(
    rule: &PreparedRule<Cfg::O, S, L>,
    query: &Q,
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> usize
where
    Cfg: EGraphConfig,
    S: Copy,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    Q: crate::ematch::MatchView<Cfg> + ?Sized,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut env = RhsEnv::new(query, rule.rhs_locals);
    let changes = rule
        .actions
        .iter()
        .map(|action| apply_action(action, &mut env, eg, model, globals))
        .sum();
    debug_assert!(
        env.locals_are_unbound(),
        "RHS comprehension locals must not escape action evaluation"
    );
    changes
}

pub fn apply_rule<Cfg, L, M, S, const T: bool, const P: bool>(
    rule: &PreparedRule<Cfg::O, S, L>,
    eg: &mut EGraph<Cfg, L, T, P>,
    index: &IndexStore<Cfg>,
    stats: &crate::schedule::IndexStats<Cfg::O>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> usize
where
    Cfg: EGraphConfig,
    S: crate::DenseId,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    crate::canon::MSetCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
{
    apply_rule_pooled(
        rule,
        eg,
        index,
        stats,
        model,
        globals,
        &mut MatchPool::new(),
    )
}

/// [`apply_rule`] with a caller-owned match buffer.
///
/// The naive driver calls this with one pool for the whole saturation, so the
/// per-match allocations happen in the first round and are recycled thereafter.
/// See [`MatchPool`].
pub fn apply_rule_pooled<Cfg, L, M, S, const T: bool, const P: bool>(
    rule: &PreparedRule<Cfg::O, S, L>,
    eg: &mut EGraph<Cfg, L, T, P>,
    index: &IndexStore<Cfg>,
    stats: &crate::schedule::IndexStats<Cfg::O>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
) -> usize
where
    Cfg: EGraphConfig,
    S: crate::DenseId,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    crate::canon::MSetCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
{
    let vindex = crate::index::VariantIndex::naive(index);
    let sampler = crate::index::IndexSampler::new(eg, vindex);
    let plan = crate::schedule::schedule_with_stats_sampled(&rule.query, stats, &sampler);
    run_query_scheduled_into(&rule.query, &plan, eg, &vindex, globals, pool);
    let mut changes = 0;
    for j in 0..pool.len() {
        let row = pool.row(j);
        changes += apply_rule_actions(rule, &row, eg, model, globals);
    }
    changes
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::id::{OpId, SortId};
    use crate::lit_model::LitModel;
    use crate::literal::{LitValStore, NiraLitVal, NiraModel};
    use crate::nodes::LitValId;
    use crate::registry::{AssocDir, OpRegistry, SortRegistry};
    use crate::resolve::{RhsResolveCtx, resolve, resolve_rhs};
    use crate::sortcheck::flatten_surface as flatten;
    use crate::test_helpers::{parse_pattern, parse_rhs};

    fn setup() -> (
        OpRegistry<OpId, SortId, false>,
        SortRegistry<SortId, false>,
        LitValStore<NiraLitVal, LitValId, false>,
    ) {
        let model = NiraModel;
        let mut sorts: SortRegistry<SortId, false> = SortRegistry::new();
        let sort_names: Vec<&str> = model.sorts().iter().map(|s| s.name).collect();
        sorts.register_builtins(&sort_names);
        let e = sorts.intern("IExpr");
        let ibig = sorts.id_by_name("IBig").unwrap();
        let mut ops = OpRegistry::new();
        ops.register_builtins(&model, &sorts);
        ops.register("f", &[e, e], e);
        ops.register("g", &[e], e);
        ops.register("a", &[], e);
        ops.register("b", &[], e);
        ops.register("c", &[], e);
        ops.register_a("concat", e, e, AssocDir::Right);
        ops.register_mset("add", e, e);
        ops.register_set("union", e, e);
        ops.register("ILit", &[ibig], e);
        (
            ops,
            sorts,
            LitValStore::<NiraLitVal, LitValId, false>::new(),
        )
    }

    #[test]
    fn rhs_local_multiplicity_interval_is_positive() {
        use crate::resolve::{MultPrimOp, ResolvedMultExpr};

        let local = ResolvedMultExpr::Var(RhsMultRef::Local(RhsLocalMultVarId::new(0)));
        assert_eq!(mult_expr_bounds(&local, &[]), Ok((1, u64::MAX)));

        let decrement = ResolvedMultExpr::Prim {
            op: MultPrimOp::Sub,
            args: vec![local.clone(), ResolvedMultExpr::Lit(1)],
        };
        assert_eq!(mult_expr_bounds(&decrement, &[]), Ok((0, u64::MAX - 1)));

        let unsafe_subtraction = ResolvedMultExpr::Prim {
            op: MultPrimOp::Sub,
            args: vec![ResolvedMultExpr::Lit(1), local.clone()],
        };
        assert!(mult_expr_bounds(&unsafe_subtraction, &[]).is_err());

        let safe_division = ResolvedMultExpr::Prim {
            op: MultPrimOp::Div,
            args: vec![ResolvedMultExpr::Lit(10), local],
        };
        assert!(mult_expr_bounds(&safe_division, &[]).is_ok());
    }

    #[test]
    fn general_rule_uses_one_local_allocator_across_actions() {
        let eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let body = vec![parse_pattern("(add chosen:1 ..rest)")];
        let source = parse_rhs("(add chosen ..rest)");
        let first = parse_rhs("(add ..{(g elem):count for elem:count in rest})");
        let second = parse_rhs("(add ..{elem:count for elem:count in rest})");
        let head = vec![
            crate::ast::Action::Union(source.clone(), first),
            crate::ast::Action::Union(source, second),
        ];
        let rule = compile_rule(
            "two-actions",
            &body,
            &head,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &NiraModel,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();
        assert_eq!(
            rule.rhs_locals,
            crate::resolve::RhsLocalShape {
                node_count: 2,
                mult_count: 2,
            }
        );
    }

    fn lhs_root_sort(
        rq: &crate::resolve::ResolvedQuery<OpId, SortId, NiraLitVal>,
        fq: &crate::compile::FlatQuery,
    ) -> Option<SortId> {
        let root_vid = rq.shape.find_var(&fq.root_vars[0]).unwrap();
        rq.var_sorts[root_vid.idx()]
    }

    fn do_compile(lhs: &str, rhs_src: &str) -> RhsOp<OpId, NiraLitVal> {
        let (ops, sorts, _) = setup();
        let model = NiraModel;
        let pat = parse_pattern(lhs);
        let fq = flatten(&[pat], &ops).unwrap();
        let rq = resolve(
            &fq,
            &ops,
            &sorts,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();
        let root_sort = lhs_root_sort(&rq, &fq);
        let ri = rhs_src;
        let rhs_ast = parse_rhs(ri);
        let mut ctx = RhsResolveCtx::new(&rq.shape, &rq.var_sorts);
        let rhs = resolve_rhs(
            &rhs_ast,
            root_sort,
            &ops,
            &sorts,
            &model,
            &mut ctx,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();
        compile_rhs(&rhs)
    }

    #[test]
    fn compile_var_is_varid() {
        let (ops, sorts, _) = setup();
        let model = NiraModel;
        let pat = parse_pattern("(f x y)");
        let fq = flatten(&[pat], &ops).unwrap();
        let rq = resolve(
            &fq,
            &ops,
            &sorts,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();
        let root_sort = lhs_root_sort(&rq, &fq);
        let ri = "x";
        let rhs_ast = parse_rhs(ri);
        let mut ctx = RhsResolveCtx::new(&rq.shape, &rq.var_sorts);
        let rhs = resolve_rhs(
            &rhs_ast,
            root_sort,
            &ops,
            &sorts,
            &model,
            &mut ctx,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();
        let c = compile_rhs(&rhs);
        // The compiled term should reference the same VarId the parser assigned to "x"
        let x_vid = rq.shape.find_var("x").unwrap();
        assert!(matches!(c, RhsOp::FetchNode(RhsNodeRef::Query(v)) if v == x_vid));
    }

    #[test]
    fn compile_lit() {
        // (ILit 42) in IExpr context
        let c = do_compile("(f x y)", "(ILit 42)");
        assert!(matches!(c, RhsOp::App { .. }));
    }

    #[test]
    fn compile_app_preserves_varids() {
        let (ops, sorts, _) = setup();
        let model = NiraModel;
        let pat = parse_pattern("(f x y)");
        let fq = flatten(&[pat], &ops).unwrap();
        let rq = resolve(
            &fq,
            &ops,
            &sorts,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();
        let root_sort = lhs_root_sort(&rq, &fq);
        let ri = "(f y x)";
        let rhs_ast = parse_rhs(ri);
        let mut ctx = RhsResolveCtx::new(&rq.shape, &rq.var_sorts);
        let rhs = resolve_rhs(
            &rhs_ast,
            root_sort,
            &ops,
            &sorts,
            &model,
            &mut ctx,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();
        let c = compile_rhs(&rhs);

        let x_vid = rq.shape.find_var("x").unwrap();
        let y_vid = rq.shape.find_var("y").unwrap();
        match c {
            RhsOp::App { args: children, .. } => {
                // (f y x) — first child is y, second is x
                assert!(matches!(
                    &children[0],
                    RhsArg::One(RhsOp::FetchNode(RhsNodeRef::Query(v))) if *v == y_vid
                ));
                assert!(matches!(
                    &children[1],
                    RhsArg::One(RhsOp::FetchNode(RhsNodeRef::Query(v))) if *v == x_vid
                ));
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn compile_splice_seq_typed() {
        let c = do_compile("(concat ..pre x ..suf)", "(concat ..pre x ..suf)");
        match c {
            RhsOp::App { args: children, .. } => {
                assert!(matches!(&children[0], RhsArg::SpliceSeq(SeqVarId(0))));
                assert!(matches!(&children[1], RhsArg::One(RhsOp::FetchNode(_))));
                assert!(matches!(&children[2], RhsArg::SpliceSeq(SeqVarId(1))));
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn compile_splice_mset_typed() {
        let c = do_compile("(add x:1 ..rest)", "(add x ..rest)");
        match c {
            RhsOp::App { args: children, .. } => {
                assert!(matches!(&children[0], RhsArg::One(RhsOp::FetchNode(_))));
                assert!(matches!(&children[1], RhsArg::SpliceMset(MsetVarId(0))));
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn compile_splice_set_typed() {
        let c = do_compile("(union x ..rest)", "(union x ..rest)");
        match c {
            RhsOp::App { args: children, .. } => {
                assert!(matches!(&children[0], RhsArg::One(RhsOp::FetchNode(_))));
                assert!(matches!(&children[1], RhsArg::SpliceSet(SetVarId(0))));
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn compile_nested_app() {
        let c = do_compile("(f x y)", "(f (g x) y)");
        match c {
            RhsOp::App { args: children, .. } => {
                assert_eq!(children.len(), 2);
                assert!(matches!(&children[0], RhsArg::One(RhsOp::App { .. })));
                assert!(matches!(&children[1], RhsArg::One(RhsOp::FetchNode(_))));
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn debug_render_full_pipeline() {
        let model = NiraModel;
        let mut sorts: SortRegistry<SortId, false> = SortRegistry::new();
        let sort_names: Vec<&str> = model.sorts().iter().map(|s| s.name).collect();
        sorts.register_builtins(&sort_names);
        let e = sorts.intern("IExpr");
        let mut ops = OpRegistry::new();
        ops.register_builtins(&model, &sorts);
        let ibig = sorts.id_by_name("IBig").unwrap();
        ops.register("f", &[e, e], e);
        ops.register("g", &[e], e);
        ops.register("h", &[e, e, e], e);
        ops.register("inv", &[e], e);
        ops.register("a", &[], e);
        ops.register("b", &[], e);
        ops.register_a("concat", e, e, AssocDir::Right);
        ops.register_mset("add", e, e);
        ops.register_mset("mul", e, e);
        ops.register_set("union", e, e);
        ops.register("ILit", &[ibig], e);
        let model = NiraModel;

        let cases: &[(&str, &str, &str)] = &[
            // 1. Plain rewrite: commutativity
            ("commute f", "(f x y)", "(f y x)"),
            // 2. Nested plain: distribute g into f
            ("nested", "(f x (g y))", "(g (f y x))"),
            // 3. AC subset + splice: factor out of add
            ("AC factor", "(add x:1 y:1 ..rest)", "(add (f x y) ..rest)"),
            // 4. ACI subset + splice: de Morgan style (union → add)
            (
                "ACI de Morgan",
                "(inv (union x ..rest))",
                "(add (inv x) ..rest)",
            ),
            // 5. A sliding window + splice: swap adjacent in sequence
            (
                "A swap adjacent",
                "(concat ..pre x y ..suf)",
                "(concat ..pre y x ..suf)",
            ),
            // 6. A prefix + splice
            ("A rotate last", "(concat ..pre x)", "(concat x ..pre)"),
            // 7. AC exact: normalize binary add
            ("AC exact", "(add x:1 y:1)", "(f x y)"),
            // 8. ACI two vars + splice
            (
                "ACI two + rest",
                "(union x y ..rest)",
                "(union (f x y) ..rest)",
            ),
            // 9. Literal in RHS
            ("literal rhs", "(f x y)", "(ILit 42)"),
            // 10. Nullary in RHS
            ("nullary rhs", "(f x y)", "(a)"),
        ];

        for &(label, lhs_src, rhs_src) in cases {
            println!("\n{}", "=".repeat(60));
            println!("  Rule: {label}");
            println!("  LHS:  {lhs_src}");
            println!("  RHS:  {rhs_src}");

            let pat = parse_pattern(lhs_src);
            let fq = flatten(&[pat], &ops).unwrap();

            println!("\n  -- Flatten ({} atoms) --", fq.atoms.len(),);
            for (i, a) in fq.atoms.iter().enumerate() {
                println!("     atom[{i}]: {a:?}");
            }

            let rq = resolve(
                &fq,
                &ops,
                &sorts,
                &model,
                &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
            )
            .unwrap();

            println!("\n  -- Resolve LHS --");
            for (name, id) in rq.shape.vars() {
                println!("     {id:?} \"{name}\"");
            }
            for (i, a) in rq.atoms.iter().enumerate() {
                println!("     ratom[{i}]: {a:?}");
            }

            println!("\n  -- MatchShape --");
            if !rq.shape.nodes.is_empty() {
                println!("     nodes: {:?}", rq.shape.nodes);
            }
            if !rq.shape.mults.is_empty() {
                println!("     mults: {:?}", rq.shape.mults);
            }
            if !rq.shape.seqs.is_empty() {
                println!("     seqs:  {:?}", rq.shape.seqs);
            }
            if !rq.shape.sets.is_empty() {
                println!("     sets:  {:?}", rq.shape.sets);
            }
            if !rq.shape.msets.is_empty() {
                println!("     msets: {:?}", rq.shape.msets);
            }

            let root_sort = lhs_root_sort(&rq, &fq);
            let ri = rhs_src;
            let rhs_ast = parse_rhs(ri);
            let mut ctx = RhsResolveCtx::new(&rq.shape, &rq.var_sorts);
            let rhs = resolve_rhs(
                &rhs_ast,
                root_sort,
                &ops,
                &sorts,
                &model,
                &mut ctx,
                &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
            )
            .unwrap();

            println!("\n  -- Resolved RHS --");
            print_rhs("     ", &rhs);

            let crhs = compile_rhs(&rhs);
            println!("\n  -- Compiled RHS --");
            print_compiled("     ", &crhs);
        }
    }

    fn print_rhs(indent: &str, t: &crate::resolve::RRhsTerm<OpId, SortId, NiraLitVal>) {
        use crate::resolve::{RRhsChild as RC, RRhsTerm as R};
        match t {
            R::Var(v) => println!("{indent}Var({v:?})"),
            R::Lit { sort, value, .. } => println!("{indent}Lit(sort={sort:?}, val={value:?})"),
            R::App { op, children } => {
                println!("{indent}App(op={op:?})");
                for (i, c) in children.iter().enumerate() {
                    match c {
                        RC::Term(t) => {
                            println!("{indent}  child[{i}]:");
                            print_rhs(&format!("{indent}    "), t);
                        }
                        RC::TermMult { body, mult } => {
                            println!("{indent}  child[{i}] (mult {mult:?}):");
                            print_rhs(&format!("{indent}    "), body);
                        }
                        RC::SpliceSeq(id) => println!("{indent}  child[{i}]: SpliceSeq({:?})", id),
                        RC::SpliceSet(id) => println!("{indent}  child[{i}]: SpliceSet({:?})", id),
                        RC::SpliceMset(id) => {
                            println!("{indent}  child[{i}]: SpliceMset({:?})", id)
                        }
                        RC::SetComp { var, source, .. } => println!(
                            "{indent}  child[{i}]: SetComp(var={}, src={:?})",
                            var.idx(),
                            source
                        ),
                        RC::MsetComp { var, source, .. } => println!(
                            "{indent}  child[{i}]: MsetComp(var={}, src={:?})",
                            var.idx(),
                            source
                        ),
                        RC::SeqComp { var, source, .. } => println!(
                            "{indent}  child[{i}]: SeqComp(var={}, src={:?})",
                            var.idx(),
                            source
                        ),
                    }
                }
            }
            R::PrimApp { op, args, .. } => {
                println!("{indent}PrimApp(op={op:?}, args={args:?})");
            }
            R::MultVar { op, var } => {
                println!("{indent}MultVar(op={op:?}, var={var:?})");
            }
            R::LitVar { op, val } => {
                println!("{indent}LitVar(op={op:?}, val={val:?})");
            }
            R::FetchGlobal(gid) => {
                println!("{indent}FetchGlobal({gid:?})");
            }
        }
    }

    fn print_compiled(indent: &str, op: &RhsOp<OpId, NiraLitVal>) {
        match op {
            RhsOp::FetchNode(v) => println!("{indent}FetchNode({v:?})"),
            RhsOp::Lit(op, id) => println!("{indent}Lit({op:?}, {id:?})"),
            RhsOp::App { op: o, args } => {
                println!("{indent}App(op={o:?})");
                for (i, a) in args.iter().enumerate() {
                    match a {
                        RhsArg::One(inner) => {
                            println!("{indent}  arg[{i}]:");
                            print_compiled(&format!("{indent}    "), inner);
                        }
                        RhsArg::OneMult { body, mult } => {
                            println!("{indent}  arg[{i}] (mult {mult:?}):");
                            print_compiled(&format!("{indent}    "), body);
                        }
                        RhsArg::SpliceSeq(s) => {
                            println!("{indent}  arg[{i}]: SpliceSeq(SeqVarId({}))", s.idx())
                        }
                        RhsArg::SpliceSet(s) => {
                            println!("{indent}  arg[{i}]: SpliceSet(SetVarId({}))", s.idx())
                        }
                        RhsArg::SpliceMset(s) => {
                            println!("{indent}  arg[{i}]: SpliceMset(MsetVarId({}))", s.idx())
                        }
                        RhsArg::SetComp { var, source, .. } => println!(
                            "{indent}  arg[{i}]: SetComp(var=VarId({}), src=SetVarId({}))",
                            var.idx(),
                            source.idx()
                        ),
                        RhsArg::MsetComp { var, source, .. } => println!(
                            "{indent}  arg[{i}]: MsetComp(var=VarId({}), src=MsetVarId({}))",
                            var.idx(),
                            source.idx()
                        ),
                        RhsArg::SeqComp { var, source, .. } => println!(
                            "{indent}  arg[{i}]: SeqComp(var=VarId({}), src=SeqVarId({}))",
                            var.idx(),
                            source.idx()
                        ),
                    }
                }
            }
            RhsOp::PrimApp { op, args } => {
                println!("{indent}PrimApp(op={op:?}, args={args:?})");
            }
            RhsOp::LitVar(op, lvid) => {
                println!("{indent}LitVar(op={op:?}, val={lvid:?})");
            }
            RhsOp::MultVar(op, mid) => {
                println!("{indent}MultVar(op={op:?}, var={mid:?})");
            }
            RhsOp::FetchGlobal(gid) => {
                println!("{indent}FetchGlobal({gid:?})");
            }
        }
    }

    // ===================================================================
    // End-to-end: compile_rewrite + apply_rule
    // ===================================================================

    use crate::egraph::EGraph;
    use crate::index::IndexStore;
    use crate::nodes::DefaultConfig;

    type EG = EGraph<DefaultConfig, NiraLitVal, false, false>;

    fn make_eg() -> EG {
        let mut eg = EG::from_model(&NiraModel);
        let e = eg.intern_sort("IExpr");
        eg.register_op2("f", e, e, e);
        eg.register_op1("g", e, e);
        eg.register_op2("h", e, e, e);
        eg.register_op0("a", e);
        eg.register_op0("b", e);
        eg.register_op0("c", e);
        eg.register_a("concat", e, e, AssocDir::Right);
        eg.register_mset("add", e, e);
        eg.register_set("union", e, e);
        eg
    }

    fn make_eg_with_lits() -> EG {
        let mut eg = EG::from_model(&NiraModel);
        let e = eg.intern_sort("IExpr");
        let ibig = eg.sorts().id_by_name("IBig").unwrap();
        eg.register_opn("ILit", &[ibig], e);
        eg.register_op2("IAdd", e, e, e);
        eg
    }

    #[test]
    fn rewrite_commute_f() {
        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);

        // Compile: (f x y) → (f y x)
        let model = NiraModel;
        let lhs = parse_pattern("(f x y)");
        let ri = "(f y x)";
        let rhs = parse_rhs(ri);
        let rule = compile_rewrite(
            "test",
            "",
            "",
            &lhs,
            &rhs,
            &[],
            false,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();

        // Before: only (f a b) exists
        let index = IndexStore::build(&eg);
        let changes = apply_rule(
            &rule,
            &mut eg,
            &index,
            &crate::schedule::IndexStats::from_index(&index),
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );
        assert!(changes > 0, "expected at least one change");

        // After: (f b a) should exist and be merged with (f a b)
        let fba = eg.add(eg.ops().id_by_name("f").unwrap(), &[b, a]);
        assert_eq!(
            eg.find(fab),
            eg.find(fba),
            "(f a b) and (f b a) should be in same e-class"
        );
    }

    #[test]
    fn rewrite_nested() {
        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let gb = eg.add(eg.ops().id_by_name("g").unwrap(), &[b]);
        let _fagb = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, gb]);

        // Compile: (f x (g y)) → (g (f y x))
        let model = NiraModel;
        let lhs = parse_pattern("(f x (g y))");
        let ri = "(g (f y x))";
        let rhs = parse_rhs(ri);
        let rule = compile_rewrite(
            "test",
            "",
            "",
            &lhs,
            &rhs,
            &[],
            false,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();

        let index = IndexStore::build(&eg);
        let changes = apply_rule(
            &rule,
            &mut eg,
            &index,
            &crate::schedule::IndexStats::from_index(&index),
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );
        assert!(changes > 0);

        // (g (f b a)) should now exist and be merged with (f a (g b))
        let fba = eg.add(eg.ops().id_by_name("f").unwrap(), &[b, a]);
        let g_fba = eg.add(eg.ops().id_by_name("g").unwrap(), &[fba]);
        assert_eq!(eg.find(_fagb), eg.find(g_fba));
    }

    #[test]
    fn rewrite_no_match_no_change() {
        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let _ga = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);

        // Compile: (f x y) → (f y x) — but no f-nodes exist
        let model = NiraModel;
        let lhs = parse_pattern("(f x y)");
        let ri = "(f y x)";
        let rhs = parse_rhs(ri);
        let rule = compile_rewrite(
            "test",
            "",
            "",
            &lhs,
            &rhs,
            &[],
            false,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();

        let index = IndexStore::build(&eg);
        let changes = apply_rule(
            &rule,
            &mut eg,
            &index,
            &crate::schedule::IndexStats::from_index(&index),
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );
        assert_eq!(changes, 0);
    }

    #[test]
    fn rewrite_insert_new_op() {
        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);

        // Compile: (f x y) → (h x y) — creates h-nodes
        let model = NiraModel;
        let lhs = parse_pattern("(f x y)");
        let ri = "(h x y)";
        let rhs = parse_rhs(ri);
        let rule = compile_rewrite(
            "test",
            "",
            "",
            &lhs,
            &rhs,
            &[],
            false,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();

        let index = IndexStore::build(&eg);
        let changes = apply_rule(
            &rule,
            &mut eg,
            &index,
            &crate::schedule::IndexStats::from_index(&index),
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );
        assert!(changes > 0);

        // (h a b) should exist and be in same e-class as (f a b)
        let hab = eg.add(eg.ops().id_by_name("h").unwrap(), &[a, b]);
        assert_eq!(eg.find(_fab), eg.find(hab));
    }

    #[test]
    fn zero_output_multiplicity_does_not_evaluate_the_body() {
        let mut eg = EG::from_model(&NiraModel);
        let e = eg.intern_sort("IExpr");
        let marker_op = eg.register_op0("marker", e);
        let a_op = eg.register_op0("a", e);
        let b_op = eg.register_op0("b", e);
        let count_f = eg.register_op1("CountF", e, e);
        let count_bag = eg.register_mset("CountBag", e, e);

        let marker = eg.add(marker_op, &[]);
        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        eg.add(count_bag, &[marker, a, b, b, b]);

        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let lhs = parse_pattern("(CountBag (marker):1 ..rest)");
        let rhs = parse_rhs("(CountBag ..{(CountF elem):(u64::- count 1) for elem:count in rest})");
        let model = NiraModel;
        let globals = crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new();
        let rule = compile_rewrite(
            "zero-output",
            "",
            "",
            &lhs,
            &rhs,
            &[],
            false,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &model,
            &globals,
        )
        .unwrap();

        let index = IndexStore::build(&eg);
        assert!(
            apply_rule(
                &rule,
                &mut eg,
                &index,
                &crate::schedule::IndexStats::from_index(&index),
                &model,
                &globals,
            ) > 0
        );
        assert_eq!(
            eg.op_node_counts()[count_f.to_usize()],
            1,
            "CountF(a) must not be materialized when a's output count is zero"
        );
    }

    // -----------------------------------------------------------------------
    // Datalog insert
    // -----------------------------------------------------------------------

    #[test]
    fn rule_datalog_insert() {
        // rule: (f x y) => insert (h x y)
        // Given (f a b), should create (h a b) as a new e-class (no union).
        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);

        let model = NiraModel;
        let body = vec![parse_pattern("(f x y)")];
        let ri = "(h x y)";
        let rhs_term = parse_rhs(ri);
        let head = vec![crate::ast::Action::Insert(rhs_term)];
        let rule = compile_rule(
            "test",
            &body,
            &head,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();

        let index = IndexStore::build(&eg);
        let changes = apply_rule(
            &rule,
            &mut eg,
            &index,
            &crate::schedule::IndexStats::from_index(&index),
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );
        assert_eq!(changes, 1);

        // (h a b) should exist but NOT be merged with (f a b)
        let hab = eg.add(eg.ops().id_by_name("h").unwrap(), &[a, b]);
        assert_ne!(
            eg.find(fab),
            eg.find(hab),
            "insert should not union with the matched node"
        );
    }

    // -----------------------------------------------------------------------
    // Rest splicing
    // -----------------------------------------------------------------------

    #[test]
    fn rewrite_a_splice_rest() {
        // concat is A (associative). Match prefix, splice rest.
        // (concat x ..rest) → (concat x x ..rest)
        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let c = eg.add(eg.ops().id_by_name("c").unwrap(), &[]);
        let abc = eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, b, c]);

        let model = NiraModel;
        let lhs = parse_pattern("(concat x ..rest)");
        let ri = "(concat x x ..rest)";
        let rhs = parse_rhs(ri);
        let rule = compile_rewrite(
            "test",
            "",
            "",
            &lhs,
            &rhs,
            &[],
            false,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();

        let index = IndexStore::build(&eg);
        let changes = apply_rule(
            &rule,
            &mut eg,
            &index,
            &crate::schedule::IndexStats::from_index(&index),
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );
        assert!(changes > 0);

        // (concat a a b c) should be merged with (concat a b c)
        let aabc = eg.add(eg.ops().id_by_name("concat").unwrap(), &[a, a, b, c]);
        assert_eq!(eg.find(abc), eg.find(aabc));
    }

    #[test]
    fn rewrite_ac_splice_rest() {
        // add is AC. Match one element, splice rest.
        // {add x ..rest} → {add (g x) ..rest}
        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let ab = eg.add(eg.ops().id_by_name("add").unwrap(), &[a, b]);

        let model = NiraModel;
        let lhs = parse_pattern("(add x:1 ..rest)");
        let ri = "(add (g x) ..rest)";
        let rhs = parse_rhs(ri);
        let rule = compile_rewrite(
            "test",
            "",
            "",
            &lhs,
            &rhs,
            &[],
            false,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();

        let index = IndexStore::build(&eg);
        let changes = apply_rule(
            &rule,
            &mut eg,
            &index,
            &crate::schedule::IndexStats::from_index(&index),
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );
        assert!(changes > 0);

        // For match x=a, rest={b}: {add (g a) b} merged with {add a b}
        let ga = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        let ga_b = eg.add(eg.ops().id_by_name("add").unwrap(), &[ga, b]);
        assert_eq!(eg.find(ab), eg.find(ga_b));
    }

    #[test]
    fn rewrite_aci_splice_rest() {
        // union is ACI. Match one element, splice rest.
        // {union x ..rest} → {union (g x) ..rest}
        let mut eg = make_eg();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let ab = eg.add(eg.ops().id_by_name("union").unwrap(), &[a, b]);

        let model = NiraModel;
        let lhs = parse_pattern("(union x ..rest)");
        let ri = "(union (g x) ..rest)";
        let rhs = parse_rhs(ri);
        let rule = compile_rewrite(
            "test",
            "",
            "",
            &lhs,
            &rhs,
            &[],
            false,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();

        let index = IndexStore::build(&eg);
        let changes = apply_rule(
            &rule,
            &mut eg,
            &index,
            &crate::schedule::IndexStats::from_index(&index),
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );
        assert!(changes > 0);

        let ga = eg.add(eg.ops().id_by_name("g").unwrap(), &[a]);
        let ga_b = eg.add(eg.ops().id_by_name("union").unwrap(), &[ga, b]);
        assert_eq!(eg.find(ab), eg.find(ga_b));
    }

    #[test]
    fn constant_fold_iadd() {
        use crate::literal::NiraLitVal;
        use num_bigint::BigInt;

        let mut eg = make_eg_with_lits();
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let model = NiraModel;

        // Build (IAdd (ILit (@IBig 3)) (ILit (@IBig 5)))
        let at_ibig = eg.ops().id_by_name("@IBig").unwrap();
        let ilit = eg.ops().id_by_name("ILit").unwrap();
        let iadd = eg.ops().id_by_name("IAdd").unwrap();

        let v3 = eg.intern_lit(NiraLitVal::Int(BigInt::from(3)));
        let n3 = eg.add_lit(at_ibig, v3); // @IBig(3)
        let lit3 = eg.add(ilit, &[n3]); // ILit(@IBig(3))

        let v5 = eg.intern_lit(NiraLitVal::Int(BigInt::from(5)));
        let n5 = eg.add_lit(at_ibig, v5); // @IBig(5)
        let lit5 = eg.add(ilit, &[n5]); // ILit(@IBig(5))

        let add_node = eg.add(iadd, &[lit3, lit5]); // IAdd(ILit(3), ILit(5))

        // Rule: (IAdd (ILit x) (ILit y)) → (ILit (+ x y))
        let lhs = parse_pattern("(IAdd (ILit x) (ILit y))");
        let ri = "(ILit (+ x y))";
        let rhs = parse_rhs(ri);
        let rule = compile_rewrite(
            "test",
            "",
            "",
            &lhs,
            &rhs,
            &[],
            false,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();

        let index = IndexStore::build(&eg);
        let changes = apply_rule(
            &rule,
            &mut eg,
            &index,
            &crate::schedule::IndexStats::from_index(&index),
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );
        assert!(changes > 0, "constant fold should fire");

        // (ILit (@IBig 8)) should now be merged with (IAdd (ILit 3) (ILit 5))
        let v8 = eg.intern_lit(NiraLitVal::Int(BigInt::from(8)));
        let n8 = eg.add_lit(at_ibig, v8);
        let lit8 = eg.add(ilit, &[n8]);
        assert_eq!(
            eg.find(add_node),
            eg.find(lit8),
            "(IAdd (ILit 3) (ILit 5)) should be merged with (ILit 8)"
        );
    }

    /// Rewrite on a PROOFS=true e-graph must produce `Rewrite` justifications.
    #[test]
    fn rewrite_produces_rewrite_justification() {
        type Peg = EGraph<DefaultConfig, NiraLitVal, false, true>;
        let mut eg = Peg::from_model(&NiraModel);
        let mut rules = crate::registry::RuleRegistry::<false>::new();
        let e = eg.intern_sort("IExpr");
        eg.register_op2("f", e, e, e);
        eg.register_op0("a", e);
        eg.register_op0("b", e);

        let a = eg.add(eg.ops().id_by_name("a").unwrap(), &[]);
        let b = eg.add(eg.ops().id_by_name("b").unwrap(), &[]);
        let _fab = eg.add(eg.ops().id_by_name("f").unwrap(), &[a, b]);

        let model = NiraModel;
        let lhs = parse_pattern("(f x y)");
        let rhs = parse_rhs("(f y x)");
        let rule = compile_rewrite(
            "commute-f",
            "(f x y)",
            "(f y x)",
            &lhs,
            &rhs,
            &[],
            false,
            eg.ops(),
            eg.sorts(),
            &mut rules,
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();
        let rule_id = rule.rule_id;

        let index = IndexStore::build(&eg);
        let changes = apply_rule(
            &rule,
            &mut eg,
            &index,
            &crate::schedule::IndexStats::from_index(&index),
            &model,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        );
        assert!(changes > 0);
        eg.rebuild();

        let fba = eg.add(eg.ops().id_by_name("f").unwrap(), &[b, a]);
        let mut buf = crate::union_find::ProofBuf::new();
        assert!(eg.explain(_fab, fba, &mut buf));

        // At least one step must be a Rewrite with our rule_id
        assert!(
            buf.steps
                .iter()
                .any(|&(_, _, j)| j == crate::union_find::Justification::Rewrite { rule_id }),
            "expected a Rewrite {{ rule_id: r0 }} step in the proof, got: {:?}",
            buf.steps,
        );
    }
}
