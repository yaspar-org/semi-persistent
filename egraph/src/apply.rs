// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Compiled RHS terms and apply function.
//!
//! All variable references use the typed dense ids from LHS resolve
//! for O(1) lookup into Match / MatchSet. The apply function walks
//! the compiled RHS tree bottom-up, building e-graph terms via `eg.add()`.

use crate::ast::{GlobalVarId, LitValVarId, MsetVarId, MultVarId, SeqVarId, SetVarId, VarId};
use crate::containers::DenseId;
use crate::resolve::{RRhsChild, RRhsTerm};

// ---------------------------------------------------------------------------
// Compiled RHS types
// ---------------------------------------------------------------------------

/// Instruction that produces one `Cfg::G` when evaluated against a Match.
#[derive(Clone, Debug)]
pub enum RhsOp<O, V> {
    /// Fetch bound e-node id from match.
    FetchNode(VarId),
    /// Create literal node via `eg.add_lit()`.
    Lit(O, V),
    /// Reconstruct `@sort(val)` lit node from a bound LitValVarId.
    LitVar(O, LitValVarId),
    /// Build `(op args...)` via `eg.add()`. Args may expand to multiple children.
    App { op: O, args: Vec<RhsArg<O, V>> },
    /// Evaluate a prim op on bound lit values, intern result.
    PrimApp { op: O, args: Vec<LitValVarId> },
    /// Fetch a global e-class id from the runtime global bindings.
    FetchGlobal(GlobalVarId),
}

/// An argument to `App` — produces one or many children.
#[derive(Clone, Debug)]
pub enum RhsArg<O, V> {
    /// Single child.
    One(RhsOp<O, V>),
    /// Splice sequence rest into children.
    SpliceSeq(SeqVarId),
    /// Splice set rest into children.
    SpliceSet(SetVarId),
    /// Splice multiset rest into children (each element repeated by its multiplicity).
    SpliceMset(MsetVarId),
    /// Set comprehension: map body over set rest.
    SetComp {
        body: Box<RhsOp<O, V>>,
        var: VarId,
        source: SetVarId,
        filter: Option<Box<RhsOp<O, V>>>,
    },
    /// Multiset comprehension: map body over mset rest, with output multiplicity.
    MsetComp {
        body: Box<RhsOp<O, V>>,
        mult: crate::resolve::ResolvedMultExpr,
        var: VarId,
        mult_var: MultVarId,
        source: MsetVarId,
        filter: Option<Box<RhsOp<O, V>>>,
    },
    /// Sequence comprehension: map body over seq rest.
    SeqComp {
        body: Box<RhsOp<O, V>>,
        var: VarId,
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

#[derive(Clone, Debug)]
pub struct PreparedRule<O, S, V> {
    pub rule_id: crate::id::RuleId,
    pub query: crate::resolve::ResolvedQuery<O, S, V>,
    pub actions: Vec<CompiledAction<O, V>>,
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
    let mut vs = rq.var_sorts.clone();
    let mut shape = rq.shape.clone();
    let root_sort = vs[root_vid.idx()];
    let resolved_rhs = crate::resolve::resolve_rhs(
        rhs, root_sort, ops, sorts, model, &mut vs, &mut shape, globals,
    )?;
    let compiled_rhs = compile_rhs(&resolved_rhs);

    let mut actions = vec![CompiledAction::Union(
        rule_id,
        RhsOp::FetchNode(root_vid),
        compiled_rhs,
    )];
    if subsume {
        actions.push(CompiledAction::Subsume(root_vid));
    }

    Ok(PreparedRule {
        rule_id,
        query: rq,
        actions,
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

    let mut vs = rq.var_sorts.clone();
    let mut shape = rq.shape.clone();
    let mut actions = Vec::with_capacity(head.len());
    for a in head {
        let ra =
            crate::resolve::resolve_action(a, ops, sorts, model, &mut vs, &mut shape, globals)?;
        actions.push(compile_action(&ra, rule_id));
    }

    Ok(PreparedRule {
        rule_id,
        query: rq,
        actions,
    })
}

// ---------------------------------------------------------------------------
// Eval: execute compiled RHS against a Match and e-graph
// ---------------------------------------------------------------------------

use crate::EGraphConfig;
use crate::canon::{MSetCanon, VarCanon};
use crate::egraph::EGraph;
use crate::ematch::{Match, run_query};
use crate::index::IndexStore;
use crate::literal::LitVal;

pub fn eval<Cfg, L, M, S: Copy, const T: bool, const P: bool>(
    op: &RhsOp<Cfg::O, L>,
    m: &mut Match<Cfg>,
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> Cfg::G
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    match op {
        RhsOp::FetchNode(vid) => eg.find(m.get(*vid)),
        RhsOp::FetchGlobal(gid) => eg.find(globals.binding(*gid)),
        RhsOp::Lit(op, val) => {
            let id = eg.lits_mut().intern(val.clone());
            eg.add_lit(*op, id)
        }
        RhsOp::LitVar(op, lvid) => {
            let val_id = m.get_lit_val(*lvid);
            eg.add_lit(*op, val_id)
        }
        RhsOp::App { op: o, args } => {
            let mut children = Vec::new();
            for arg in args {
                eval_arg(arg, m, eg, model, globals, &mut children);
            }
            eg.add(*o, &children)
        }
        RhsOp::PrimApp { op, args } => {
            // Gather bound lit values from the match
            let raw_vals: Vec<L> = args
                .iter()
                .map(|vid| {
                    let lit_val_id = m.get_lit_val(*vid);
                    eg.lits().get(lit_val_id).clone()
                })
                .collect();
            let refs: Vec<&L> = raw_vals.iter().collect();
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

fn eval_arg<Cfg, L, M, S: Copy, const T: bool, const P: bool>(
    arg: &RhsArg<Cfg::O, L>,
    m: &mut Match<Cfg>,
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
    out: &mut Vec<Cfg::G>,
) where
    Cfg: EGraphConfig,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    match arg {
        RhsArg::One(inner) => out.push(eval(inner, m, eg, model, globals)),
        RhsArg::SpliceSeq(sid) => out.extend_from_slice(m.seq_slice(*sid)),
        RhsArg::SpliceSet(sid) => out.extend_from_slice(m.set_slice(*sid)),
        RhsArg::SpliceMset(mid) => {
            for c in m.mset_slice(*mid) {
                let id = Cfg::mset_child_id(c);
                let mult = Cfg::mset_child_mult(c);
                let mult_u32: u32 = mult.into();
                for _ in 0..mult_u32 {
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
            let slice = m.seq_slice(*source).to_vec();
            for elem in slice {
                m.set(*var, elem);
                if let Some(f) = filter {
                    let g = eval(f, m, eg, model, globals);
                    if !check_filter_truthy(eg, model, g) {
                        continue;
                    }
                }
                out.push(eval(body, m, eg, model, globals));
            }
            m.clear(*var);
        }
        RhsArg::SetComp {
            body,
            var,
            source,
            filter,
        } => {
            let slice = m.set_slice(*source).to_vec();
            for elem in slice {
                m.set(*var, elem);
                if let Some(f) = filter {
                    let g = eval(f, m, eg, model, globals);
                    if !check_filter_truthy(eg, model, g) {
                        continue;
                    }
                }
                out.push(eval(body, m, eg, model, globals));
            }
            m.clear(*var);
        }
        RhsArg::MsetComp {
            body,
            mult: out_mult,
            var,
            mult_var,
            source,
            filter,
        } => {
            let slice = m.mset_slice(*source).to_vec();
            for c in &slice {
                let id = Cfg::mset_child_id(c);
                let src_mult = Cfg::mset_child_mult(c);
                m.set(*var, id);
                m.set_mult(*mult_var, src_mult);
                if let Some(f) = filter {
                    let g = eval(f, m, eg, model, globals);
                    if !check_filter_truthy(eg, model, g) {
                        continue;
                    }
                }
                let result = eval(body, m, eg, model, globals);
                let n: u32 = match out_mult {
                    crate::resolve::ResolvedMultExpr::Lit(n) => *n as u32,
                    crate::resolve::ResolvedMultExpr::Var(mid) => m.get_mult(*mid).into(),
                };
                for _ in 0..n {
                    out.push(result);
                }
            }
            m.clear(*var);
        }
    }
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
    match eg.get_lit_val(id) {
        Some(val) => M::is_truthy(val),
        None => false,
    }
}

pub fn apply_action<Cfg, L, M, S: Copy, const T: bool, const P: bool>(
    action: &CompiledAction<Cfg::O, L>,
    m: &mut Match<Cfg>,
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    globals: &crate::resolve::GlobalCtx<S, Cfg::G>,
) -> usize
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    match action {
        CompiledAction::Union(rule_id, a, b) => {
            let va = eval(a, m, eg, model, globals);
            let vb = eval(b, m, eg, model, globals);
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
            eval(t, m, eg, model, globals);
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
            let node = m.get(*var);
            eg.subsume(node);
            1
        }
    }
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
    let plan = crate::schedule::schedule_with_stats(&rule.query, stats);
    let vindex = crate::index::VariantIndex::naive(index);
    let mut matches = run_query(&plan, eg, &vindex, globals);
    let mut changes = 0;
    for m in &mut matches {
        for action in &rule.actions {
            changes += apply_action(action, m, eg, model, globals);
        }
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
    use crate::resolve::{resolve, resolve_rhs};
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
        let mut vs = rq.var_sorts.clone();
        let mut shape = rq.shape.clone();
        let rhs = resolve_rhs(
            &rhs_ast,
            root_sort,
            &ops,
            &sorts,
            &model,
            &mut vs,
            &mut shape,
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
        let mut vs = rq.var_sorts.clone();
        let mut shape = rq.shape.clone();
        let rhs = resolve_rhs(
            &rhs_ast,
            root_sort,
            &ops,
            &sorts,
            &model,
            &mut vs,
            &mut shape,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();
        let c = compile_rhs(&rhs);
        // The compiled term should reference the same VarId the parser assigned to "x"
        let x_vid = shape.find_var("x").unwrap();
        assert!(matches!(c, RhsOp::FetchNode(v) if v == x_vid));
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
        let mut vs = rq.var_sorts.clone();
        let mut shape = rq.shape.clone();
        let rhs = resolve_rhs(
            &rhs_ast,
            root_sort,
            &ops,
            &sorts,
            &model,
            &mut vs,
            &mut shape,
            &crate::resolve::GlobalCtx::<crate::id::SortId, crate::id::ENodeId>::new(),
        )
        .unwrap();
        let c = compile_rhs(&rhs);

        let x_vid = shape.find_var("x").unwrap();
        let y_vid = shape.find_var("y").unwrap();
        match c {
            RhsOp::App { args: children, .. } => {
                // (f y x) — first child is y, second is x
                assert!(matches!(&children[0], RhsArg::One(RhsOp::FetchNode(v)) if *v == y_vid));
                assert!(matches!(&children[1], RhsArg::One(RhsOp::FetchNode(v)) if *v == x_vid));
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
            let mut vs = rq.var_sorts.clone();
            let mut shape = rq.shape.clone();
            let rhs = resolve_rhs(
                &rhs_ast,
                root_sort,
                &ops,
                &sorts,
                &model,
                &mut vs,
                &mut shape,
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
            R::Var(v) => println!("{indent}Var(VarId({}))", v.idx()),
            R::Lit { sort, value, .. } => println!("{indent}Lit(sort={sort:?}, val={value:?})"),
            R::App { op, children } => {
                println!("{indent}App(op={op:?})");
                for (i, c) in children.iter().enumerate() {
                    match c {
                        RC::Term(t) => {
                            println!("{indent}  child[{i}]:");
                            print_rhs(&format!("{indent}    "), t);
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
            RhsOp::FetchNode(v) => println!("{indent}FetchNode(VarId({}))", v.idx()),
            RhsOp::Lit(op, id) => println!("{indent}Lit({op:?}, {id:?})"),
            RhsOp::App { op: o, args } => {
                println!("{indent}App(op={o:?})");
                for (i, a) in args.iter().enumerate() {
                    match a {
                        RhsArg::One(inner) => {
                            println!("{indent}  arg[{i}]:");
                            print_compiled(&format!("{indent}    "), inner);
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
