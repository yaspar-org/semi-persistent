// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Sort-checking: validate that all terms and patterns are well-sorted,
//! resolve operator and sort names to dense ids, produce `CCommand`.

use crate::DenseId;
use crate::ast::*;
use crate::lit_model::LitModel;
use crate::literal::LitVal;
use crate::registry::{OpKind, OpRegistry, SortRegistry};
use crate::resolve::{GlobalCtx, ResolvedQuery};
use std::hash::Hash;

// ── Error type ──

#[derive(Clone, Debug)]
pub struct SortError {
    pub msg: String,
    pub span: Span,
}

impl std::fmt::Display for SortError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.span {
            Span::Dummy => write!(f, "sort error: {}", self.msg),
            Span::Range { start, end } => {
                write!(f, "sort error at {}..{}: {}", start, end, self.msg)
            }
        }
    }
}

fn serr(msg: impl Into<String>, span: Span) -> SortError {
    SortError {
        msg: msg.into(),
        span,
    }
}

// ── Checked types ──

/// Fully sort-checked term. Every node has an `OpId` and a `SortId`.
#[derive(Clone, Debug)]
pub enum CTerm<O, S, L> {
    Lit(L, S),
    App {
        op: O,
        sort: S,
        children: Vec<CTerm<O, S, L>>,
    },
    /// Reference to a let-bound global. Resolved at interpret time.
    Global(String, S),
}

/// Fully resolved command — ready for interpretation.
#[derive(Clone, Debug)]
pub enum CCommand<O, S, L> {
    /// Declaration — replay through interpreter's existing exec path.
    Decl(Command),
    Let(String, CTerm<O, S, L>),
    Union(CTerm<O, S, L>, CTerm<O, S, L>),
    Insert(CTerm<O, S, L>),
    Check(CTerm<O, S, L>),
    CheckEq(CTerm<O, S, L>, CTerm<O, S, L>),
    CheckNeq(CTerm<O, S, L>, CTerm<O, S, L>),
    Extract(CTerm<O, S, L>),
    Rewrite {
        query: ResolvedQuery<O, S, L>,
        rhs: crate::resolve::RRhsTerm<O, S, L>,
        root_vid: crate::ast::VarId,
        subsume: bool,
    },
    Rule {
        query: ResolvedQuery<O, S, L>,
        actions: Vec<crate::resolve::ResolvedAction<O, S, L>>,
    },
    Run(u64),
    Push(bool), // true = shrink on mark
    Pop,
}

// ── Sort-check a Term ──

pub fn check_term<O, S, L, M, const TRACK: bool>(
    term: &Term,
    hint: Option<S>,
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    model: &M,
    globals: &GlobalCtx<S, impl Copy>,
) -> Result<CTerm<O, S, L>, SortError>
where
    O: DenseId + Hash + Copy,
    S: DenseId + Copy,
    L: LitVal,
    M: LitModel<Value = L>,
{
    match term {
        Term::Lit(tok, span) => {
            // Global name?
            if let Some((_gid, sort, _)) = globals.get(tok.as_str()) {
                if let Some(h) = hint
                    && h != sort
                {
                    return Err(serr(
                        format!(
                            "global '{}' has sort '{}' but expected '{}'",
                            tok,
                            sorts.name(sort),
                            sorts.name(h)
                        ),
                        *span,
                    ));
                }
                return Ok(CTerm::Global(tok.clone(), sort));
            }
            // Try hint sort first
            if let Some(sort) = hint {
                let sort_name = sorts.name(sort);
                if let Some(val) = model.parse_as(sort_name, tok) {
                    return Ok(CTerm::Lit(val, sort));
                }
            }
            // Try all sorts
            if let Some((sort_name, val)) = model.parse_any(tok) {
                let sort = sorts
                    .id_by_name(sort_name)
                    .ok_or_else(|| serr(format!("unknown sort '{sort_name}'"), *span))?;
                return Ok(CTerm::Lit(val, sort));
            }
            // Might be a nullary op name
            if let Some(op_id) = ops.id_by_name(tok) {
                let info = ops.info(op_id);
                match &info.kind {
                    OpKind::Normal { arg_sorts } if arg_sorts.is_empty() => {
                        return Ok(CTerm::App {
                            op: op_id,
                            sort: info.return_sort,
                            children: vec![],
                        });
                    }
                    _ => {}
                }
            }
            Err(serr(
                format!("cannot resolve '{tok}' as literal or nullary op"),
                *span,
            ))
        }
        Term::App { op, children, span } => {
            let op_id = ops
                .id_by_name(op)
                .ok_or_else(|| serr(format!("unknown operator '{op}'"), *span))?;
            let info = ops.info(op_id);
            let ret_sort = info.return_sort;

            // Check arity
            let expected = match &info.kind {
                OpKind::Normal { arg_sorts } => Some(arg_sorts.len()),
                OpKind::Commutative { .. } => Some(2),
                OpKind::Lit => Some(0), // lit nodes have no children in terms
                _ => None,              // variadic: any count
            };
            if let Some(exp) = expected
                && children.len() != exp
            {
                return Err(serr(
                    format!(
                        "operator '{op}' expects {exp} arguments, got {}",
                        children.len()
                    ),
                    *span,
                ));
            }

            // Sort-check children
            let mut checked = Vec::with_capacity(children.len());
            for (i, child) in children.iter().enumerate() {
                let child_sort = child_sort_hint(&info.kind, i);
                let ct = check_term(child, child_sort, ops, sorts, model, globals)?;
                // Verify child sort matches expected
                if let Some(expected_sort) = child_sort {
                    let actual = cterm_sort(&ct);
                    if actual != expected_sort {
                        return Err(serr(
                            format!(
                                "argument {} of '{}': expected sort '{}', got '{}'",
                                i + 1,
                                op,
                                sorts.name(expected_sort),
                                sorts.name(actual),
                            ),
                            child.span(),
                        ));
                    }
                }
                checked.push(ct);
            }

            Ok(CTerm::App {
                op: op_id,
                sort: ret_sort,
                children: checked,
            })
        }
    }
}

fn child_sort_hint<S: DenseId + Copy>(kind: &OpKind<S>, pos: usize) -> Option<S> {
    match kind {
        OpKind::Normal { arg_sorts } => arg_sorts.get(pos).copied(),
        OpKind::Commutative { arg_sorts } => arg_sorts.get(pos).copied(),
        OpKind::A { arg_sort, .. } | OpKind::AC { arg_sort } | OpKind::ACI { arg_sort } => {
            Some(*arg_sort)
        }
        OpKind::Lit => None,
    }
}

fn cterm_sort<O, S: Copy, L>(ct: &CTerm<O, S, L>) -> S {
    match ct {
        CTerm::Lit(_, s) | CTerm::Global(_, s) => *s,
        CTerm::App { sort, .. } => *sort,
    }
}

// ── Flatten SurfacePattern directly to Atom (skip Pattern) ──

use crate::compile::{Atom, FlatMult, FlatQuery};
use crate::surface_ast::{SurfaceCommand, SurfacePatChild, SurfacePattern};

/// Flatten surface patterns directly to `FlatQuery`, skipping `Pattern`.
pub fn flatten_surface<O, S, const TRACK: bool>(
    patterns: &[SurfacePattern],
    ops: &crate::registry::OpRegistry<O, S, TRACK>,
) -> Result<FlatQuery, String>
where
    O: crate::DenseId + std::hash::Hash + Copy,
    S: crate::DenseId + Copy,
{
    let mut ctx = SurfaceFlatCtx {
        atoms: Vec::new(),
        next_fresh: 0,
        ops,
    };
    let mut root_vars = Vec::with_capacity(patterns.len());
    for p in patterns {
        root_vars.push(ctx.flatten_root(p)?);
    }
    Ok(FlatQuery {
        atoms: ctx.atoms,
        root_vars,
    })
}

struct SurfaceFlatCtx<'a, O: crate::DenseId, S: crate::DenseId, const TRACK: bool> {
    atoms: Vec<Atom>,
    next_fresh: usize,
    ops: &'a crate::registry::OpRegistry<O, S, TRACK>,
}

impl<'a, O, S, const TRACK: bool> SurfaceFlatCtx<'a, O, S, TRACK>
where
    O: crate::DenseId + std::hash::Hash + Copy,
    S: crate::DenseId + Copy,
{
    fn fresh(&mut self, hint: &str) -> String {
        let id = self.next_fresh;
        self.next_fresh += 1;
        format!("?{hint}{id}")
    }

    fn flatten_root(&mut self, pat: &SurfacePattern) -> Result<String, String> {
        match pat {
            SurfacePattern::Var(v, _) => Ok(v.clone()),
            SurfacePattern::Lit(text, span) => {
                let v = self.fresh("lit");
                self.atoms.push(Atom::Lit {
                    node: v.clone(),
                    text: text.clone(),
                    span: *span,
                });
                Ok(v)
            }
            SurfacePattern::App { .. } => {
                let node = self.fresh("n");
                self.flatten_app(pat, &node)?;
                Ok(node)
            }
        }
    }

    fn flatten_child(&mut self, pat: &SurfacePattern) -> Result<String, String> {
        match pat {
            SurfacePattern::Var(v, _) => Ok(v.clone()),
            SurfacePattern::Lit(text, span) => {
                let v = self.fresh("lit");
                self.atoms.push(Atom::Lit {
                    node: v.clone(),
                    text: text.clone(),
                    span: *span,
                });
                Ok(v)
            }
            SurfacePattern::App { .. } => {
                let v = self.fresh("n");
                self.flatten_app(pat, &v)?;
                Ok(v)
            }
        }
    }

    /// Flatten children, returning var names. Only Elem children (no mults).
    fn flatten_elems(&mut self, children: &[SurfacePatChild]) -> Result<Vec<String>, String> {
        children
            .iter()
            .map(|c| match c {
                SurfacePatChild::Elem(p) => self.flatten_child(p),
                SurfacePatChild::ElemMult(_, _) => unreachable!("mults already rejected"),
            })
            .collect()
    }

    /// Flatten children with multiplicities, returning (var, mult) pairs.
    fn flatten_elems_with_mult(
        &mut self,
        children: &[SurfacePatChild],
    ) -> Result<Vec<(String, FlatMult)>, String> {
        children
            .iter()
            .map(|c| match c {
                SurfacePatChild::Elem(p) => Ok((self.flatten_child(p)?, FlatMult::Exact(1))),
                SurfacePatChild::ElemMult(p, m) => {
                    Ok((self.flatten_child(p)?, flatten_mult_spec(m)))
                }
            })
            .collect()
    }

    fn has_mult(children: &[SurfacePatChild]) -> bool {
        children
            .iter()
            .any(|c| matches!(c, SurfacePatChild::ElemMult(..)))
    }

    fn flatten_app(&mut self, pat: &SurfacePattern, node_var: &str) -> Result<(), String> {
        let SurfacePattern::App {
            op,
            prefix,
            children,
            suffix,
            span,
        } = pat
        else {
            unreachable!()
        };
        let has_mult = Self::has_mult(children);

        let op_id = self
            .ops
            .id_by_name(op)
            .ok_or_else(|| format!("unknown operator '{op}'"))?;
        let info = self.ops.info(op_id);

        match &info.kind {
            OpKind::Normal { arg_sorts } => {
                if prefix.is_some() || suffix.is_some() {
                    return Err(format!(
                        "operator '{op}' is plain; rest variables not allowed"
                    ));
                }
                if has_mult {
                    return Err(format!(
                        "operator '{op}' is plain; multiplicities not allowed"
                    ));
                }
                if children.len() != arg_sorts.len() {
                    return Err(format!(
                        "operator '{op}' expects {} args, got {}",
                        arg_sorts.len(),
                        children.len()
                    ));
                }
                let cvars = self.flatten_elems(children)?;
                self.atoms.push(Atom::Plain {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    children: cvars,
                    span: *span,
                });
            }
            OpKind::Commutative { .. } => {
                if prefix.is_some() || suffix.is_some() {
                    return Err(format!(
                        "operator '{op}' is commutative; rest variables not allowed"
                    ));
                }
                if has_mult {
                    return Err(format!(
                        "operator '{op}' is commutative; multiplicities not allowed"
                    ));
                }
                if children.len() != 2 {
                    return Err(format!(
                        "operator '{op}' expects 2 args, got {}",
                        children.len()
                    ));
                }
                let cvars = self.flatten_elems(children)?;
                self.atoms.push(Atom::Plain {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    children: cvars,
                    span: *span,
                });
            }
            OpKind::Lit => {
                if prefix.is_some() || suffix.is_some() {
                    return Err(format!(
                        "operator '{op}' is a literal op; rest variables not allowed"
                    ));
                }
                if has_mult {
                    return Err(format!(
                        "operator '{op}' is a literal op; multiplicities not allowed"
                    ));
                }
                if children.len() != 1 {
                    return Err(format!(
                        "operator '{op}' expects 1 arg, got {}",
                        children.len()
                    ));
                }
                let cvars = self.flatten_elems(children)?;
                self.atoms.push(Atom::Plain {
                    node: node_var.to_owned(),
                    op: op.clone(),
                    children: cvars,
                    span: *span,
                });
            }
            OpKind::A { .. } => {
                if has_mult {
                    return Err(format!(
                        "operator '{op}' is associative; multiplicities not allowed (use AC)"
                    ));
                }
                let fixed = self.flatten_elems(children)?;
                match (prefix, suffix) {
                    (None, None) => {
                        self.atoms.push(Atom::AExact {
                            node: node_var.to_owned(),
                            op: op.clone(),
                            children: fixed,
                            span: *span,
                        });
                    }
                    (Some((pre, _)), None) => {
                        self.atoms.push(Atom::APrefix {
                            node: node_var.to_owned(),
                            op: op.clone(),
                            rest: pre.clone(),
                            fixed,
                            span: *span,
                        });
                    }
                    (None, Some((suf, _))) => {
                        self.atoms.push(Atom::ASuffix {
                            node: node_var.to_owned(),
                            op: op.clone(),
                            fixed,
                            rest: suf.clone(),
                            span: *span,
                        });
                    }
                    (Some((pre, _)), Some((suf, _))) => {
                        self.atoms.push(Atom::ABoth {
                            node: node_var.to_owned(),
                            op: op.clone(),
                            pre: pre.clone(),
                            fixed,
                            suf: suf.clone(),
                            span: *span,
                        });
                    }
                }
            }
            OpKind::AC { .. } => {
                if prefix.is_some() {
                    return Err(format!(
                        "operator '{op}' is AC; prefix rest variable not allowed"
                    ));
                }
                let elems = self.flatten_elems_with_mult(children)?;
                match suffix {
                    None => {
                        self.atoms.push(Atom::ACExact {
                            node: node_var.to_owned(),
                            op: op.clone(),
                            elems,
                            span: *span,
                        });
                    }
                    Some((rest, _)) => {
                        self.atoms.push(Atom::ACSub {
                            node: node_var.to_owned(),
                            op: op.clone(),
                            elems,
                            rest: rest.clone(),
                            span: *span,
                        });
                    }
                }
            }
            OpKind::ACI { .. } => {
                if prefix.is_some() {
                    return Err(format!(
                        "operator '{op}' is ACI; prefix rest variable not allowed"
                    ));
                }
                if has_mult {
                    return Err(format!(
                        "operator '{op}' is ACI (set); multiplicities not allowed (use AC)"
                    ));
                }
                let elems = self.flatten_elems(children)?;
                match suffix {
                    None => {
                        self.atoms.push(Atom::ACIExact {
                            node: node_var.to_owned(),
                            op: op.clone(),
                            elems,
                            span: *span,
                        });
                    }
                    Some((rest, _)) => {
                        self.atoms.push(Atom::ACISub {
                            node: node_var.to_owned(),
                            op: op.clone(),
                            elems,
                            rest: rest.clone(),
                            span: *span,
                        });
                    }
                }
            }
        }
        Ok(())
    }
}

fn flatten_mult_spec(m: &MultSpec) -> FlatMult {
    match m {
        MultSpec::Exact(n) => FlatMult::Exact(*n),
        MultSpec::Var { name, constraint } => FlatMult::Var {
            name: name.clone(),
            constraint: *constraint,
        },
    }
}

// ── Top-level sort-check ──

use crate::resolve::{resolve, resolve_action, resolve_rhs};

/// Sort-check a full program against a live egraph.
/// Declarations register directly into the egraph (setting up caches).
pub fn sortcheck_program<Cfg, L, M, const TRACK: bool, const PROOFS: bool>(
    cmds: Vec<SurfaceCommand>,
    eg: &mut crate::egraph::EGraph<Cfg, L, TRACK, PROOFS>,
    model: &M,
    globals: &mut GlobalCtx<Cfg::S>,
) -> Result<Vec<CCommand<Cfg::O, Cfg::S, L>>, SortError>
where
    Cfg: crate::config::EGraphConfig,
    Cfg::O: Hash,
    L: LitVal,
    M: LitModel<Value = L>,
    crate::canon::ACCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
{
    let mut out = Vec::with_capacity(cmds.len());
    for cmd in cmds {
        out.push(sortcheck_one(cmd, eg, model, globals)?);
    }
    Ok(out)
}

fn sortcheck_one<Cfg, L, M, const TRACK: bool, const PROOFS: bool>(
    cmd: SurfaceCommand,
    eg: &mut crate::egraph::EGraph<Cfg, L, TRACK, PROOFS>,
    model: &M,
    globals: &mut GlobalCtx<Cfg::S>,
) -> Result<CCommand<Cfg::O, Cfg::S, L>, SortError>
where
    Cfg: crate::config::EGraphConfig,
    Cfg::O: Hash,
    L: LitVal,
    M: LitModel<Value = L>,
    crate::canon::ACCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
{
    match cmd {
        SurfaceCommand::Pass(c) => sortcheck_pass(c, eg, model, globals),
        SurfaceCommand::Rewrite {
            lhs,
            rhs,
            when,
            subsume,
        } => {
            let mut pats = vec![lhs];
            pats.extend(when);
            let fq = flatten_surface(&pats, eg.ops()).map_err(|e| serr(e, Span::Dummy))?;
            let root_name = fq.root_vars[0].clone();
            let rq = resolve(&fq, eg.ops(), eg.sorts(), model, globals)
                .map_err(|e| serr(e.to_string(), Span::Dummy))?;
            let root_vid = rq.shape.find_var(&root_name).expect("root var");
            let mut vs = rq.var_sorts.clone();
            let mut shape = rq.shape.clone();
            let root_sort = vs[root_vid.idx()];
            let resolved_rhs = resolve_rhs(
                &rhs,
                root_sort,
                eg.ops(),
                eg.sorts(),
                model,
                &mut vs,
                &mut shape,
                globals,
            )
            .map_err(|e| serr(e.to_string(), Span::Dummy))?;
            Ok(CCommand::Rewrite {
                query: rq,
                rhs: resolved_rhs,
                root_vid,
                subsume,
            })
        }
        SurfaceCommand::Rule { body, head } => {
            let fq = flatten_surface(&body, eg.ops()).map_err(|e| serr(e, Span::Dummy))?;
            let rq = resolve(&fq, eg.ops(), eg.sorts(), model, globals)
                .map_err(|e| serr(e.to_string(), Span::Dummy))?;
            let mut vs = rq.var_sorts.clone();
            let mut shape = rq.shape.clone();
            let mut actions = Vec::with_capacity(head.len());
            for a in &head {
                let ra =
                    resolve_action(a, eg.ops(), eg.sorts(), model, &mut vs, &mut shape, globals)
                        .map_err(|e| serr(e.to_string(), Span::Dummy))?;
                actions.push(ra);
            }
            Ok(CCommand::Rule { query: rq, actions })
        }
    }
}

fn sortcheck_pass<Cfg, L, M, const TRACK: bool, const PROOFS: bool>(
    cmd: Command,
    eg: &mut crate::egraph::EGraph<Cfg, L, TRACK, PROOFS>,
    model: &M,
    globals: &mut GlobalCtx<Cfg::S>,
) -> Result<CCommand<Cfg::O, Cfg::S, L>, SortError>
where
    Cfg: crate::config::EGraphConfig,
    Cfg::O: Hash,
    L: LitVal,
    M: LitModel<Value = L>,
    crate::canon::ACCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
{
    // Declarations: register into egraph, then wrap as Decl
    match &cmd {
        Command::Sort(_) | Command::Function { .. } | Command::Datatype { .. } => {
            // Use the interpreter's existing exec_function / intern_sort logic
            // by delegating to the egraph directly.
            exec_decl(&cmd, eg)?;
            return Ok(CCommand::Decl(cmd));
        }
        _ => {}
    }
    // Non-declaration commands: sort-check terms
    match cmd {
        Command::Let(name, term) => {
            let ct = check_term(&term, None, eg.ops(), eg.sorts(), model, globals)?;
            globals.insert(name.clone(), cterm_sort(&ct), ());
            Ok(CCommand::Let(name, ct))
        }
        Command::Union(a, b) => {
            let ca = check_term(&a, None, eg.ops(), eg.sorts(), model, globals)?;
            let cb = check_term(&b, None, eg.ops(), eg.sorts(), model, globals)?;
            Ok(CCommand::Union(ca, cb))
        }
        Command::Insert(term) => {
            let ct = check_term(&term, None, eg.ops(), eg.sorts(), model, globals)?;
            Ok(CCommand::Insert(ct))
        }
        Command::Check(t) => {
            let ct = check_term(&t, None, eg.ops(), eg.sorts(), model, globals)?;
            Ok(CCommand::Check(ct))
        }
        Command::CheckEq(a, b) => {
            let ca = check_term(&a, None, eg.ops(), eg.sorts(), model, globals)?;
            let cb = check_term(&b, None, eg.ops(), eg.sorts(), model, globals)?;
            Ok(CCommand::CheckEq(ca, cb))
        }
        Command::CheckNeq(a, b) => {
            let ca = check_term(&a, None, eg.ops(), eg.sorts(), model, globals)?;
            let cb = check_term(&b, None, eg.ops(), eg.sorts(), model, globals)?;
            Ok(CCommand::CheckNeq(ca, cb))
        }
        Command::Extract(t) => {
            let ct = check_term(&t, None, eg.ops(), eg.sorts(), model, globals)?;
            Ok(CCommand::Extract(ct))
        }
        Command::Run(n) => Ok(CCommand::Run(n)),
        Command::Push(shrink) => Ok(CCommand::Push(shrink)),
        Command::Pop => Ok(CCommand::Pop),
        _ => unreachable!(),
    }
}

/// Register a declaration command into the egraph.
fn exec_decl<Cfg, L, const TRACK: bool, const PROOFS: bool>(
    cmd: &Command,
    eg: &mut crate::egraph::EGraph<Cfg, L, TRACK, PROOFS>,
) -> Result<(), SortError>
where
    Cfg: crate::config::EGraphConfig,
    Cfg::O: Hash,
    L: LitVal,
    crate::canon::ACCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
{
    match cmd {
        Command::Sort(name) => {
            eg.intern_sort(name);
        }
        Command::Function {
            name,
            arg_sorts,
            ret_sort,
            attr,
        } => {
            let ret = eg
                .sorts()
                .id_by_name(ret_sort)
                .ok_or_else(|| serr(format!("unknown sort '{ret_sort}'"), Span::Dummy))?;
            let args: Vec<Cfg::S> = arg_sorts
                .iter()
                .map(|s| {
                    eg.sorts()
                        .id_by_name(s)
                        .ok_or_else(|| serr(format!("unknown sort '{s}'"), Span::Dummy))
                })
                .collect::<Result<_, _>>()?;
            register_op(eg, name, &args, ret, *attr)?;
        }
        Command::Datatype { name, variants } => {
            eg.intern_sort(name);
            let sid = eg.sorts().id_by_name(name).unwrap();
            for (ctor, arg_names, attr) in variants {
                let arg_ids: Vec<Cfg::S> = arg_names
                    .iter()
                    .map(|s| {
                        eg.sorts()
                            .id_by_name(s)
                            .ok_or_else(|| serr(format!("unknown sort '{s}'"), Span::Dummy))
                    })
                    .collect::<Result<_, _>>()?;
                let oid = register_op(eg, ctor, &arg_ids, sid, *attr)?;
                eg.ops_mut().set_constructor(oid);
            }
        }
        _ => {}
    }
    Ok(())
}

fn register_op<Cfg, L, const TRACK: bool, const PROOFS: bool>(
    eg: &mut crate::egraph::EGraph<Cfg, L, TRACK, PROOFS>,
    name: &str,
    args: &[Cfg::S],
    ret: Cfg::S,
    attr: Option<AlgAttr>,
) -> Result<Cfg::O, SortError>
where
    Cfg: crate::config::EGraphConfig,
    Cfg::O: Hash,
    L: LitVal,
    crate::canon::ACCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
{
    Ok(match attr {
        None => eg.register_opn(name, args, ret),
        Some(AlgAttr::Comm) => {
            if args.len() != 2 {
                return Err(serr(":comm requires 2 args", Span::Dummy));
            }
            eg.register_c(name, [args[0], args[1]], ret)
        }
        Some(AlgAttr::Assoc | AlgAttr::AssocLeft) => {
            if args.len() != 1 {
                return Err(serr(":assoc requires 1 arg", Span::Dummy));
            }
            eg.register_a(name, args[0], ret, crate::registry::AssocDir::Left)
        }
        Some(AlgAttr::AssocRight) => {
            if args.len() != 1 {
                return Err(serr(":assoc-right requires 1 arg", Span::Dummy));
            }
            eg.register_a(name, args[0], ret, crate::registry::AssocDir::Right)
        }
        Some(AlgAttr::AssocComm) => {
            if args.len() != 1 {
                return Err(serr(":assoc-comm requires 1 arg", Span::Dummy));
            }
            eg.register_ac(name, args[0], ret)
        }
        Some(AlgAttr::AssocCommIdem) => {
            if args.len() != 1 {
                return Err(serr(":assoc-comm-idem requires 1 arg", Span::Dummy));
            }
            eg.register_aci(name, args[0], ret)
        }
    })
}
