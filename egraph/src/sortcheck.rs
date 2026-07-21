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
    AntiUnify {
        left: CTerm<O, S, L>,
        right: CTerm<O, S, L>,
        playouts: u64,
        algorithm: String,
    },
    CheckAu {
        left: CTerm<O, S, L>,
        right: CTerm<O, S, L>,
        max_size: u32,
        playouts: u64,
        algorithm: String,
    },
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

            // Zero-child variadic applications: the empty monomial denotes the op's
            // identity, so `(add)` is meaningful only when the op declares `:identity e`
            // (it then builds the unit). Without one, the empty monomial names nothing in
            // the algebra — reject here, mirroring the pattern-side "at least 1 child"
            // rule, instead of minting a meaningless empty node.
            if children.is_empty() {
                match &info.kind {
                    OpKind::MSet { identity: None, .. } | OpKind::Set { identity: None, .. } => {
                        return Err(serr(
                            format!(
                                "operator '{op}' has no :identity — a zero-argument \
                                 application (the empty monomial) is meaningless; declare \
                                 an identity or supply at least one argument"
                            ),
                            *span,
                        ));
                    }
                    OpKind::A { .. } => {
                        return Err(serr(
                            format!("operator '{op}' requires at least 1 argument"),
                            *span,
                        ));
                    }
                    _ => {}
                }
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
        OpKind::A { arg_sort, .. }
        | OpKind::MSet { arg_sort, .. }
        | OpKind::Set { arg_sort, .. } => Some(*arg_sort),
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
            OpKind::MSet { .. } => {
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
            OpKind::Set { .. } => {
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
    crate::canon::MSetCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
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
    crate::canon::MSetCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
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
    crate::canon::MSetCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
{
    // Declarations: register into egraph, then wrap as Decl
    match &cmd {
        Command::Sort(_) | Command::Function { .. } | Command::Datatype { .. } => {
            // Use the interpreter's existing exec_function / intern_sort logic
            // by delegating to the egraph directly.
            exec_decl(&cmd, eg, model, globals)?;
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
        Command::AntiUnify {
            left,
            right,
            playouts,
            algorithm,
        } => {
            let cl = check_term(&left, None, eg.ops(), eg.sorts(), model, globals)?;
            let cr = check_term(&right, None, eg.ops(), eg.sorts(), model, globals)?;
            Ok(CCommand::AntiUnify {
                left: cl,
                right: cr,
                playouts,
                algorithm,
            })
        }
        Command::CheckAu {
            left,
            right,
            max_size,
            playouts,
            algorithm,
        } => {
            let cl = check_term(&left, None, eg.ops(), eg.sorts(), model, globals)?;
            let cr = check_term(&right, None, eg.ops(), eg.sorts(), model, globals)?;
            Ok(CCommand::CheckAu {
                left: cl,
                right: cr,
                max_size,
                playouts,
                algorithm,
            })
        }
        Command::Push(shrink) => Ok(CCommand::Push(shrink)),
        Command::Pop => Ok(CCommand::Pop),
        _ => unreachable!(),
    }
}

/// Register a declaration command into the egraph. `model`/`globals` are needed to resolve a
/// completion op's `:identity` unit term to a node at registration.
fn exec_decl<Cfg, L, M, const TRACK: bool, const PROOFS: bool>(
    cmd: &Command,
    eg: &mut crate::egraph::EGraph<Cfg, L, TRACK, PROOFS>,
    model: &M,
    globals: &GlobalCtx<Cfg::S>,
) -> Result<(), SortError>
where
    Cfg: crate::config::EGraphConfig,
    Cfg::O: Hash,
    L: LitVal,
    M: LitModel<Value = L>,
    crate::canon::MSetCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
{
    match cmd {
        Command::Sort(name) => {
            eg.intern_sort(name);
        }
        Command::Function {
            name,
            arg_sorts,
            ret_sort,
            tags,
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
            register_op(eg, name, &args, ret, tags, model, globals)?;
        }
        Command::Datatype { name, variants } => {
            eg.intern_sort(name);
            let sid = eg.sorts().id_by_name(name).unwrap();
            for (ctor, arg_names, tags) in variants {
                let arg_ids: Vec<Cfg::S> = arg_names
                    .iter()
                    .map(|s| {
                        eg.sorts()
                            .id_by_name(s)
                            .ok_or_else(|| serr(format!("unknown sort '{s}'"), Span::Dummy))
                    })
                    .collect::<Result<_, _>>()?;
                let oid = register_op(eg, ctor, &arg_ids, sid, tags, model, globals)?;
                eg.ops_mut().set_constructor(oid);
            }
        }
        _ => {}
    }
    Ok(())
}

/// Resolve a composable algebra-tag set into a concrete op registration (multi-AC/ACI plan,
/// Facet A). Validates the combination and builds the `OpKind` descriptor. A declared
/// `:identity e` is resolved to a real node here (sortcheck has the model) and stored in the
/// egraph's per-op unit map; `:inverse` is validated but its resolved op is not stored yet
/// (deferred to the group facet). Plain `:assoc :comm` reproduces AC, `+ :idempotent` reproduces
/// ACI; the unit only affects completion once it is consumed (identity drop in the round).
fn register_op<Cfg, L, M, const TRACK: bool, const PROOFS: bool>(
    eg: &mut crate::egraph::EGraph<Cfg, L, TRACK, PROOFS>,
    name: &str,
    args: &[Cfg::S],
    ret: Cfg::S,
    tags: &[AlgTag],
    model: &M,
    globals: &GlobalCtx<Cfg::S>,
) -> Result<Cfg::O, SortError>
where
    Cfg: crate::config::EGraphConfig,
    Cfg::O: Hash,
    L: LitVal,
    M: LitModel<Value = L>,
    crate::canon::MSetCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
{
    use crate::registry::{AssocDir, Clamp, OpKind, UnitRef};

    // No tags → plain op.
    if tags.is_empty() {
        return Ok(eg.register_opn(name, args, ret));
    }

    // Collect the tag set into flags. Duplicate/conflicting basic tags are folded; direction
    // and value tags are captured. Order-independent.
    let mut comm = false;
    let mut assoc = false;
    let mut dir: Option<AssocDir> = None; // set by assoc-left/right
    let mut idempotent = false;
    let mut nilpotent: Option<u8> = None;
    let mut identity: Option<Term> = None;
    let mut cancellative = false;
    let mut inverse: Option<String> = None;
    for tag in tags {
        match tag {
            AlgTag::Comm => comm = true,
            AlgTag::Assoc => assoc = true,
            AlgTag::AssocLeft => {
                assoc = true;
                dir = Some(AssocDir::Left);
            }
            AlgTag::AssocRight => {
                assoc = true;
                dir = Some(AssocDir::Right);
            }
            AlgTag::Idempotent => idempotent = true,
            AlgTag::Nilpotent(order) => nilpotent = Some(order.unwrap_or(2)),
            AlgTag::Identity(term) => identity = Some(term.clone()),
            AlgTag::Cancellative => cancellative = true,
            AlgTag::Inverse(n) => inverse = Some(n.clone()),
        }
    }

    // --- Validation (reject at registration; design §"Validation at registration") ---
    if idempotent && nilpotent.is_some() {
        return Err(serr(
            ":idempotent and :nilpotent are mutually exclusive",
            Span::Dummy,
        ));
    }
    // Idempotent + inverse is algebraically incoherent, not merely unimplemented: an idempotent
    // group is trivial (x∘x = x ⟹ x = e), so an idempotent op has no non-trivial inverses. (The
    // intended `not`/complement cancels to the annihilator, not the identity — it is a `xor`, not
    // an `and`-inverse. See the design doc "Inverse is a group inverse, not a complement".)
    if idempotent && inverse.is_some() {
        return Err(serr(
            ":idempotent and :inverse are mutually exclusive (an idempotent op has no group inverse; \
             logical negation is xor-with-true, not an and-inverse)",
            Span::Dummy,
        ));
    }
    // A cancellative idempotent monoid is trivial: x∘x = x and cancellation
    // give x = e for every x, so the tag set describes a one-element algebra.
    if idempotent && cancellative {
        return Err(serr(
            ":idempotent and :cancellative are mutually exclusive (a cancellative idempotent \
             monoid collapses to the identity)",
            Span::Dummy,
        ));
    }
    if (idempotent || nilpotent.is_some()) && !(assoc && comm) {
        return Err(serr(
            ":idempotent/:nilpotent require :assoc :comm",
            Span::Dummy,
        ));
    }
    if nilpotent.is_some() && identity.is_none() {
        return Err(serr(
            ":nilpotent requires :identity (the emptied monomial must reduce to the unit)",
            Span::Dummy,
        ));
    }
    if inverse.is_some() && identity.is_none() {
        return Err(serr(":inverse requires :identity", Span::Dummy));
    }
    // Cancellativity is an inference rule on AC monomial equations (Kapur §5); on an
    // A-only, C-only, or plain operator the tag would be stored nowhere and silently
    // ignored, so reject it up front like the other AC-only property tags.
    if cancellative && !(assoc && comm) {
        return Err(serr(
            ":cancellative requires :assoc :comm (an AC operator)",
            Span::Dummy,
        ));
    }
    // Facet status (2026-07-10): `:cancellative` drives the Kapur §5 cancel-closure
    // inferences (C1 rule cancel-close + C2 cancelative disjoint superposition, minus the
    // §5.2(iii)(b) no-identity per-constant case), and `:inverse` drives inverse-PAIR
    // cancellation (x ∘ inv(x) = e) — gate-level group support, not §5.4's full
    // Abelian-group completion. An op with an inverse is cancelative (a group is), so the
    // flag is implied below.
    let cancellative = cancellative || inverse.is_some();

    // Build the deferred unit reference from the identity term, if any.
    let unit_ref = match &identity {
        None => None,
        Some(Term::Lit(tok, _)) => Some(UnitRef::Lit { token: tok.clone() }),
        Some(term @ Term::App { .. }) => Some(UnitRef::Ctor { term: term.clone() }),
    };

    // --- Dispatch on the (assoc, comm) shape ---
    match (assoc, comm) {
        // AC family: assoc + comm, variadic (1 declared arg sort).
        (true, true) => {
            if args.len() != 1 {
                return Err(serr(
                    ":assoc :comm operator takes one argument sort",
                    Span::Dummy,
                ));
            }
            // Partition is derived from the clamp (design "storage partition and clamp are
            // independent"): idempotent → Set (dedup is the sound build canonize); plain AC and
            // nilpotent → MSet (nilpotent keeps true multiplicities for the completion-time mod-n
            // reduction — the Set dedup canonize would destroy them at build).
            let kind = if idempotent {
                OpKind::Set {
                    arg_sort: args[0],
                    clamp: Clamp::Idempotent,
                    identity: unit_ref,
                    cancellative,
                }
            } else {
                OpKind::MSet {
                    arg_sort: args[0],
                    clamp: match nilpotent {
                        Some(order) => Clamp::Nilpotent { order },
                        None => Clamp::None,
                    },
                    identity: unit_ref,
                    cancellative,
                }
            };
            let op = eg.register_kind(name, ret, kind);
            // Resolve `:identity e` to a real node NOW (sortcheck has the model to parse the
            // term; the node id is stored in the egraph's per-op unit map — `OpKind<S>` cannot
            // carry a `Cfg::G`). The unit must sort-check to the op's return sort and be a
            // ground term (a literal or a constructor over ground args), so its constructors
            // must already be declared. Stored on the egraph, rolls back with the op decl.
            if let Some(term) = &identity {
                let ct = check_term(term, Some(ret), eg.ops(), eg.sorts(), model, globals)
                    .map_err(|e| {
                        serr(
                            format!(":identity term does not sort-check: {e}"),
                            Span::Dummy,
                        )
                    })?;
                let unit = eg.build_ground_cterm(&ct);
                eg.set_unit_node(op, unit);
            }
            // Resolve `:inverse neg` to a real op id now (it must be declared before this
            // op, like the identity's constructors) and validate the group-inverse
            // signature `neg : ret -> ret`. Stored in the egraph's per-op inverse map
            // (same persistence as the unit map).
            if let Some(inv_name) = &inverse {
                let inv_op = eg.ops().id_by_name(inv_name).ok_or_else(|| {
                    serr(
                        format!(":inverse operator '{inv_name}' is not declared"),
                        Span::Dummy,
                    )
                })?;
                let info = eg.ops().info(inv_op);
                let sig_ok = matches!(
                    &info.kind,
                    OpKind::Normal { arg_sorts } if arg_sorts.as_slice() == [ret]
                ) && info.return_sort == ret;
                if !sig_ok {
                    return Err(serr(
                        format!(
                            ":inverse operator '{inv_name}' must be unary over the op's \
                             sort (inv : S -> S)"
                        ),
                        Span::Dummy,
                    ));
                }
                eg.set_inverse_op(op, inv_op);
            }
            Ok(op)
        }
        // Associative-only (A): a sequence op; no comm/idempotent/nilpotent/identity semantics.
        (true, false) => {
            if idempotent || nilpotent.is_some() || identity.is_some() || inverse.is_some() {
                return Err(serr(
                    ":idempotent/:nilpotent/:identity/:inverse require :comm (an AC operator)",
                    Span::Dummy,
                ));
            }
            if args.len() != 1 {
                return Err(serr(":assoc requires 1 argument sort", Span::Dummy));
            }
            Ok(eg.register_a(name, args[0], ret, dir.unwrap_or(AssocDir::Left)))
        }
        // Commutative-only (C): binary.
        (false, true) => {
            if idempotent || nilpotent.is_some() || identity.is_some() || inverse.is_some() {
                return Err(serr(
                    ":idempotent/:nilpotent/:identity/:inverse require :assoc (an AC operator)",
                    Span::Dummy,
                ));
            }
            if args.len() != 2 {
                return Err(serr(":comm requires 2 argument sorts", Span::Dummy));
            }
            Ok(eg.register_c(name, [args[0], args[1]], ret))
        }
        // No structural tag but property tags present → error (idempotent-only etc. is meaningless).
        (false, false) => Err(serr(
            "algebra tags require :assoc and/or :comm",
            Span::Dummy,
        )),
    }
}
