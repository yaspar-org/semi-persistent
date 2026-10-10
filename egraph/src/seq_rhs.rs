// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The right-hand side, `:let`, and `:when` of a sequence rule, resolved against the
//! rule's [`MatchShape`] and evaluated against a [`Match`](crate::ematch::Match)
//! (`doc/sequence-patterns.md`, Typing; engine design §7.6).
//!
//! The surface language is the ordinary right-hand side (`ast::RhsTerm`), with the
//! sequence forms: element comprehensions over a filter (`..{ body for g in gs }`,
//! which rebinds the filter's pattern variables as scalars per element), tuple
//! comprehensions over a primitive's rows (`..{ body for (q a b) in (union-by p l u) }`),
//! reductions (`count`, `min`, `max`, `sum`), primitives applied element-wise, `if`,
//! and the sequence primitives `union-by`, `narrow`, `narrowed`, `zip`, `concat`.
//!
//! **Typing** (the depth rule). A filter's pattern variables are scalars inside the
//! pattern and sequences outside it; a sequence is consumed only by a reduction, an
//! element-wise primitive, a splice, or a comprehension, and anywhere else is the
//! error "a sequence used as a scalar". Inside a comprehension the binders are
//! scalars again.
//!
//! **Evaluation** is at application time: the match is read-only, and `:let`,
//! `:when`, and the right-hand side compute literal values (which are interned only
//! when a literal node is built). A reduction with no value (`min` of an empty
//! sequence) and a right-hand side with no value (an A application of nothing, an AC
//! or ACI one without an identity) do not fire; an undefined primitive (an overflow)
//! is an error, as it is for ordinary rules.
//!
//! The resolved form is separate from `resolve::RRhsTerm` because a sequence rule's
//! right-hand side needs literal locals, reductions, element-wise primitives, `if`,
//! `:let`, and guards evaluated at application time, none of which an ordinary rule
//! has; both read the same `Match`.

use crate::apply::{Children, mult_overflow_error};
use crate::ast::{BinderMult, GlobalVarId, LitValVarId, MultVarId, RhsChild, RhsTerm, Span, VarId};
use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::ematch::MatchView;
use crate::lit_model::LitModel;
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;
use crate::registry::{OpKind, OpRegistry, SortRegistry};
use crate::resolve::{ColRef, GlobalCtx, MatchShape, RestRef};
use std::collections::HashMap;

type R<T> = Result<T, (String, Span)>;

/// A reduction over a sequence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reduction {
    Count,
    Min,
    Max,
    Sum,
}

/// A local of a comprehension, by kind and index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SLocal {
    Node(usize),
    Lit(usize),
    Mult(usize),
}

/// A literal-valued expression.
#[derive(Clone, Debug)]
pub enum SScalar<L> {
    Const(L),
    QueryLit(LitValVarId),
    QueryMult(MultVarId),
    Local(SLocal),
    Let(usize),
    /// A literal primitive, by its index in the model's primitive table.
    Prim {
        prim: usize,
        args: Vec<SScalar<L>>,
    },
    /// A reduction; `prim` is the model primitive combining two elements (`min`,
    /// `max`, `+`), none for `count`.
    Reduce {
        red: Reduction,
        prim: Option<usize>,
        arg: Box<SSeq<L>>,
    },
    /// `(count (zip ..))` and the like: the number of rows of a sequence primitive.
    CountRows(Box<SRows<L>>),
}

/// A multiplicity expression, evaluated natively with checked `u64` arithmetic (as
/// `resolve::ResolvedMultExpr` is): a count is never read back from a literal.
#[derive(Clone, Debug)]
pub enum SMult {
    Lit(u64),
    Query(MultVarId),
    Local(usize),
    Prim { op: MultOp, args: Vec<SMult> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MultOp {
    Add,
    Sub,
    Mul,
    Min,
    Max,
}

/// A node reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SNode {
    Query(VarId),
    Local(usize),
}

/// A sequence-valued expression.
#[derive(Clone, Debug)]
pub enum SSeq<L> {
    Col(ColRef),
    Children(RestRef),
    /// A primitive applied per element; at least one argument is a sequence.
    Map {
        prim: usize,
        args: Vec<SSeqArg<L>>,
    },
}

#[derive(Clone, Debug)]
pub enum SSeqArg<L> {
    Seq(SSeq<L>),
    Scalar(SScalar<L>),
}

/// A term.
#[derive(Clone, Debug)]
pub enum STerm<O, L> {
    Node(SNode),
    Global(GlobalVarId),
    /// A literal node of sort-operator `op` whose value is `val`.
    Lit {
        op: O,
        val: SScalar<L>,
    },
    App {
        op: O,
        children: Vec<SChild<O, L>>,
    },
    If {
        cond: SScalar<L>,
        then: Box<STerm<O, L>>,
        els: Box<STerm<O, L>>,
    },
}

/// Where a comprehension's rows come from.
#[derive(Clone, Debug)]
pub enum SRows<L> {
    /// A filter's elements: the child and its columns, per element.
    Filter(usize),
    /// A rest's children.
    Rest(RestRef),
    Zip(Vec<SSeq<L>>),
    Concat(Vec<SSeq<L>>),
    UnionBy(Box<[SSeq<L>; 3]>),
    Narrow(Box<[SSeq<L>; 6]>, bool),
}

/// A binder: where each element of a row goes. `NodeMult` binds a child and its
/// multiplicity.
#[derive(Clone, Copy, Debug)]
pub enum SBinder {
    Node(usize),
    NodeMult(usize, usize),
    Lit(usize),
    Mult(usize),
}

#[derive(Clone, Debug)]
pub enum SChild<O, L> {
    One(STerm<O, L>),
    /// `term:mult`.
    OneMult(STerm<O, L>, SMult),
    Splice(RestRef),
    Comp {
        body: STerm<O, L>,
        mult: Option<SMult>,
        rows: SRows<L>,
        binders: Vec<SBinder>,
        guard: Option<SScalar<L>>,
    },
}

/// A sequence rule's resolved right-hand side, lets, and guards.
#[derive(Clone, Debug)]
pub struct SeqRhs<O, L> {
    pub rhs: STerm<O, L>,
    pub lets: Vec<SScalar<L>>,
    pub whens: Vec<SScalar<L>>,
    pub locals: (usize, usize, usize),
    /// What the rule does that its text leaves implicit, one line each: a splice
    /// across kinds ("§Edge cases 3") and how it converts.
    pub plan: Vec<String>,
    /// Constructs whose result depends on class ids ("§Edge cases 7"): a zip across
    /// filters under AC or ACI, unordered children into an ordered operator.
    pub warnings: Vec<String>,
}

// ── Types ───────────────────────────────────────────────────────────────────

/// The type of a name or an expression during resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty<S> {
    /// A class of sort `S`.
    Node(S),
    /// A literal of literal sort `S`.
    Lit(S),
    /// A sequence of classes; `true` when the children carry multiplicities (AC).
    SeqNode(S, bool),
    SeqLit(S),
}

fn sequence_as_scalar() -> String {
    "a sequence used as a scalar: use it inside a reduction (min, max, sum, count) or a comprehension".into()
}

struct Resolver<'a, O: DenseId, S: DenseId, L, M: LitModel<Value = L>, const TRACK: bool> {
    ops: &'a OpRegistry<O, S, TRACK>,
    sorts: &'a SortRegistry<S, TRACK>,
    model: &'a M,
    globals: &'a GlobalCtx<S>,
    shape: &'a MatchShape,
    /// Sorts of query node and literal variables by name, and of rest sequences.
    node_sorts: &'a HashMap<String, S>,
    lit_sorts: &'a HashMap<String, S>,
    rest_sorts: &'a HashMap<String, S>,
    /// Column element sorts by name.
    col_sorts: &'a HashMap<String, S>,
    i64_sort: S,
    bool_sort: S,
    scopes: Vec<HashMap<String, (SLocal, Ty<S>)>>,
    counts: (usize, usize, usize),
    lets: Vec<(String, S)>,
    plan: Vec<String>,
    warnings: Vec<String>,
}

/// The kind of a sequence of children, by its pool.
fn rest_kind(r: RestRef) -> &'static str {
    match r {
        RestRef::Seq(_) => "A",
        RestRef::Set(_) => "ACI",
        RestRef::Mset(_) => "AC",
    }
}

fn op_kind_name<S: DenseId>(k: &OpKind<S>) -> &'static str {
    match k {
        OpKind::A { .. } => "A",
        OpKind::Set { .. } => "ACI",
        _ => "AC",
    }
}

impl<
    'a,
    O: DenseId + std::hash::Hash + Copy,
    S: DenseId + Copy + std::fmt::Debug,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
> Resolver<'a, O, S, L, M, TRACK>
{
    fn sort_name(&self, s: S) -> String {
        self.sorts.name(s).to_string()
    }

    fn rest_sort(&self, name: &str, span: Span) -> R<S> {
        self.rest_sorts
            .get(name)
            .copied()
            .ok_or_else(|| (format!("'{name}' is not a sequence of children"), span))
    }

    fn col_sort(&self, name: &str, span: Span) -> R<S> {
        self.col_sorts
            .get(name)
            .copied()
            .ok_or_else(|| (format!("'{name}' is not a filter's column"), span))
    }

    fn local(&self, name: &str) -> Option<(SLocal, Ty<S>)> {
        self.scopes
            .iter()
            .rev()
            .find_map(|sc| sc.get(name).cloned())
    }

    fn alloc(&mut self, name: &str, ty: Ty<S>, span: Span) -> R<SLocal> {
        let local = match &ty {
            Ty::Node(_) => {
                self.counts.0 += 1;
                SLocal::Node(self.counts.0 - 1)
            }
            Ty::Lit(_) => {
                self.counts.1 += 1;
                SLocal::Lit(self.counts.1 - 1)
            }
            _ => {
                return Err((
                    format!("a comprehension binder '{name}' of a sequence type"),
                    span,
                ));
            }
        };
        let scope = self.scopes.last_mut().ok_or_else(|| {
            (
                "internal: a binder outside a comprehension".to_string(),
                span,
            )
        })?;
        if scope.insert(name.to_string(), (local, ty)).is_some() {
            return Err((
                format!("comprehension binding '{name}' is declared twice"),
                span,
            ));
        }
        Ok(local)
    }

    fn alloc_mult(&mut self, name: &str, span: Span) -> R<SLocal> {
        self.counts.2 += 1;
        let local = SLocal::Mult(self.counts.2 - 1);
        let scope = self.scopes.last_mut().ok_or_else(|| {
            (
                "internal: a binder outside a comprehension".to_string(),
                span,
            )
        })?;
        if scope
            .insert(name.to_string(), (local, Ty::Lit(self.i64_sort)))
            .is_some()
        {
            return Err((
                format!("comprehension binding '{name}' is declared twice"),
                span,
            ));
        }
        Ok(local)
    }

    /// A model primitive by surface name, resolved as a sequence rule reads it: the
    /// name qualified by the first argument's sort (`i64::+` for `+`), then the name.
    fn prim(&self, name: &str, first: Option<S>, span: Span) -> R<(usize, Vec<String>, String)> {
        let qualified = first.map(|s| format!("{}::{name}", self.sort_name(s)));
        let ops = self.model.ops();
        let find = |n: &str| ops.iter().position(|d| d.name == n);
        let i = qualified
            .as_deref()
            .and_then(find)
            .or_else(|| find(name))
            .ok_or_else(|| (format!("unknown operator or primitive '{name}'"), span))?;
        let d = &ops[i];
        Ok((
            i,
            d.arg_sorts.iter().map(|s| s.to_string()).collect(),
            d.ret_sort.to_string(),
        ))
    }

    fn sort_by_name(&self, name: &str, span: Span) -> R<S> {
        self.sorts
            .id_by_name(name)
            .ok_or_else(|| (format!("unknown sort '{name}'"), span))
    }

    /// The type of a name.
    fn name_ty(&self, name: &str, span: Span) -> R<Ty<S>> {
        if let Some((_, t)) = self.local(name) {
            return Ok(t);
        }
        if let Some((_, s)) = self.lets.iter().find(|(n, _)| n == name) {
            return Ok(Ty::Lit(*s));
        }
        if let Some(fi) = self.shape.find_filter(name) {
            let s = self.rest_sort(name, span)?;
            return Ok(Ty::SeqNode(
                s,
                matches!(self.shape.filters[fi].elems, RestRef::Mset(_)),
            ));
        }
        if let Some((_, col)) = self.shape.find_column(name) {
            let s = self.col_sort(name, span)?;
            return Ok(match col {
                ColRef::Node(_) => Ty::SeqNode(s, false),
                ColRef::Lit(_) | ColRef::Mult(_) => Ty::SeqLit(s),
            });
        }
        if let Some(s) = self.rest_sorts.get(name) {
            let mset = self.shape.find_mset(name).is_some();
            return Ok(Ty::SeqNode(*s, mset));
        }
        if let Some(s) = self.node_sorts.get(name) {
            return Ok(Ty::Node(*s));
        }
        if let Some(s) = self.lit_sorts.get(name) {
            return Ok(Ty::Lit(*s));
        }
        if self.shape.find_mult(name).is_some() {
            return Ok(Ty::Lit(self.i64_sort));
        }
        if let Some((_, gs, _)) = self.globals.get(name) {
            return Ok(if self.ops.lit_op_for_sort(gs).is_some() {
                Ty::Lit(gs)
            } else {
                Ty::Node(gs)
            });
        }
        Err((format!("unbound variable '{name}'"), span))
    }

    /// A sequence of children: a filter or a rest. A filter's node column is in the
    /// same pool as the rests (`seq_pool`) but is not one.
    fn rest_ref(&self, name: &str) -> Option<RestRef> {
        if let Some(fi) = self.shape.find_filter(name) {
            return Some(self.shape.filters[fi].elems);
        }
        if self.shape.find_column(name).is_some() {
            return None;
        }
        self.shape
            .find_seq(name)
            .map(RestRef::Seq)
            .or_else(|| self.shape.find_set(name).map(RestRef::Set))
            .or_else(|| self.shape.find_mset(name).map(RestRef::Mset))
    }

    /// Resolve a literal-valued expression of sort `want` (when given).
    fn scalar(&mut self, t: &RhsTerm, want: Option<S>) -> R<(SScalar<L>, S)> {
        let span = t.span();
        let check = |got: S, this: &Self| -> R<()> {
            match want {
                Some(w) if w != got => Err((
                    format!(
                        "an expression of sort '{}' where '{}' is expected",
                        this.sort_name(got),
                        this.sort_name(w)
                    ),
                    span,
                )),
                _ => Ok(()),
            }
        };
        match t {
            RhsTerm::Lit(text, _) => {
                let v = match want {
                    Some(w) => {
                        let v = self
                            .model
                            .parse_as(&self.sort_name(w), text.trim_matches('"'))
                            .ok_or_else(|| {
                                (
                                    format!(
                                        "'{text}' is not a literal of sort '{}'",
                                        self.sort_name(w)
                                    ),
                                    span,
                                )
                            })?;
                        (v, w)
                    }
                    None => {
                        let (so, v) = if text.starts_with('"') {
                            (
                                "String",
                                self.model
                                    .parse_as("String", text.trim_matches('"'))
                                    .ok_or_else(|| (format!("cannot read '{text}'"), span))?,
                            )
                        } else {
                            self.model
                                .parse_any(text)
                                .ok_or_else(|| (format!("cannot read literal '{text}'"), span))?
                        };
                        (v, self.sort_by_name(so, span)?)
                    }
                };
                Ok((SScalar::Const(v.0), v.1))
            }
            RhsTerm::Var(name, _) => {
                let ty = self.name_ty(name, span)?;
                let Ty::Lit(s) = ty else {
                    return Err(match ty {
                        Ty::Node(s) => (
                            format!(
                                "'{name}' is a class of sort '{}', not a literal",
                                self.sort_name(s)
                            ),
                            span,
                        ),
                        _ => (sequence_as_scalar(), span),
                    });
                };
                check(s, self)?;
                if let Some((l, _)) = self.local(name) {
                    return Ok((SScalar::Local(l), s));
                }
                if let Some(i) = self.lets.iter().position(|(n, _)| n == name) {
                    return Ok((SScalar::Let(i), s));
                }
                if let Some(v) = self.shape.find_lit_val(name) {
                    return Ok((SScalar::QueryLit(v), s));
                }
                if let Some(m) = self.shape.find_mult(name) {
                    return Ok((SScalar::QueryMult(m), s));
                }
                if self.globals.get(name).is_some() {
                    return Err((
                        format!("the literal global '{name}' is not readable as a value here"),
                        span,
                    ));
                }
                Err((format!("'{name}' is not a literal value"), span))
            }
            RhsTerm::App { op, children, .. } => {
                let exprs = self.plain_args(op, children, span)?;
                if let Some(red) = reduction(op) {
                    return self.reduce(red, &exprs, want, span);
                }
                if op == "if" {
                    return Err(("an `if` whose branches are literals is not supported; write the literal operator around it".into(), span));
                }
                // A literal primitive, resolved by its first argument's sort.
                let first = match exprs.first() {
                    Some(e) => Some(self.infer_sort(e)?),
                    None => None,
                };
                let (prim, arg_sorts, ret) = self.prim(op, first, span)?;
                if arg_sorts.len() != exprs.len() {
                    return Err((
                        format!(
                            "'{op}' takes {} arguments, not {}",
                            arg_sorts.len(),
                            exprs.len()
                        ),
                        span,
                    ));
                }
                let mut args = Vec::with_capacity(exprs.len());
                for (e, so) in exprs.iter().zip(&arg_sorts) {
                    let s = self.sort_by_name(so, e.span())?;
                    args.push(self.scalar(e, Some(s))?.0);
                }
                let r = self.sort_by_name(&ret, span)?;
                check(r, self)?;
                Ok((SScalar::Prim { prim, args }, r))
            }
        }
    }

    /// The sort a scalar expression would have, without resolving it.
    fn infer_sort(&mut self, t: &RhsTerm) -> R<S> {
        match t {
            RhsTerm::Lit(text, s) => {
                let so = if text.starts_with('"') {
                    "String"
                } else {
                    self.model
                        .parse_any(text)
                        .map(|(so, _)| so)
                        .ok_or_else(|| (format!("cannot read literal '{text}'"), *s))?
                };
                self.sort_by_name(so, *s)
            }
            RhsTerm::Var(name, s) => match self.name_ty(name, *s)? {
                Ty::Lit(x) | Ty::Node(x) | Ty::SeqLit(x) | Ty::SeqNode(x, _) => Ok(x),
            },
            RhsTerm::App { op, children, span } => {
                if let Some(red) = reduction(op) {
                    if red == Reduction::Count {
                        return Ok(self.i64_sort);
                    }
                    let exprs = self.plain_args(op, children, *span)?;
                    return match exprs.first() {
                        Some(e) => self.infer_sort(e),
                        None => Err((format!("'{op}' takes one sequence"), *span)),
                    };
                }
                let exprs = self.plain_args(op, children, *span)?;
                let first = match exprs.first() {
                    Some(e) => Some(self.infer_sort(e)?),
                    None => None,
                };
                if let Ok((_, _, ret)) = self.prim(op, first, *span) {
                    return self.sort_by_name(&ret, *span);
                }
                let (_, info) = self.op(op, *span)?;
                Ok(info.return_sort)
            }
        }
    }

    fn plain_args<'t>(
        &self,
        op: &str,
        children: &'t [RhsChild],
        span: Span,
    ) -> R<Vec<&'t RhsTerm>> {
        children
            .iter()
            .map(|c| match c {
                RhsChild::Term(t) => Ok(t),
                _ => Err((format!("'{op}' takes no spliced arguments"), span)),
            })
            .collect()
    }

    fn op(&self, name: &str, span: Span) -> R<(O, crate::registry::OpInfo<S>)> {
        let o = self
            .ops
            .id_by_name(name)
            .ok_or_else(|| (format!("unknown operator or primitive '{name}'"), span))?;
        Ok((o, self.ops.info(o).clone()))
    }

    fn reduce(
        &mut self,
        red: Reduction,
        exprs: &[&RhsTerm],
        want: Option<S>,
        span: Span,
    ) -> R<(SScalar<L>, S)> {
        let [arg] = exprs else {
            return Err((
                format!("a reduction takes one sequence, not {}", exprs.len()),
                span,
            ));
        };
        if let RhsTerm::App { op, .. } = arg
            && is_rows_prim(op)
        {
            if red != Reduction::Count {
                return Err((format!("'{op}' has rows, which only count reduces"), span));
            }
            let (rows, _, _) = self.rows(arg)?;
            return self.want_sort(
                SScalar::CountRows(Box::new(rows)),
                self.i64_sort,
                want,
                span,
            );
        }
        let (seq, elem) = self.seq(arg)?;
        let (prim, ret) = match red {
            Reduction::Count => (None, self.i64_sort),
            _ => {
                let Ty::Lit(s) = elem else {
                    return Err(("min, max, and sum reduce literals".into(), span));
                };
                let name = match red {
                    Reduction::Min => "min",
                    Reduction::Max => "max",
                    _ => "+",
                };
                let (p, _, _) = self.prim(name, Some(s), span)?;
                (Some(p), s)
            }
        };
        self.want_sort(
            SScalar::Reduce {
                red,
                prim,
                arg: Box::new(seq),
            },
            ret,
            want,
            span,
        )
    }

    fn want_sort(&self, s: SScalar<L>, ret: S, want: Option<S>, span: Span) -> R<(SScalar<L>, S)> {
        if let Some(w) = want
            && w != ret
        {
            return Err((
                format!(
                    "a reduction of sort '{}' where '{}' is expected",
                    self.sort_name(ret),
                    self.sort_name(w)
                ),
                span,
            ));
        }
        Ok((s, ret))
    }

    /// The sequences of children an expression's elements come from: a filter's for
    /// its columns, the rest's for itself.
    fn origins(&self, q: &SSeq<L>, out: &mut Vec<RestRef>) {
        let mut add = |r: RestRef| {
            if !out.contains(&r) {
                out.push(r);
            }
        };
        match q {
            SSeq::Children(r) => add(*r),
            SSeq::Col(c) => {
                if let Some(f) = self
                    .shape
                    .filters
                    .iter()
                    .find(|f| f.cols.iter().any(|(_, x)| x == c))
                {
                    add(f.elems);
                }
            }
            SSeq::Map { args, .. } => {
                for a in args {
                    if let SSeqArg::Seq(s) = a {
                        self.origins(s, out);
                    }
                }
            }
        }
    }

    /// Resolve a sequence primitive's rows: the rows, each column's element type, and
    /// whether the column carries multiplicities (a column of AC children).
    fn rows(&mut self, source: &RhsTerm) -> R<(SRows<L>, Vec<Ty<S>>, Vec<bool>)> {
        let span = source.span();
        let RhsTerm::App {
            op,
            children,
            span: ss,
        } = source
        else {
            return Err((
                "a comprehension source is a sequence or a sequence primitive".into(),
                span,
            ));
        };
        let exprs = self.plain_args(op, children, *ss)?;
        let mut seqs = Vec::with_capacity(exprs.len());
        let mut elems = Vec::with_capacity(exprs.len());
        let mut msets = Vec::with_capacity(exprs.len());
        for e in &exprs {
            let (sq, el) = self.seq(e)?;
            msets.push(matches!(sq, SSeq::Children(RestRef::Mset(_))));
            seqs.push(sq);
            elems.push(el);
        }
        if op == "zip" {
            let mut origins: Vec<RestRef> = Vec::new();
            for q in &seqs {
                self.origins(q, &mut origins);
            }
            origins.dedup();
            if origins.len() > 1 && origins.iter().any(|r| !matches!(r, RestRef::Seq(_))) {
                let names: Vec<String> = origins.iter().map(|r| self.rest_name(*r)).collect();
                self.warnings.push(format!(
                    "zip across {} pairs AC or ACI children by class id, which is not a function of the e-graph's contents",
                    names.join(" and ")
                ));
            }
        }
        let (rows, row_tys): (SRows<L>, Vec<Ty<S>>) = match op.as_str() {
            "zip" => (SRows::Zip(seqs), elems.clone()),
            "concat" => {
                let first = elems
                    .first()
                    .cloned()
                    .ok_or_else(|| ("concat takes sequences".to_string(), *ss))?;
                if elems.iter().any(|e| *e != first) {
                    return Err(("concat takes sequences of one element type".into(), *ss));
                }
                (SRows::Concat(seqs), vec![first])
            }
            "union-by" => {
                let [p, l, u]: [SSeq<L>; 3] = seqs
                    .try_into()
                    .map_err(|_| ("union-by takes 3 sequences".to_string(), *ss))?;
                (
                    SRows::UnionBy(Box::new([p, l, u])),
                    vec![elems[0].clone(), elems[1].clone(), elems[2].clone()],
                )
            }
            "narrow" | "narrowed" => {
                let n = elems.len();
                let six: [SSeq<L>; 6] = seqs
                    .try_into()
                    .map_err(|_| (format!("{op} takes 6 sequences, not {n}"), *ss))?;
                (
                    SRows::Narrow(Box::new(six), op == "narrowed"),
                    vec![elems[2].clone(), elems[0].clone(), elems[1].clone()],
                )
            }
            other => return Err((format!("'{other}' is not a sequence primitive"), *ss)),
        };
        let from_mset: Vec<bool> = match &rows {
            SRows::Zip(_) => msets,
            SRows::Concat(_) => vec![msets.iter().any(|m| *m)],
            _ => vec![false; row_tys.len()],
        };
        Ok((rows, row_tys, from_mset))
    }

    /// Resolve a sequence-valued expression; returns it and its element type.
    fn seq(&mut self, t: &RhsTerm) -> R<(SSeq<L>, Ty<S>)> {
        let span = t.span();
        match t {
            RhsTerm::Var(name, _) => {
                if self.local(name).is_some() {
                    return Err((format!("'{name}' is a scalar here, not a sequence"), span));
                }
                if let Some((_, col)) = self.shape.find_column(name) {
                    let s = self.col_sort(name, span)?;
                    return Ok((
                        SSeq::Col(col),
                        match col {
                            ColRef::Node(_) => Ty::Node(s),
                            _ => Ty::Lit(s),
                        },
                    ));
                }
                if let Some(r) = self.rest_ref(name) {
                    let s = self.rest_sort(name, span)?;
                    return Ok((SSeq::Children(r), Ty::Node(s)));
                }
                Err((format!("'{name}' is not a sequence"), span))
            }
            RhsTerm::App { op, children, .. } => {
                // A literal primitive applied element-wise: at least one sequence.
                let exprs = self.plain_args(op, children, span)?;
                let first = match exprs.first() {
                    Some(e) => Some(self.infer_sort(e)?),
                    None => None,
                };
                let (prim, arg_sorts, ret) = self.prim(op, first, span)?;
                if arg_sorts.len() != exprs.len() {
                    return Err((
                        format!(
                            "'{op}' takes {} arguments, not {}",
                            arg_sorts.len(),
                            exprs.len()
                        ),
                        span,
                    ));
                }
                let mut args = Vec::with_capacity(exprs.len());
                let mut any_seq = false;
                for (e, so) in exprs.iter().zip(&arg_sorts) {
                    let want = self.sort_by_name(so, e.span())?;
                    if self.is_seq(e) {
                        let (sq, el) = self.seq(e)?;
                        if el != Ty::Lit(want) {
                            return Err((
                                format!(
                                    "an element of the wrong sort for '{op}', which expects '{so}'"
                                ),
                                e.span(),
                            ));
                        }
                        args.push(SSeqArg::Seq(sq));
                        any_seq = true;
                    } else {
                        args.push(SSeqArg::Scalar(self.scalar(e, Some(want))?.0));
                    }
                }
                if !any_seq {
                    return Err((
                        format!(
                            "'{op}' has no sequence argument here, where a sequence is expected"
                        ),
                        span,
                    ));
                }
                Ok((
                    SSeq::Map { prim, args },
                    Ty::Lit(self.sort_by_name(&ret, span)?),
                ))
            }
            RhsTerm::Lit(..) => Err(("a literal where a sequence is expected".into(), span)),
        }
    }

    /// Whether an expression denotes a sequence (a column, a rest, or a primitive over
    /// one).
    fn is_seq(&self, t: &RhsTerm) -> bool {
        match t {
            RhsTerm::Var(name, _) => {
                self.local(name).is_none()
                    && (self.shape.find_column(name).is_some() || self.rest_ref(name).is_some())
            }
            RhsTerm::App { op, children, .. } => {
                reduction(op).is_none()
                    && op != "if"
                    && self
                        .ops
                        .id_by_name(op)
                        .is_none_or(|o| self.ops.is_prim_op(o))
                    && children
                        .iter()
                        .any(|c| matches!(c, RhsChild::Term(t) if self.is_seq(t)))
            }
            RhsTerm::Lit(..) => false,
        }
    }

    /// Resolve a term of sort `want`.
    fn term(&mut self, t: &RhsTerm, want: S) -> R<STerm<O, L>> {
        let span = t.span();
        if let Some(lit_op) = self.ops.lit_op_for_sort(want) {
            // A literal position: any literal-valued expression.
            let (val, _) = self.scalar(t, Some(want))?;
            return Ok(STerm::Lit { op: lit_op, val });
        }
        match t {
            RhsTerm::Lit(..) => Err((
                format!(
                    "a literal where a term of sort '{}' is expected",
                    self.sort_name(want)
                ),
                span,
            )),
            RhsTerm::Var(name, _) => {
                let ty = self.name_ty(name, span)?;
                match ty {
                    Ty::Node(s) if s == want => {}
                    Ty::Node(s) => {
                        return Err((
                            format!(
                                "'{name}' has sort '{}' where '{}' is expected",
                                self.sort_name(s),
                                self.sort_name(want)
                            ),
                            span,
                        ));
                    }
                    _ => return Err((sequence_as_scalar(), span)),
                }
                if let Some((SLocal::Node(i), _)) = self.local(name) {
                    return Ok(STerm::Node(SNode::Local(i)));
                }
                if let Some(v) = self.shape.find_var(name) {
                    return Ok(STerm::Node(SNode::Query(v)));
                }
                if let Some((gid, _, _)) = self.globals.get(name) {
                    return Ok(STerm::Global(gid));
                }
                Err((format!("unbound variable '{name}'"), span))
            }
            RhsTerm::App { op, children, .. } => {
                if op == "if" {
                    let exprs = self.plain_args(op, children, span)?;
                    let [c, a, b] = exprs.as_slice() else {
                        return Err(("(if cond then else)".into(), span));
                    };
                    let (cond, _) = self.scalar(c, Some(self.bool_sort))?;
                    let then = self.term(a, want)?;
                    let els = self.term(b, want)?;
                    return Ok(STerm::If {
                        cond,
                        then: Box::new(then),
                        els: Box::new(els),
                    });
                }
                let (o, info) = self.op(op, span)?;
                if info.return_sort != want {
                    return Err((
                        format!(
                            "the right-hand side has sort '{}'; the position expects '{}'",
                            self.sort_name(info.return_sort),
                            self.sort_name(want)
                        ),
                        span,
                    ));
                }
                let mut out = Vec::with_capacity(children.len());
                match &info.kind {
                    OpKind::Normal { arg_sorts } => {
                        let exprs = self.plain_args(op, children, span)?;
                        if exprs.len() != arg_sorts.len() {
                            return Err((
                                format!(
                                    "'{op}' takes {} arguments, not {}",
                                    arg_sorts.len(),
                                    exprs.len()
                                ),
                                span,
                            ));
                        }
                        for (e, &s) in exprs.iter().zip(arg_sorts) {
                            out.push(SChild::One(self.term(e, s)?));
                        }
                    }
                    OpKind::Commutative { arg_sorts } => {
                        let exprs = self.plain_args(op, children, span)?;
                        if exprs.len() != 2 {
                            return Err((format!("'{op}' takes 2 arguments"), span));
                        }
                        for (e, &s) in exprs.iter().zip(arg_sorts) {
                            out.push(SChild::One(self.term(e, s)?));
                        }
                    }
                    OpKind::A { arg_sort, .. }
                    | OpKind::MSet { arg_sort, .. }
                    | OpKind::Set { arg_sort, .. } => {
                        let ordered = matches!(info.kind, OpKind::A { .. });
                        for c in children {
                            comp_bracket(c, ordered, op)?;
                            let ch = self.child(c, *arg_sort)?;
                            self.note_kinds(&ch, op, &info.kind);
                            out.push(ch);
                        }
                    }
                    OpKind::Lit => return Err((format!("'{op}' is a literal operator"), span)),
                }
                Ok(STerm::App {
                    op: o,
                    children: out,
                })
            }
        }
    }

    /// Record a splice across kinds ("§Edge cases 3") in the plan, and warn where
    /// unordered children enter an ordered operator: their order is the class ids'.
    fn note_kinds(&mut self, ch: &SChild<O, L>, op: &str, target: &OpKind<S>) {
        let to = op_kind_name(target);
        let from = match ch {
            SChild::Splice(r) => Some((*r, "..")),
            SChild::Comp {
                rows: SRows::Rest(r),
                ..
            } => Some((*r, "for over ")),
            SChild::Comp {
                rows: SRows::Filter(fi),
                ..
            } => Some((self.shape.filters[*fi].elems, "for over ")),
            SChild::Comp { rows, .. } => {
                let seqs: Vec<&SSeq<L>> = match rows {
                    SRows::Zip(q) | SRows::Concat(q) => q.iter().collect(),
                    SRows::UnionBy(q) => q.iter().collect(),
                    SRows::Narrow(q, _) => q.iter().collect(),
                    SRows::Filter(_) | SRows::Rest(_) => Vec::new(),
                };
                let mut origins = Vec::new();
                for q in seqs {
                    self.origins(q, &mut origins);
                }
                if to == "A" && origins.iter().any(|r| !matches!(r, RestRef::Seq(_))) {
                    self.warnings.push(format!(
                        "a comprehension puts rows of AC or ACI children under the associative '{op}' in class-id order, which is not a function of the e-graph's contents"
                    ));
                }
                None
            }
            _ => None,
        };
        let Some((r, how)) = from else { return };
        let fk = rest_kind(r);
        if fk == to {
            return;
        }
        let name = self.rest_name(r);
        let conv = match (fk, to) {
            ("AC", "A") if how == ".." => "each child repeated by its multiplicity",
            ("AC", "ACI") => "one copy of each child (idempotence)",
            (_, "AC") => "each child with multiplicity 1",
            ("A", "ACI") => "duplicates collapse",
            _ => "each element once",
        };
        self.plan
            .push(format!("{how}{name} into '{op}': {fk} into {to}, {conv}"));
        if to == "A" {
            self.warnings.push(format!(
                "{how}{name} puts {fk} children under the associative '{op}' in class-id order, which is not a function of the e-graph's contents"
            ));
        }
    }

    fn rest_name(&self, r: RestRef) -> String {
        if let Some(f) = self.shape.filters.iter().find(|f| f.elems == r) {
            return f.name.clone();
        }
        self.rest_sorts
            .keys()
            .find(|n| self.rest_ref(n) == Some(r))
            .cloned()
            .unwrap_or_default()
    }

    /// One child of a variadic application, of element sort `elem`.
    fn child(&mut self, c: &RhsChild, elem: S) -> R<SChild<O, L>> {
        match c {
            RhsChild::Term(t) => Ok(SChild::One(self.term(t, elem)?)),
            RhsChild::TermMult { term, mult, span } => {
                let body = self.term(term, elem)?;
                let m = self.mult_expr(mult, *span)?;
                Ok(SChild::OneMult(body, m))
            }
            RhsChild::Splice(name, span) => {
                if self.local(name).is_some() {
                    return Err((
                        format!("'{name}' is a comprehension binder, not a sequence"),
                        *span,
                    ));
                }
                let r = self.rest_ref(name).ok_or_else(|| {
                    if self.shape.find_column(name).is_some() {
                        (format!("..{name} splices a filter's column; splice the filter, or use a comprehension"), *span)
                    } else {
                        (format!("..{name} is not a sequence of children"), *span)
                    }
                })?;
                let s = self.rest_sort(name, *span)?;
                if s != elem {
                    return Err((
                        format!(
                            "..{name} splices '{}' into a position of '{}'",
                            self.sort_name(s),
                            self.sort_name(elem)
                        ),
                        *span,
                    ));
                }
                Ok(SChild::Splice(r))
            }
            RhsChild::SetComp {
                body,
                var,
                source,
                filter,
                span,
            }
            | RhsChild::SeqComp {
                body,
                var,
                source,
                filter,
                span,
            } => self.comp_over_name(
                body,
                None,
                &[(var.clone(), BinderMult::None)],
                source,
                filter,
                elem,
                *span,
            ),
            RhsChild::MsetComp {
                body,
                mult,
                var,
                mult_var,
                source,
                filter,
                span,
            } => {
                let m = Some(mult);
                self.comp_over_name(
                    body,
                    m,
                    &[(var.clone(), BinderMult::Var(mult_var.clone()))],
                    source,
                    filter,
                    elem,
                    *span,
                )
            }
            RhsChild::RowComp {
                body,
                mult,
                binders,
                source,
                filter,
                span,
                ..
            } => {
                if let RhsTerm::Var(name, _) = source.as_ref() {
                    return self.comp_over_name(
                        body,
                        mult.as_ref(),
                        binders,
                        name,
                        filter,
                        elem,
                        *span,
                    );
                }
                self.comp_over_rows(body, mult.as_ref(), binders, source, filter, elem, *span)
            }
        }
    }

    fn mult_expr(&mut self, m: &crate::ast::MultExpr, span: Span) -> R<SMult> {
        use crate::ast::MultExpr;
        match m {
            MultExpr::Lit(n) => Ok(SMult::Lit(*n)),
            MultExpr::Var(name) => {
                if let Some((SLocal::Mult(i), _)) = self.local(name) {
                    return Ok(SMult::Local(i));
                }
                if let Some(v) = self.shape.find_mult(name) {
                    return Ok(SMult::Query(v));
                }
                Err((format!("'{name}' is not a multiplicity"), span))
            }
            MultExpr::Prim { op, args } => {
                let op = match op.as_str() {
                    "u64::+" | "+" => MultOp::Add,
                    "u64::-" | "-" => MultOp::Sub,
                    "u64::*" | "*" => MultOp::Mul,
                    "u64::min" | "min" => MultOp::Min,
                    "u64::max" | "max" => MultOp::Max,
                    other => {
                        return Err((format!("'{other}' is not a multiplicity operator"), span));
                    }
                };
                let args = args
                    .iter()
                    .map(|a| self.mult_expr(a, span))
                    .collect::<R<Vec<_>>>()?;
                Ok(SMult::Prim { op, args })
            }
        }
    }

    /// A comprehension over a named sequence: a filter (its columns rebound per
    /// element), or a rest.
    #[allow(clippy::too_many_arguments)]
    fn comp_over_name(
        &mut self,
        body: &RhsTerm,
        mult: Option<&crate::ast::MultExpr>,
        binders: &[(String, BinderMult)],
        source: &str,
        filter: &Option<Box<RhsTerm>>,
        elem: S,
        span: Span,
    ) -> R<SChild<O, L>> {
        let [(var, bm)] = binders else {
            return Err((
                format!("a comprehension over '{source}' takes one binder; zip it for several"),
                span,
            ));
        };
        let r = self.rest_ref(source).ok_or_else(|| {
            if self.shape.find_column(source).is_some() {
                (
                    format!(
                        "'{source}' is a filter's column; iterate the filter, or zip its columns"
                    ),
                    span,
                )
            } else {
                (format!("'{source}' is not a sequence of children"), span)
            }
        })?;
        let s = self.rest_sort(source, span)?;
        let mset = matches!(r, RestRef::Mset(_));
        self.scopes.push(HashMap::new());
        let res = (|| {
            let mut out = Vec::new();
            let node = self.alloc(var, Ty::Node(s), span)?;
            let SLocal::Node(ni) = node else {
                return Err((format!("internal: {}", "a node binder"), span));
            };
            // The binder's multiplicity may be named as the filter's multiplicity column
            // (`for f:k in fs` over `(..fs:k P)`): both are the child's multiplicity.
            let mut binder_mult: Option<(&str, usize)> = None;
            match (bm, mset) {
                (BinderMult::Var(k), true) => {
                    let SLocal::Mult(mi) = self.alloc_mult(k, span)? else {
                        return Err((format!("internal: {}", "a multiplicity binder"), span));
                    };
                    out.push(SBinder::NodeMult(ni, mi));
                    binder_mult = Some((k.as_str(), mi));
                }
                (BinderMult::None, true) => {
                    return Err((
                        format!(
                            "'{source}' carries multiplicities: bind them as `{var}:k`, or drop them as `{var}:_`"
                        ),
                        span,
                    ));
                }
                (BinderMult::Var(_), false) => {
                    return Err((format!("'{source}' has no multiplicities to bind"), span));
                }
                _ => out.push(SBinder::Node(ni)),
            }
            let rows = match self.shape.find_filter(source) {
                Some(fi) => {
                    // "§Typing: Inside `..{ body for g in gs }` the pattern's variables are
                    // scalars again, bound to the element's values".
                    let cols = self.shape.filters[fi].cols.clone();
                    for (name, col) in cols {
                        let cs = self.col_sort(&name, span)?;
                        let b = match col {
                            ColRef::Node(_) => match self.alloc(&name, Ty::Node(cs), span)? {
                                SLocal::Node(i) => SBinder::Node(i),
                                _ => return Err((format!("internal: {}", "a node column"), span)),
                            },
                            ColRef::Lit(_) => match self.alloc(&name, Ty::Lit(cs), span)? {
                                SLocal::Lit(i) => SBinder::Lit(i),
                                _ => {
                                    return Err((
                                        format!("internal: {}", "a literal column"),
                                        span,
                                    ));
                                }
                            },
                            ColRef::Mult(_) => match binder_mult {
                                Some((k, mi)) if k == name => SBinder::Mult(mi),
                                _ => match self.alloc_mult(&name, span)? {
                                    SLocal::Mult(i) => SBinder::Mult(i),
                                    _ => {
                                        return Err((
                                            format!("internal: {}", "a multiplicity column"),
                                            span,
                                        ));
                                    }
                                },
                            },
                        };
                        out.push(b);
                    }
                    SRows::Filter(fi)
                }
                None => SRows::Rest(r),
            };
            self.finish_comp(body, mult, rows, out, filter, elem, span)
        })();
        self.scopes.pop();
        res
    }

    /// A comprehension over a primitive's rows: `zip`, `concat`, `union-by`,
    /// `narrow`, `narrowed`.
    #[allow(clippy::too_many_arguments)]
    fn comp_over_rows(
        &mut self,
        body: &RhsTerm,
        mult: Option<&crate::ast::MultExpr>,
        binders: &[(String, BinderMult)],
        source: &RhsTerm,
        filter: &Option<Box<RhsTerm>>,
        elem: S,
        span: Span,
    ) -> R<SChild<O, L>> {
        let (rows, row_tys, from_mset) = self.rows(source)?;
        if binders.len() != row_tys.len() {
            return Err((
                format!(
                    "a comprehension binding {} names needs a source of that width",
                    binders.len()
                ),
                span,
            ));
        }
        self.scopes.push(HashMap::new());
        let res = (|| {
            let mut out = Vec::new();
            for (((name, bm), ty), mset) in binders.iter().zip(&row_tys).zip(&from_mset) {
                let b = match (ty, bm, mset) {
                    (Ty::Node(_), BinderMult::Var(k), true) => {
                        let SLocal::Node(ni) = self.alloc(name, ty.clone(), span)? else {
                            return Err((format!("internal: {}", "a node binder"), span));
                        };
                        let SLocal::Mult(mi) = self.alloc_mult(k, span)? else {
                            return Err((format!("internal: {}", "a multiplicity binder"), span));
                        };
                        SBinder::NodeMult(ni, mi)
                    }
                    (Ty::Node(_), BinderMult::None, true) => {
                        return Err((
                            format!(
                                "the column bound to '{name}' carries multiplicities: bind them as `{name}:k`, or drop them as `{name}:_`"
                            ),
                            span,
                        ));
                    }
                    (_, BinderMult::Var(_), false) => {
                        return Err((
                            format!("the column bound to '{name}' has no multiplicities to bind"),
                            span,
                        ));
                    }
                    (Ty::Node(_), _, _) => match self.alloc(name, ty.clone(), span)? {
                        SLocal::Node(i) => SBinder::Node(i),
                        _ => return Err((format!("internal: {}", "a node binder"), span)),
                    },
                    (Ty::Lit(_), _, _) => match self.alloc(name, ty.clone(), span)? {
                        SLocal::Lit(i) => SBinder::Lit(i),
                        SLocal::Mult(i) => SBinder::Mult(i),
                        SLocal::Node(_) => {
                            return Err((format!("internal: {}", "a literal binder"), span));
                        }
                    },
                    _ => return Err((format!("'{name}' would bind a sequence"), span)),
                };
                out.push(b);
            }
            self.finish_comp(body, mult, rows, out, filter, elem, span)
        })();
        self.scopes.pop();
        res
    }

    #[allow(clippy::too_many_arguments)]
    fn finish_comp(
        &mut self,
        body: &RhsTerm,
        mult: Option<&crate::ast::MultExpr>,
        rows: SRows<L>,
        binders: Vec<SBinder>,
        filter: &Option<Box<RhsTerm>>,
        elem: S,
        span: Span,
    ) -> R<SChild<O, L>> {
        let body = self.term(body, elem)?;
        let mult = match mult {
            Some(m) => Some(self.mult_expr(m, span)?),
            None => None,
        };
        let guard = match filter {
            Some(g) => Some(self.scalar(g, Some(self.bool_sort))?.0),
            None => None,
        };
        Ok(SChild::Comp {
            body,
            mult,
            rows,
            binders,
            guard,
        })
    }
}

/// "§Multiplicities and `zip`: The comprehension's bracket is the target operator's
/// kind: `..[ … ]` under A, `..{ … }` under ACI and AC".
fn comp_bracket(c: &RhsChild, ordered: bool, op: &str) -> R<()> {
    let (is_ordered, span) = match c {
        RhsChild::SeqComp { span, .. } => (true, *span),
        RhsChild::SetComp { span, .. } | RhsChild::MsetComp { span, .. } => (false, *span),
        RhsChild::RowComp { ordered, span, .. } => (*ordered, *span),
        _ => return Ok(()),
    };
    match (ordered, is_ordered) {
        (true, false) => Err((
            format!("'{op}' is associative: its comprehension is ordered, written `..[ … ]`"),
            span,
        )),
        (false, true) => Err((
            format!("'{op}' is AC or ACI: its comprehension is unordered, written `..{{ … }}`"),
            span,
        )),
        _ => Ok(()),
    }
}

/// The primitives whose value is rows of sequences, consumed by a comprehension or
/// by `count`.
fn is_rows_prim(op: &str) -> bool {
    matches!(op, "zip" | "concat" | "union-by" | "narrow" | "narrowed")
}

fn reduction(op: &str) -> Option<Reduction> {
    match op {
        "count" => Some(Reduction::Count),
        "min" => Some(Reduction::Min),
        "max" => Some(Reduction::Max),
        "sum" => Some(Reduction::Sum),
        _ => None,
    }
}

/// The names a sequence rule's match binds, with their sorts, for resolution.
pub struct SeqNames<S> {
    pub node_sorts: HashMap<String, S>,
    pub lit_sorts: HashMap<String, S>,
    pub rest_sorts: HashMap<String, S>,
    pub col_sorts: HashMap<String, S>,
}

/// Resolve a sequence rule's right-hand side (of sort `root_sort`), `:let`
/// bindings, and `:when` guards against its match shape.
#[allow(clippy::too_many_arguments)]
pub fn resolve<O, S, L, M, const TRACK: bool>(
    rhs: &RhsTerm,
    lets: &[(String, RhsTerm)],
    whens: &[RhsTerm],
    root_sort: S,
    shape: &MatchShape,
    names: &SeqNames<S>,
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    model: &M,
    globals: &GlobalCtx<S>,
) -> R<SeqRhs<O, L>>
where
    O: DenseId + std::hash::Hash + Copy,
    S: DenseId + Copy + std::fmt::Debug,
    L: LitVal,
    M: LitModel<Value = L>,
{
    let i64_sort = sorts
        .id_by_name("i64")
        .ok_or_else(|| ("the model has no i64 sort".to_string(), rhs.span()))?;
    let bool_sort = sorts
        .id_by_name("bool")
        .ok_or_else(|| ("the model has no bool sort".to_string(), rhs.span()))?;
    let mut r = Resolver {
        ops,
        sorts,
        model,
        globals,
        shape,
        node_sorts: &names.node_sorts,
        lit_sorts: &names.lit_sorts,
        rest_sorts: &names.rest_sorts,
        col_sorts: &names.col_sorts,
        i64_sort,
        bool_sort,
        scopes: Vec::new(),
        counts: (0, 0, 0),
        lets: Vec::new(),
        plan: Vec::new(),
        warnings: Vec::new(),
    };
    let mut rlets = Vec::with_capacity(lets.len());
    for (name, e) in lets {
        let (v, s) = r.scalar(e, None)?;
        if r.lets.iter().any(|(n, _)| n == name) {
            return Err((format!("'{name}' is bound twice"), e.span()));
        }
        rlets.push(v);
        r.lets.push((name.clone(), s));
    }
    let mut rwhens = Vec::with_capacity(whens.len());
    for g in whens {
        rwhens.push(
            r.scalar(g, Some(bool_sort))
                .map_err(|(m, s)| {
                    if m.starts_with("an expression of sort") {
                        (format!("a guard is a bool: {m}"), s)
                    } else {
                        (m, s)
                    }
                })?
                .0,
        );
    }
    let rhs = r.term(rhs, root_sort)?;
    Ok(SeqRhs {
        rhs,
        lets: rlets,
        whens: rwhens,
        locals: r.counts,
        plan: r.plan,
        warnings: r.warnings,
    })
}

// ── Evaluation ───────────────────────────────────────────────────────────────

/// A sequence rule does not fire at this match: a reduction or a right-hand side with
/// no value.
pub const NO_FIRE: &str = "no value";

/// The most children one application a right-hand side builds may have. Splicing an
/// AC child of multiplicity m under an A or AC operator repeats it m times, and a
/// right-hand side can multiply multiplicities (`(G x):(* k k)`), so a match can ask
/// for more children than memory holds; such a match is skipped with a warning and
/// counted, as a node over the match bound is.
pub const MAX_WIDTH: usize = 1 << 20;

/// A count beyond 2^64 reaching a sequence rule, which computes at the u64 surface width:
/// the rule reports it. Both built widths fit u64, so this guards the trait contract
/// (`to_u64` is fallible) and is not reachable from a program today.
pub const BEYOND_U64: &str = "multiplicity overflow: a count beyond 2^64 in a sequence rule";

/// A count as the sequence-rule evaluator reads it, at the u64 surface width.
fn surface<K: MultiplicityLike>(k: K) -> ERes<u64> {
    k.to_u64().ok_or_else(|| BEYOND_U64.to_string())
}

/// A right-hand side over `MAX_WIDTH`.
pub const TOO_WIDE: &str = "an application of more than 2^20 children";

/// The value of one element of a sequence or row.
#[derive(Clone, Debug)]
enum SVal<G, L> {
    Node(G),
    NodeMult(G, u64),
    Lit(L),
    /// A multiplicity, native (an AC filter's multiplicity column).
    Count(u64),
}

struct Env<'m, Cfg: EGraphConfig, L, Q: ?Sized> {
    query: &'m Q,
    shape: &'m MatchShape,
    nodes: Vec<Option<Cfg::G>>,
    lits: Vec<Option<L>>,
    mults: Vec<Option<u64>>,
    lets: Vec<L>,
}

type ERes<T> = Result<T, String>;

/// Evaluate `:let` and `:when` against the match: `Ok(None)` when a guard fails or
/// a reduction has no value, `Ok(Some(lets))` when the rule fires.
pub fn prelude<Cfg, L, M, Q, const T: bool, const P: bool>(
    s: &SeqRhs<Cfg::O, L>,
    shape: &MatchShape,
    query: &Q,
    eg: &EGraph<Cfg, L, T, P>,
    model: &M,
) -> ERes<Option<Vec<L>>>
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    Q: MatchView<Cfg> + ?Sized,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    let mut env = Env::<Cfg, L, Q> {
        query,
        shape,
        nodes: vec![None; s.locals.0],
        lits: vec![None; s.locals.1],
        mults: vec![None; s.locals.2],
        lets: Vec::new(),
    };
    for l in &s.lets {
        match scalar(l, &env, eg, model) {
            Ok(v) => env.lets.push(v),
            Err(e) if e == NO_FIRE => return Ok(None),
            Err(e) => return Err(e),
        }
    }
    for g in &s.whens {
        match scalar(g, &env, eg, model) {
            Ok(v) if M::is_truthy(&v) => {}
            Ok(_) => return Ok(None),
            Err(e) if e == NO_FIRE => return Ok(None),
            Err(e) => return Err(e),
        }
    }
    Ok(Some(env.lets))
}

/// Build the right-hand side for a match whose prelude gave `lets`: `Err(NO_FIRE)`
/// when it has no value.
pub fn build<Cfg, L, M, Q, S: Copy, const T: bool, const P: bool>(
    s: &SeqRhs<Cfg::O, L>,
    lets: Vec<L>,
    shape: &MatchShape,
    query: &Q,
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    globals: &GlobalCtx<S, Cfg::G>,
) -> ERes<Cfg::G>
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    Q: MatchView<Cfg> + ?Sized,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    let mut env = Env::<Cfg, L, Q> {
        query,
        shape,
        nodes: vec![None; s.locals.0],
        lits: vec![None; s.locals.1],
        mults: vec![None; s.locals.2],
        lets,
    };
    term(&s.rhs, &mut env, eg, model, globals)
}

fn prim_eval<M: LitModel>(model: &M, prim: usize, args: &[M::Value]) -> ERes<M::Value> {
    let d = model
        .ops()
        .get(prim)
        .ok_or_else(|| format!("no primitive {prim}"))?;
    let refs: Vec<&M::Value> = args.iter().collect();
    (d.eval)(&refs).ok_or_else(|| {
        format!(
            "{} is undefined on ({})",
            d.name,
            args.iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    })
}

fn int<M: LitModel>(model: &M, n: u64) -> ERes<M::Value> {
    let n = i64::try_from(n).map_err(|_| format!("{n} is beyond i64"))?;
    model
        .parse_as("i64", &n.to_string())
        .ok_or_else(|| "the model has no i64 sort".into())
}

fn scalar<Cfg, L, M, Q, const T: bool, const P: bool>(
    s: &SScalar<L>,
    env: &Env<'_, Cfg, L, Q>,
    eg: &EGraph<Cfg, L, T, P>,
    model: &M,
) -> ERes<L>
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    Q: MatchView<Cfg> + ?Sized,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    Ok(match s {
        SScalar::Const(v) => v.clone(),
        SScalar::QueryLit(v) => eg.lits().get(env.query.get_lit_val(*v)).clone(),
        SScalar::QueryMult(m) => int(model, surface(env.query.get_mult(*m))?)?,
        SScalar::Local(SLocal::Lit(i)) => env.lits[*i].clone().ok_or("an unbound literal local")?,
        SScalar::Local(SLocal::Mult(i)) => {
            int(model, env.mults[*i].ok_or("an unbound multiplicity local")?)?
        }
        SScalar::Local(SLocal::Node(_)) => return Err("a node where a literal is expected".into()),
        SScalar::Let(i) => env
            .lets
            .get(*i)
            .cloned()
            .ok_or("a let used before it is bound")?,
        SScalar::Prim { prim, args } => {
            let mut vs = Vec::with_capacity(args.len());
            for a in args {
                vs.push(scalar(a, env, eg, model)?);
            }
            prim_eval(model, *prim, &vs)?
        }
        SScalar::CountRows(r) => {
            let n = rows_of(r, env, eg, model)?.len();
            int(
                model,
                u64::try_from(n).map_err(|_| "multiplicity overflow: a count beyond u64")?,
            )?
        }
        SScalar::Reduce { red, prim, arg } => {
            let items = seq(arg, env, eg, model)?;
            if *red == Reduction::Count {
                return int(
                    model,
                    u64::try_from(items.len())
                        .map_err(|_| "multiplicity overflow: a count beyond u64")?,
                );
            }
            let mut acc: Option<L> = None;
            for it in items {
                let x = match it {
                    SVal::Lit(x) => x,
                    SVal::Count(m) => int(model, m)?,
                    _ => return Err("min, max, and sum reduce literals".into()),
                };
                acc = Some(match acc {
                    None => x,
                    Some(a) => prim_eval(
                        model,
                        prim.ok_or("a reduction without its primitive")?,
                        &[a, x],
                    )?,
                });
            }
            match (acc, red) {
                (Some(a), _) => a,
                (None, Reduction::Sum) => int(model, 0)?,
                (None, _) => return Err(NO_FIRE.into()),
            }
        }
    })
}

fn rest_vals<Cfg: EGraphConfig, L, Q: MatchView<Cfg> + ?Sized>(
    q: &Q,
    r: RestRef,
) -> ERes<Vec<SVal<Cfg::G, L>>> {
    Ok(match r {
        RestRef::Seq(v) => q.seq_slice(v).iter().map(|&g| SVal::Node(g)).collect(),
        RestRef::Set(v) => q.set_slice(v).iter().map(|&g| SVal::Node(g)).collect(),
        RestRef::Mset(v) => q
            .mset_slice(v)
            .iter()
            .map(|c| {
                Ok(SVal::NodeMult(
                    Cfg::mset_child_id(c),
                    surface(Cfg::mset_child_mult(c))?,
                ))
            })
            .collect::<ERes<_>>()?,
    })
}

fn seq<Cfg, L, M, Q, const T: bool, const P: bool>(
    s: &SSeq<L>,
    env: &Env<'_, Cfg, L, Q>,
    eg: &EGraph<Cfg, L, T, P>,
    model: &M,
) -> ERes<Vec<SVal<Cfg::G, L>>>
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    Q: MatchView<Cfg> + ?Sized,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    Ok(match s {
        SSeq::Children(r) => rest_vals::<Cfg, L, Q>(env.query, *r)?,
        SSeq::Col(ColRef::Node(v)) => env
            .query
            .seq_slice(*v)
            .iter()
            .map(|&g| SVal::Node(g))
            .collect(),
        SSeq::Col(ColRef::Lit(v)) => env
            .query
            .lit_seq_slice(*v)
            .iter()
            .map(|&id| SVal::Lit(eg.lits().get(id).clone()))
            .collect(),
        SSeq::Col(ColRef::Mult(v)) => env
            .query
            .mset_slice(*v)
            .iter()
            .map(|c| Ok(SVal::Count(surface(Cfg::mset_child_mult(c))?)))
            .collect::<ERes<_>>()?,
        SSeq::Map { prim, args } => {
            let mut cols: Vec<Option<Vec<SVal<Cfg::G, L>>>> = Vec::with_capacity(args.len());
            let mut scalars: Vec<Option<L>> = Vec::with_capacity(args.len());
            let mut n: Option<usize> = None;
            for a in args {
                match a {
                    SSeqArg::Seq(q) => {
                        let v = seq(q, env, eg, model)?;
                        // Element-wise over sequences of one length (the columns of one
                        // filter); a shorter one stops the map, as `zip` does.
                        n = Some(n.map_or(v.len(), |m| m.min(v.len())));
                        cols.push(Some(v));
                        scalars.push(None);
                    }
                    SSeqArg::Scalar(x) => {
                        cols.push(None);
                        scalars.push(Some(scalar(x, env, eg, model)?));
                    }
                }
            }
            let n = n.unwrap_or(0);
            let mut out = Vec::with_capacity(n);
            for j in 0..n {
                let mut vs = Vec::with_capacity(args.len());
                for (c, x) in cols.iter().zip(&scalars) {
                    vs.push(match (c, x) {
                        (Some(c), _) => match &c[j] {
                            SVal::Lit(l) => l.clone(),
                            SVal::Count(m) => int(model, *m)?,
                            _ => return Err("a primitive over a class".into()),
                        },
                        (None, Some(x)) => x.clone(),
                        (None, None) => {
                            return Err("internal: an argument is a sequence or a scalar".into());
                        }
                    });
                }
                out.push(SVal::Lit(prim_eval(model, *prim, &vs)?));
            }
            out
        }
    })
}

fn term<Cfg, L, M, Q, S: Copy, const T: bool, const P: bool>(
    t: &STerm<Cfg::O, L>,
    env: &mut Env<'_, Cfg, L, Q>,
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    globals: &GlobalCtx<S, Cfg::G>,
) -> ERes<Cfg::G>
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    Q: MatchView<Cfg> + ?Sized,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    Ok(match t {
        STerm::Node(SNode::Query(v)) => eg.find(env.query.get(*v)),
        STerm::Node(SNode::Local(i)) => eg.find(env.nodes[*i].ok_or("an unbound node local")?),
        STerm::Global(g) => eg.find(globals.binding(*g)),
        STerm::Lit { op, val } => {
            let v = scalar(val, env, eg, model)?;
            let id = eg.intern_lit(v);
            eg.add_lit(*op, id)
        }
        STerm::If { cond, then, els } => {
            let c = scalar(cond, env, eg, model)?;
            if M::is_truthy(&c) {
                term(then, env, eg, model, globals)?
            } else {
                term(els, env, eg, model, globals)?
            }
        }
        STerm::App { op, children } => {
            let kind = eg.ops().info(*op).kind.clone();
            // The children in the form the operator stores (`apply::Children`). Only an A
            // operator keeps copies as positions; an AC one keeps a count, an ACI one, or
            // any other, a single child.
            let mut out = match kind {
                OpKind::A { .. } | OpKind::MSet { .. } => Children::<Cfg>::for_kind(&kind),
                _ => Children::<Cfg>::Distinct(Default::default()),
            };
            for c in children {
                child(c, env, eg, model, globals, &mut out)?;
            }
            let (len, single) = match &out {
                Children::Positional(ids) | Children::Distinct(ids) => {
                    (ids.len(), ids.first().copied())
                }
                Children::Counted(cs) => (
                    cs.len(),
                    cs.first()
                        .filter(|c| Cfg::mset_child_mult(c) == Cfg::M::ONE)
                        .map(|c| Cfg::mset_child_id(c)),
                ),
            };
            // The unit law: an AC or ACI application of one child is the child.
            if matches!(kind, OpKind::Set { .. } | OpKind::MSet { .. })
                && len == 1
                && let Some(g) = single
            {
                return Ok(g);
            }
            let empty_ok = matches!(
                &kind,
                OpKind::Set {
                    identity: Some(_),
                    ..
                } | OpKind::MSet {
                    identity: Some(_),
                    ..
                }
            );
            if len == 0
                && matches!(
                    kind,
                    OpKind::A { .. } | OpKind::Set { .. } | OpKind::MSet { .. }
                )
                && !empty_ok
            {
                return Err(NO_FIRE.into());
            }
            match &out {
                Children::Counted(cs) => eg
                    .add_mset(*op, cs)
                    .map_err(|_| mult_overflow_error(&eg.ops().info(*op).name).to_string())?,
                Children::Positional(ids) | Children::Distinct(ids) => eg.add(*op, ids),
            }
        }
    })
}

/// `g` counted `m > 0` times, in the application's form: `m` positions under an A
/// operator, bounded by [`MAX_WIDTH`]; one counted entry under an AC operator, narrowed
/// to the configured width; one child otherwise.
fn push_repeated<Cfg: EGraphConfig>(out: &mut Children<Cfg>, g: Cfg::G, m: u64) -> ERes<()> {
    match out {
        Children::Positional(ids) => {
            let m = usize::try_from(m).map_err(|_| TOO_WIDE)?;
            if ids.len().checked_add(m).is_none_or(|n| n > MAX_WIDTH) {
                return Err(TOO_WIDE.into());
            }
            ids.extend(std::iter::repeat_n(g, m));
        }
        Children::Distinct(ids) => ids.push(g),
        Children::Counted(cs) => {
            let k = Cfg::M::try_from_u64(m).ok_or_else(|| {
                crate::multiplicity::overflow_message::<Cfg::M>(&format!("the count {m}"))
            })?;
            cs.push(Cfg::mset_child_with_mult(g, k));
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn child<Cfg, L, M, Q, S: Copy, const T: bool, const P: bool>(
    c: &SChild<Cfg::O, L>,
    env: &mut Env<'_, Cfg, L, Q>,
    eg: &mut EGraph<Cfg, L, T, P>,
    model: &M,
    globals: &GlobalCtx<S, Cfg::G>,
    out: &mut Children<Cfg>,
) -> ERes<()>
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    Q: MatchView<Cfg> + ?Sized,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    match c {
        SChild::One(t) => out.push(term(t, env, eg, model, globals)?),
        SChild::OneMult(t, m) => {
            let k = mult_of(m, env)?;
            if k > 0 {
                let g = term(t, env, eg, model, globals)?;
                push_repeated(out, g, k)?;
            }
        }
        SChild::Splice(r) => {
            // "§Edge cases 3": an AC sequence under an operator that keeps copies
            // repeats each child by its multiplicity; under ACI, one copy.
            for v in rest_vals::<Cfg, L, Q>(env.query, *r)? {
                match v {
                    SVal::Node(g) => out.push(eg.find(g)),
                    SVal::NodeMult(g, m) => push_repeated(out, eg.find(g), m)?,
                    SVal::Lit(_) | SVal::Count(_) => {
                        return Err("a literal spliced as a child".into());
                    }
                }
            }
        }
        SChild::Comp {
            body,
            mult,
            rows,
            binders,
            guard,
        } => {
            let rows = rows_of(rows, env, eg, model)?;
            for row in rows {
                // Bind the row, remembering what each binder held (a comprehension
                // nested in another may reuse no local, but restoring is the rule).
                let mut saved: Vec<(SLocal, Option<Cfg::G>, Option<L>, Option<u64>)> =
                    Vec::with_capacity(binders.len());
                let bind = |env: &mut Env<'_, Cfg, L, Q>,
                            b: &SBinder,
                            v: &SVal<Cfg::G, L>,
                            saved: &mut Vec<(SLocal, Option<Cfg::G>, Option<L>, Option<u64>)>|
                 -> ERes<()> {
                    match (b, v) {
                        (SBinder::Node(i), SVal::Node(g) | SVal::NodeMult(g, _)) => {
                            saved.push((SLocal::Node(*i), env.nodes[*i].replace(*g), None, None));
                        }
                        (SBinder::NodeMult(i, k), SVal::NodeMult(g, m)) => {
                            saved.push((SLocal::Node(*i), env.nodes[*i].replace(*g), None, None));
                            saved.push((SLocal::Mult(*k), None, None, env.mults[*k].replace(*m)));
                        }
                        (SBinder::NodeMult(i, k), SVal::Node(g)) => {
                            saved.push((SLocal::Node(*i), env.nodes[*i].replace(*g), None, None));
                            saved.push((SLocal::Mult(*k), None, None, env.mults[*k].replace(1)));
                        }
                        (SBinder::Lit(i), SVal::Lit(l)) => {
                            saved.push((
                                SLocal::Lit(*i),
                                None,
                                env.lits[*i].replace(l.clone()),
                                None,
                            ));
                        }
                        (SBinder::Mult(k), SVal::Count(m)) => {
                            saved.push((SLocal::Mult(*k), None, None, env.mults[*k].replace(*m)));
                        }
                        _ => return Err("a row element of another kind than its binder".into()),
                    }
                    Ok(())
                };
                let mut res: ERes<()> = Ok(());
                for (b, v) in binders.iter().zip(&row) {
                    res = bind(env, b, v, &mut saved);
                    if res.is_err() {
                        break;
                    }
                }
                let res = res.and_then(|()| {
                    let keep = match guard {
                        Some(g) => M::is_truthy(&scalar(g, env, eg, model)?),
                        None => true,
                    };
                    if !keep {
                        return Ok(());
                    }
                    let k = match mult {
                        Some(m) => mult_of(m, env)?,
                        None => 1,
                    };
                    if k > 0 {
                        let g = term(body, env, eg, model, globals)?;
                        push_repeated(out, g, k)?;
                    }
                    Ok(())
                });
                // Restore on every path.
                for (l, n, x, m) in saved.into_iter().rev() {
                    match l {
                        SLocal::Node(i) => env.nodes[i] = n,
                        SLocal::Lit(i) => env.lits[i] = x,
                        SLocal::Mult(i) => env.mults[i] = m,
                    }
                }
                res?;
            }
        }
    }
    Ok(())
}

/// A multiplicity expression's value, with checked arithmetic.
fn mult_of<Cfg: EGraphConfig, L, Q: MatchView<Cfg> + ?Sized>(
    m: &SMult,
    env: &Env<'_, Cfg, L, Q>,
) -> ERes<u64> {
    Ok(match m {
        SMult::Lit(n) => *n,
        SMult::Query(v) => surface(env.query.get_mult(*v))?,
        SMult::Local(i) => env.mults[*i].ok_or("an unbound multiplicity local")?,
        SMult::Prim { op, args } => {
            let vs = args
                .iter()
                .map(|a| mult_of(a, env))
                .collect::<ERes<Vec<_>>>()?;
            let [a, b] = vs.as_slice() else {
                return Err("a multiplicity operator takes two arguments".into());
            };
            match op {
                MultOp::Add => a
                    .checked_add(*b)
                    .ok_or("multiplicity overflow: a sum in a sequence rule's count")?,
                MultOp::Sub => a.checked_sub(*b).ok_or("a multiplicity went below zero")?,
                MultOp::Mul => a
                    .checked_mul(*b)
                    .ok_or("multiplicity overflow: a product in a sequence rule's count")?,
                MultOp::Min => *a.min(b),
                MultOp::Max => *a.max(b),
            }
        }
    })
}

fn rows_of<Cfg, L, M, Q, const T: bool, const P: bool>(
    r: &SRows<L>,
    env: &Env<'_, Cfg, L, Q>,
    eg: &EGraph<Cfg, L, T, P>,
    model: &M,
) -> ERes<Vec<Vec<SVal<Cfg::G, L>>>>
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    Q: MatchView<Cfg> + ?Sized,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    Ok(match r {
        SRows::Rest(rr) => rest_vals::<Cfg, L, Q>(env.query, *rr)?
            .into_iter()
            .map(|v| vec![v])
            .collect(),
        SRows::Filter(fi) => {
            let f = &env.shape.filters[*fi];
            let elems = rest_vals::<Cfg, L, Q>(env.query, f.elems)?;
            let mut cols = Vec::with_capacity(f.cols.len());
            for (_, c) in &f.cols {
                cols.push(seq(&SSeq::Col(*c), env, eg, model)?);
            }
            // The columns of one filter have its length; `min` keeps a malformed match
            // from indexing past one.
            let n = cols.iter().map(Vec::len).fold(elems.len(), usize::min);
            (0..n)
                .map(|j| {
                    let mut row = vec![elems[j].clone()];
                    for c in &cols {
                        row.push(c[j].clone());
                    }
                    row
                })
                .collect()
        }
        SRows::Zip(qs) => {
            let mut cols = Vec::with_capacity(qs.len());
            for q in qs {
                cols.push(seq(q, env, eg, model)?);
            }
            // "§Multiplicities and `zip`: stopping at the shortest input".
            let n = cols.iter().map(|c| c.len()).min().unwrap_or(0);
            (0..n)
                .map(|j| cols.iter().map(|c| c[j].clone()).collect())
                .collect()
        }
        SRows::Concat(qs) => {
            let mut out = Vec::new();
            for q in qs {
                out.extend(seq(q, env, eg, model)?.into_iter().map(|v| vec![v]));
            }
            out
        }
        SRows::UnionBy(args) => {
            let [p, l, u] = args.as_ref();
            let (p, l, u) = (
                seq(p, env, eg, model)?,
                seq(l, env, eg, model)?,
                seq(u, env, eg, model)?,
            );
            let ints = Ints::new(model)?;
            let mut groups: Vec<(Cfg::G, Vec<(L, L)>)> = Vec::new();
            for j in 0..p.len().min(l.len()).min(u.len()) {
                let (SVal::Node(g) | SVal::NodeMult(g, _)) = &p[j] else {
                    return Err("union-by: a literal where a class is expected".into());
                };
                let as_lit = |x: &SVal<Cfg::G, L>| -> ERes<L> {
                    match x {
                        SVal::Lit(l) => Ok(l.clone()),
                        SVal::Count(m) => int(model, *m),
                        _ => Err("union-by: a class where an integer is expected".into()),
                    }
                };
                let (a, b) = (as_lit(&l[j])?, as_lit(&u[j])?);
                match groups.iter_mut().find(|(x, _)| x == g) {
                    Some((_, w)) => w.push((a, b)),
                    None => groups.push((*g, vec![(a, b)])),
                }
            }
            let mut out = Vec::new();
            for (g, w) in groups {
                for (a, b) in ints.union(w)? {
                    out.push(vec![SVal::Node(g), SVal::Lit(a), SVal::Lit(b)]);
                }
            }
            out
        }
        SRows::Narrow(args, changed_only) => {
            let mut v = Vec::with_capacity(6);
            for q in args.iter() {
                v.push(seq(q, env, eg, model)?);
            }
            let lit = |x: &SVal<Cfg::G, L>| -> ERes<L> {
                match x {
                    SVal::Lit(l) => Ok(l.clone()),
                    SVal::Count(m) => int(model, *m),
                    _ => Err("narrow: a class where an integer is expected".into()),
                }
            };
            let node = |x: &SVal<Cfg::G, L>| -> ERes<Cfg::G> {
                match x {
                    SVal::Node(g) | SVal::NodeMult(g, _) => Ok(*g),
                    SVal::Lit(_) | SVal::Count(_) => {
                        Err("narrow: an integer where a class is expected".into())
                    }
                }
            };
            let ints = Ints::new(model)?;
            let mut out = Vec::new();
            for i in 0..v[0].len().min(v[1].len()).min(v[2].len()) {
                let (c, d, r) = (lit(&v[0][i])?, lit(&v[1][i])?, node(&v[2][i])?);
                let mut windows = Vec::new();
                for j in 0..v[3].len().min(v[4].len()).min(v[5].len()) {
                    if node(&v[5][j])? == r {
                        windows.push((lit(&v[3][j])?, lit(&v[4][j])?));
                    }
                }
                let windows = ints.union(windows)?;
                let (mut lo, mut hi) = (c.clone(), d.clone());
                loop {
                    let before = (lo.clone(), hi.clone());
                    for (wa, wb) in &windows {
                        if ints.le(wa, &lo)?
                            && ints.le(&lo, &ints.succ(wb)?)?
                            && ints.lt(wb, &hi)?
                        {
                            lo = ints.max(&lo, &ints.succ(wb)?)?;
                        }
                        if ints.lt(&lo, wa)? && ints.le(wa, &hi)? && ints.le(&hi, wb)? {
                            hi = ints.min(&hi, &ints.pred(wa)?)?;
                        }
                    }
                    if lo == before.0 && hi == before.1 {
                        break;
                    }
                }
                let (lo, hi) = if ints.le(&lo, &hi)? {
                    (lo, hi)
                } else {
                    (c.clone(), d.clone())
                };
                if !*changed_only || lo != c || hi != d {
                    out.push(vec![SVal::Node(r), SVal::Lit(lo), SVal::Lit(hi)]);
                }
            }
            out
        }
    })
}

/// Integer comparisons and arithmetic on literals through the model's primitives
/// (the literal type is opaque; the model's checked arithmetic reports an overflow).
struct Ints<'m, M: LitModel> {
    model: &'m M,
    one: M::Value,
}

impl<'m, M: LitModel> Ints<'m, M> {
    fn new(model: &'m M) -> ERes<Self> {
        Ok(Ints {
            model,
            one: model
                .parse_as("i64", "1")
                .ok_or("the model has no i64 sort")?,
        })
    }
    fn call(&self, name: &str, args: &[&M::Value]) -> ERes<M::Value> {
        let sort = args.first().map(|a| M::sort_of(a)).unwrap_or("");
        let d = self
            .model
            .find_op(&format!("{sort}::{name}"))
            .or_else(|| self.model.find_op(name))
            .ok_or_else(|| format!("no primitive '{name}' on {sort}"))?;
        (d.eval)(args).ok_or_else(|| {
            format!(
                "{name} is undefined on ({})",
                args.iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })
    }
    fn le(&self, a: &M::Value, b: &M::Value) -> ERes<bool> {
        self.call("<=", &[a, b]).map(|v| M::is_truthy(&v))
    }
    fn lt(&self, a: &M::Value, b: &M::Value) -> ERes<bool> {
        self.call("<", &[a, b]).map(|v| M::is_truthy(&v))
    }
    fn succ(&self, a: &M::Value) -> ERes<M::Value> {
        self.call("+", &[a, &self.one])
    }
    fn pred(&self, a: &M::Value) -> ERes<M::Value> {
        self.call("-", &[a, &self.one])
    }
    fn max(&self, a: &M::Value, b: &M::Value) -> ERes<M::Value> {
        Ok(if self.le(a, b)? { b.clone() } else { a.clone() })
    }
    fn min(&self, a: &M::Value, b: &M::Value) -> ERes<M::Value> {
        Ok(if self.le(a, b)? { a.clone() } else { b.clone() })
    }
    fn union(&self, w: Vec<(M::Value, M::Value)>) -> ERes<Vec<(M::Value, M::Value)>> {
        let mut sorted: Vec<(M::Value, M::Value)> = Vec::with_capacity(w.len());
        for x in w {
            let mut at = sorted.len();
            for (i, y) in sorted.iter().enumerate() {
                if self.lt(&x.0, &y.0)? || (!self.lt(&y.0, &x.0)? && self.lt(&x.1, &y.1)?) {
                    at = i;
                    break;
                }
            }
            sorted.insert(at, x);
        }
        let mut out: Vec<(M::Value, M::Value)> = Vec::new();
        for (l, u) in sorted {
            match out.last_mut() {
                Some(last) if self.le(&l, &self.succ(&last.1)?)? => {
                    last.1 = self.max(&last.1, &u)?
                }
                _ => out.push((l, u)),
            }
        }
        Ok(out)
    }
}

// ── Non-emptiness analysis ───────────────────────────────────────────────────

impl<O, L: LitVal> SeqRhs<O, L> {
    /// Per filter of `shape`, whether the rule cannot fire when that filter is empty
    /// (Semper design §7.6, "When part 2 is dropped"). A plan may then drive from
    /// the filter alone and skip the nodes where it has no row.
    ///
    /// **Soundness condition, not an optimisation hint.** Answering "required" wrongly
    /// drops matches, so the analysis is conservative: it answers "not known" whenever a
    /// form is not one of these, each of which provably fails on an empty filter `g`:
    ///
    /// - a `:when` conjunct `(op C D)` where both are counts that are 0 whenever `g` is
    ///   empty and `op(0, 0)` evaluates false (merging's `(< (count (union-by p l u))
    ///   (count gs))`);
    /// - a `:when` conjunct `(op C k)` or `(op k C)` with `k` a constant, where `C` is
    ///   0 whenever `g` is empty (`count` of `g`, of one of its columns, of a primitive
    ///   mapped over one, or of rows that are empty when `g` is), and `op(0, k)`
    ///   evaluates false. The test goes through the model's primitive, so `>=`, `>`,
    ///   `==`, and `!=` are all handled and no literal is parsed;
    /// - `min` or `max` over a sequence that is empty when `g` is, anywhere in the
    ///   `:let`s (always evaluated) or `:when`s (evaluated in order, and an earlier
    ///   failing guard also prevents firing), since it has no value there.
    ///
    /// Rows are empty on an empty `g` for `zip` over any `g`-derived input, `narrow` and
    /// `narrowed` over `g`'s first three columns, `union-by` over any `g`-derived input
    /// (all three are implemented here, so the property is known rather than assumed),
    /// and `concat` only when every input is. `sum` is 0 on empty input, not undefined,
    /// so it proves nothing.
    pub fn required_nonempty<M: LitModel<Value = L>>(
        &self,
        shape: &MatchShape,
        model: &M,
    ) -> Vec<bool> {
        (0..shape.filters.len())
            .map(|g| {
                self.lets.iter().any(|e| minmax_over(e, g, shape))
                    || self
                        .whens
                        .iter()
                        .any(|w| minmax_over(w, g, shape) || fails_when_empty(w, g, shape, model))
            })
            .collect()
    }
}

/// Whether the sequence is empty whenever filter `g` is.
fn seq_empty_if<L>(s: &SSeq<L>, g: usize, shape: &MatchShape) -> bool {
    match s {
        SSeq::Col(c) => shape
            .filters
            .get(g)
            .is_some_and(|f| f.cols.iter().any(|(_, x)| x == c)),
        SSeq::Children(r) => shape.filters.get(g).is_some_and(|f| f.elems == *r),
        // Element-wise over the shortest sequence argument, so one empty input is enough.
        SSeq::Map { args, .. } => args
            .iter()
            .any(|a| matches!(a, SSeqArg::Seq(q) if seq_empty_if(q, g, shape))),
    }
}

/// Whether the rows are empty whenever filter `g` is.
fn rows_empty_if<L>(r: &SRows<L>, g: usize, shape: &MatchShape) -> bool {
    match r {
        SRows::Filter(fi) => *fi == g,
        SRows::Rest(_) => false,
        SRows::Zip(qs) => qs.iter().any(|q| seq_empty_if(q, g, shape)),
        SRows::Concat(qs) => !qs.is_empty() && qs.iter().all(|q| seq_empty_if(q, g, shape)),
        SRows::UnionBy(qs) => qs.iter().any(|q| seq_empty_if(q, g, shape)),
        // The outer loop ranges over the first three columns (`rows_of`).
        SRows::Narrow(qs, _) => qs[..3].iter().any(|q| seq_empty_if(q, g, shape)),
    }
}

/// Whether the scalar is a count that is 0 whenever filter `g` is empty.
fn count_zero_if<L>(e: &SScalar<L>, g: usize, shape: &MatchShape) -> bool {
    match e {
        SScalar::Reduce {
            red: Reduction::Count,
            arg,
            ..
        } => seq_empty_if(arg, g, shape),
        SScalar::CountRows(r) => rows_empty_if(r, g, shape),
        _ => false,
    }
}

/// Whether `min` or `max` over a `g`-empty sequence occurs anywhere in the expression.
fn minmax_over<L>(e: &SScalar<L>, g: usize, shape: &MatchShape) -> bool {
    match e {
        SScalar::Reduce {
            red: Reduction::Min | Reduction::Max,
            arg,
            ..
        } if seq_empty_if(arg, g, shape) => true,
        SScalar::Reduce { arg, .. } => seq_minmax(arg, g, shape),
        SScalar::Prim { args, .. } => args.iter().any(|a| minmax_over(a, g, shape)),
        _ => false,
    }
}

fn seq_minmax<L>(s: &SSeq<L>, g: usize, shape: &MatchShape) -> bool {
    match s {
        SSeq::Map { args, .. } => args.iter().any(|a| match a {
            SSeqArg::Seq(q) => seq_minmax(q, g, shape),
            SSeqArg::Scalar(x) => minmax_over(x, g, shape),
        }),
        _ => false,
    }
}

/// Whether the guard `(op C k)` / `(op k C)` is false when `g` is empty.
fn fails_when_empty<L: LitVal, M: LitModel<Value = L>>(
    w: &SScalar<L>,
    g: usize,
    shape: &MatchShape,
    model: &M,
) -> bool {
    let SScalar::Prim { prim, args } = w else {
        return false;
    };
    let [a, b] = args.as_slice() else {
        return false;
    };
    let Ok(zero) = int(model, 0) else {
        return false;
    };
    let probe = match (a, b) {
        // Both sides counts that vanish with `g`, e.g. merging's
        // `(< (count (union-by p l u)) (count gs))`: `op(0, 0)`.
        (c, d) if count_zero_if(c, g, shape) && count_zero_if(d, g, shape) => {
            prim_eval(model, *prim, &[zero.clone(), zero])
        }
        (c, SScalar::Const(k)) if count_zero_if(c, g, shape) => {
            prim_eval(model, *prim, &[zero, k.clone()])
        }
        (SScalar::Const(k), c) if count_zero_if(c, g, shape) => {
            prim_eval(model, *prim, &[k.clone(), zero])
        }
        _ => return false,
    };
    // An undefined primitive at 0 proves nothing: "unknown", not "required".
    probe.is_ok_and(|v| !M::is_truthy(&v))
}
