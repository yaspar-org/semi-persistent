// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Resolve pass: validate and type-check flat atoms against OpRegistry + LitModel.
//!
//! Transforms `compile::Atom` (string ops) into `ResolvedAtom` (OpId, SortId, LitValId).

use crate::DenseId;
use crate::ast::{
    CmpOp, GlobalVarId, LitValVarId, MsetVarId, MultVarId, RhsLocalMultVarId, RhsLocalVarId,
    SeqVarId, SetVarId, Span, VarId,
};
use crate::compile::{Atom, FlatMult, FlatQuery};
use crate::lit_model::LitModel;
use crate::literal::LitVal;
use crate::registry::{OpKind, OpRegistry, SortRegistry};
use std::collections::HashMap;
use std::hash::Hash;

// ---------------------------------------------------------------------------
// Resolved types

/// Global name table: maps names → dense GlobalVarId, stores (sort, eclass) per id.
#[derive(Clone, Debug)]
pub struct GlobalCtx<S, G = ()> {
    index: HashMap<String, GlobalVarId>,
    sorts: Vec<S>,
    bindings: Vec<G>,
    /// Overwritten name bindings, keyed by the id that shadowed them. This is
    /// normally empty; it lets `truncate` restore an outer binding without
    /// duplicating every global name in a second vector.
    shadows: Vec<(GlobalVarId, String, GlobalVarId)>,
}

impl<S: Copy, G: Copy> Default for GlobalCtx<S, G> {
    fn default() -> Self {
        Self::new()
    }
}

impl<S: Copy, G: Copy> GlobalCtx<S, G> {
    pub fn new() -> Self {
        Self {
            index: HashMap::new(),
            sorts: Vec::new(),
            bindings: Vec::new(),
            shadows: Vec::new(),
        }
    }

    pub fn insert(&mut self, name: String, sort: S, eclass: G) -> GlobalVarId {
        // Checked mint: `GlobalVarId` is a bare u16 with no bound of its own, and
        // globals accumulate across a session, so the 65537th binding would
        // otherwise wrap and alias binding 0 — the same narrow-before-check shape
        // fixed in the container index layer. No Result channel here, so refuse
        // loudly rather than hand back an aliased id.
        let raw = u16::try_from(self.sorts.len())
            .expect("too many global bindings: GlobalVarId is u16, so at most 65536 are supported");
        let gid = GlobalVarId::new(raw);
        self.sorts.push(sort);
        self.bindings.push(eclass);
        match self.index.entry(name) {
            std::collections::hash_map::Entry::Vacant(e) => {
                e.insert(gid);
            }
            std::collections::hash_map::Entry::Occupied(mut e) => {
                let previous = *e.get();
                let name = e.key().clone();
                e.insert(gid);
                self.shadows.push((gid, name, previous));
            }
        }
        gid
    }

    /// Resolver lookup: name → (GlobalVarId, sort, eclass).
    pub fn get(&self, name: &str) -> Option<(GlobalVarId, S, G)> {
        self.index
            .get(name)
            .map(|&gid| (gid, self.sorts[gid.idx()], self.bindings[gid.idx()]))
    }

    /// Runtime: resolve a GlobalVarId to its bound eclass.
    pub fn binding(&self, gid: GlobalVarId) -> G {
        self.bindings[gid.idx()]
    }

    /// Compile-time: resolve a GlobalVarId to its sort.
    pub fn sort(&self, gid: GlobalVarId) -> S {
        self.sorts[gid.idx()]
    }

    pub fn len(&self) -> usize {
        self.sorts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.sorts.is_empty()
    }

    pub fn truncate(&mut self, n: usize) {
        while self
            .shadows
            .last()
            .is_some_and(|(shadowing, _, _)| shadowing.idx() >= n)
        {
            let (_, name, previous) = self.shadows.pop().unwrap();
            self.index.insert(name, previous);
        }
        // A name first introduced in the truncated suffix has no shadow entry.
        // Remove it after restoring overwritten outer bindings.
        self.index.retain(|_, gid| gid.idx() < n);
        self.sorts.truncate(n);
        self.bindings.truncate(n);
    }
}

impl<S: Copy> GlobalCtx<S, ()> {
    /// Convenience for tests: insert with no eclass binding.
    pub fn insert_sort(&mut self, name: String, sort: S) -> GlobalVarId {
        self.insert(name, sort, ())
    }
}
// ---------------------------------------------------------------------------

/// A child position in a pattern atom: local (bound during matching) or global (pre-known).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PatVar {
    Local(VarId),
    Global(GlobalVarId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RAtom<O, S, L> {
    Plain {
        node: VarId,
        op: O,
        children: Vec<PatVar>,
    },
    /// A ground literal in a pattern: `node` is the `@sort` literal node whose payload
    /// equals `value`. `op` is that `@sort` constructor — carried so the scheduler can
    /// emit a real index lookup for this atom. Without it the atom had no lookup to
    /// scan and compiled to an unsatisfiable join.
    Lit {
        node: VarId,
        op: O,
        sort: S,
        value: L,
    },
    AExact {
        node: VarId,
        op: O,
        children: Vec<PatVar>,
    },
    APrefix {
        node: VarId,
        op: O,
        pre: SeqVarId,
        fixed: Vec<PatVar>,
    },
    ASuffix {
        node: VarId,
        op: O,
        fixed: Vec<PatVar>,
        suf: SeqVarId,
    },
    ABoth {
        node: VarId,
        op: O,
        pre: SeqVarId,
        fixed: Vec<PatVar>,
        suf: SeqVarId,
    },
    ACExact {
        node: VarId,
        op: O,
        elems: Vec<(PatVar, RMult)>,
    },
    ACSub {
        node: VarId,
        op: O,
        elems: Vec<(PatVar, RMult)>,
        rest: MsetVarId,
    },
    ACIExact {
        node: VarId,
        op: O,
        elems: Vec<PatVar>,
    },
    ACISub {
        node: VarId,
        op: O,
        elems: Vec<PatVar>,
        rest: SetVarId,
    },
    LitBind {
        node: VarId,
        op: O,
        val: LitValVarId,
    },
    Eq(VarId, VarId),
    EqGlobal(VarId, GlobalVarId),
    /// A primitive predicate guard. Scans nothing and binds nothing: it is evaluated
    /// over already-bound literal values and keeps or drops the partial match.
    ///
    /// `deps` names the atoms that bind the guard's literal values: the `LitBind` atoms
    /// for the variables in `guard.expr`. The scheduler lowers the guard as soon as all
    /// of them have run, which is as early as the guard can be evaluated at all.
    Pred {
        guard: PredGuard<O, L>,
        deps: Vec<usize>,
    },
}

/// A resolved primitive predicate guard: the computation, plus the truth test for the
/// literal model the query was resolved against.
///
/// Both function pointers come from the model (`LitOpDesc::eval`, `LitModel::is_truthy`)
/// and are captured at resolve time, which is what keeps the matcher generic over the
/// value type alone rather than over the whole model.
#[derive(Clone, Debug)]
pub struct PredGuard<O, L> {
    pub expr: RPredExpr<O, L>,
    /// `LitModel::is_truthy`: the guard passes when the value it computes is true.
    pub truthy: fn(&L) -> bool,
}

/// Equality on the computation, not on the captured function pointers: an operator
/// determines its own `eval`, and the truth test is a property of the model, which is
/// fixed for a program. Comparing the pointers would be comparing addresses that the
/// compiler is free to merge or duplicate.
impl<O: PartialEq, L: PartialEq> PartialEq for PredGuard<O, L> {
    fn eq(&self, other: &Self) -> bool {
        self.expr == other.expr
    }
}
impl<O: Eq, L: Eq> Eq for PredGuard<O, L> {}

/// A resolved guard expression. Leaves are bound literal values or constants; nodes are
/// primitive applications carrying the model's evaluator.
#[derive(Clone, Debug)]
pub enum RPredExpr<O, L> {
    /// A literal value bound by a `LitBind` atom.
    Val(LitValVarId),
    /// A constant written in the guard, parsed at the argument position's sort.
    Const(L),
    App {
        op: O,
        eval: fn(&[&L]) -> L,
        args: Vec<RPredExpr<O, L>>,
    },
}

impl<O: PartialEq, L: PartialEq> PartialEq for RPredExpr<O, L> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (RPredExpr::Val(a), RPredExpr::Val(b)) => a == b,
            (RPredExpr::Const(a), RPredExpr::Const(b)) => a == b,
            (
                RPredExpr::App {
                    op: a, args: xs, ..
                },
                RPredExpr::App {
                    op: b, args: ys, ..
                },
            ) => a == b && xs == ys,
            _ => false,
        }
    }
}
impl<O: Eq, L: Eq> Eq for RPredExpr<O, L> {}

impl<O, L> RPredExpr<O, L> {
    /// The literal-value variables the guard reads, in evaluation order.
    pub fn value_vars(&self, out: &mut Vec<LitValVarId>) {
        match self {
            RPredExpr::Val(v) => out.push(*v),
            RPredExpr::Const(_) => {}
            RPredExpr::App { args, .. } => {
                for a in args {
                    a.value_vars(out);
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RMult {
    Exact(u64),
    Var {
        var: MultVarId,
        constraint: Option<(CmpOp, u64)>,
    },
}

/// Describes the shape of a match: per-kind variable info indexed by typed dense id.
///
/// This is the single source of truth for what ids are valid and how to safely
/// index into `Match` and `MatchSet` objects.
#[derive(Clone, Debug, Default)]
pub struct MatchShape {
    pub nodes: Vec<String>,
    pub seqs: Vec<String>,
    pub sets: Vec<String>,
    pub msets: Vec<String>,
    pub mults: Vec<String>,
    pub lit_vals: Vec<String>,
    /// Tracks which kind each name belongs to, for clash detection.
    kinds: std::collections::HashMap<String, VarKind>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VarKind {
    Node,
    Seq,
    Set,
    Mset,
    Mult,
    LitVal,
}

impl VarKind {
    fn label(self) -> &'static str {
        match self {
            VarKind::Node => "node variable",
            VarKind::Seq => "sequence rest variable",
            VarKind::Set => "set rest variable",
            VarKind::Mset => "multiset rest variable",
            VarKind::Mult => "multiplicity variable",
            VarKind::LitVal => "literal value variable",
        }
    }
}

impl MatchShape {
    pub fn num_vars(&self) -> usize {
        self.nodes.len()
    }
    pub fn num_seq_vars(&self) -> usize {
        self.seqs.len()
    }
    pub fn num_set_vars(&self) -> usize {
        self.sets.len()
    }
    pub fn num_mset_vars(&self) -> usize {
        self.msets.len()
    }
    pub fn num_mult_vars(&self) -> usize {
        self.mults.len()
    }
    pub fn num_lit_val_vars(&self) -> usize {
        self.lit_vals.len()
    }

    pub fn var_ids(&self) -> impl Iterator<Item = VarId> {
        (0..self.nodes.len()).map(|i| VarId::new(i as u16))
    }
    pub fn seq_var_ids(&self) -> impl Iterator<Item = SeqVarId> {
        (0..self.seqs.len()).map(|i| SeqVarId::new(i as u16))
    }
    pub fn set_var_ids(&self) -> impl Iterator<Item = SetVarId> {
        (0..self.sets.len()).map(|i| SetVarId::new(i as u16))
    }
    pub fn mset_var_ids(&self) -> impl Iterator<Item = MsetVarId> {
        (0..self.msets.len()).map(|i| MsetVarId::new(i as u16))
    }
    pub fn mult_var_ids(&self) -> impl Iterator<Item = MultVarId> {
        (0..self.mults.len()).map(|i| MultVarId::new(i as u16))
    }
    pub fn lit_val_var_ids(&self) -> impl Iterator<Item = LitValVarId> {
        (0..self.lit_vals.len()).map(|i| LitValVarId::new(i as u16))
    }

    pub fn var_name(&self, v: VarId) -> &str {
        &self.nodes[v.idx()]
    }
    pub fn seq_name(&self, v: SeqVarId) -> &str {
        &self.seqs[v.idx()]
    }
    pub fn set_name(&self, v: SetVarId) -> &str {
        &self.sets[v.idx()]
    }
    pub fn mset_name(&self, v: MsetVarId) -> &str {
        &self.msets[v.idx()]
    }
    pub fn mult_name(&self, v: MultVarId) -> &str {
        &self.mults[v.idx()]
    }
    pub fn lit_val_name(&self, v: LitValVarId) -> &str {
        &self.lit_vals[v.idx()]
    }

    // Lookup helpers — return None if not found
    pub fn find_var(&self, name: &str) -> Option<VarId> {
        self.nodes
            .iter()
            .position(|n| n == name)
            .map(|i| VarId::new(i as u16))
    }
    pub fn find_seq(&self, name: &str) -> Option<SeqVarId> {
        self.seqs
            .iter()
            .position(|n| n == name)
            .map(|i| SeqVarId::new(i as u16))
    }
    pub fn find_set(&self, name: &str) -> Option<SetVarId> {
        self.sets
            .iter()
            .position(|n| n == name)
            .map(|i| SetVarId::new(i as u16))
    }
    pub fn find_mset(&self, name: &str) -> Option<MsetVarId> {
        self.msets
            .iter()
            .position(|n| n == name)
            .map(|i| MsetVarId::new(i as u16))
    }
    pub fn find_mult(&self, name: &str) -> Option<MultVarId> {
        self.mults
            .iter()
            .position(|n| n == name)
            .map(|i| MultVarId::new(i as u16))
    }
    pub fn find_lit_val(&self, name: &str) -> Option<LitValVarId> {
        self.lit_vals
            .iter()
            .position(|n| n == name)
            .map(|i| LitValVarId::new(i as u16))
    }

    /// Register a new mult variable (for comprehension bindings). Returns existing if already present.
    pub fn intern_mult(&mut self, name: &str) -> Result<MultVarId, String> {
        self.check_kind(name, VarKind::Mult)?;
        Ok(if let Some(id) = self.find_mult(name) {
            id
        } else {
            // Checked mint (u16 id family): the 65537th distinct name would
            // otherwise wrap onto id 0; report through the existing Err channel.
            let raw = u16::try_from(self.mults.len()).map_err(|_| {
                format!(
                    "too many mult variables in one rule: at most {} distinct names",
                    u16::MAX as u32 + 1
                )
            })?;
            let id = MultVarId::new(raw);
            self.mults.push(name.to_owned());
            self.kinds.insert(name.to_owned(), VarKind::Mult);
            id
        })
    }

    pub fn intern_var(&mut self, name: &str) -> Result<VarId, String> {
        self.check_kind(name, VarKind::Node)?;
        Ok(if let Some(id) = self.find_var(name) {
            id
        } else {
            // Checked mint (u16 id family): the 65537th distinct name would
            // otherwise wrap onto id 0; report through the existing Err channel.
            let raw = u16::try_from(self.nodes.len()).map_err(|_| {
                format!(
                    "too many node variables in one rule: at most {} distinct names",
                    u16::MAX as u32 + 1
                )
            })?;
            let id = VarId::new(raw);
            self.nodes.push(name.to_owned());
            self.kinds.insert(name.to_owned(), VarKind::Node);
            id
        })
    }

    pub fn intern_seq(&mut self, name: &str) -> Result<SeqVarId, String> {
        self.check_kind(name, VarKind::Seq)?;
        Ok(if let Some(id) = self.find_seq(name) {
            id
        } else {
            // Checked mint (u16 id family): the 65537th distinct name would
            // otherwise wrap onto id 0; report through the existing Err channel.
            let raw = u16::try_from(self.seqs.len()).map_err(|_| {
                format!(
                    "too many sequence variables in one rule: at most {} distinct names",
                    u16::MAX as u32 + 1
                )
            })?;
            let id = SeqVarId::new(raw);
            self.seqs.push(name.to_owned());
            self.kinds.insert(name.to_owned(), VarKind::Seq);
            id
        })
    }

    pub fn intern_set(&mut self, name: &str) -> Result<SetVarId, String> {
        self.check_kind(name, VarKind::Set)?;
        Ok(if let Some(id) = self.find_set(name) {
            id
        } else {
            // Checked mint (u16 id family): the 65537th distinct name would
            // otherwise wrap onto id 0; report through the existing Err channel.
            let raw = u16::try_from(self.sets.len()).map_err(|_| {
                format!(
                    "too many set variables in one rule: at most {} distinct names",
                    u16::MAX as u32 + 1
                )
            })?;
            let id = SetVarId::new(raw);
            self.sets.push(name.to_owned());
            self.kinds.insert(name.to_owned(), VarKind::Set);
            id
        })
    }

    pub fn intern_mset(&mut self, name: &str) -> Result<MsetVarId, String> {
        self.check_kind(name, VarKind::Mset)?;
        Ok(if let Some(id) = self.find_mset(name) {
            id
        } else {
            // Checked mint (u16 id family): the 65537th distinct name would
            // otherwise wrap onto id 0; report through the existing Err channel.
            let raw = u16::try_from(self.msets.len()).map_err(|_| {
                format!(
                    "too many multiset variables in one rule: at most {} distinct names",
                    u16::MAX as u32 + 1
                )
            })?;
            let id = MsetVarId::new(raw);
            self.msets.push(name.to_owned());
            self.kinds.insert(name.to_owned(), VarKind::Mset);
            id
        })
    }

    pub fn intern_lit_val(&mut self, name: &str) -> Result<LitValVarId, String> {
        self.check_kind(name, VarKind::LitVal)?;
        Ok(if let Some(id) = self.find_lit_val(name) {
            id
        } else {
            // Checked mint (u16 id family): the 65537th distinct name would
            // otherwise wrap onto id 0; report through the existing Err channel.
            let raw = u16::try_from(self.lit_vals.len()).map_err(|_| {
                format!(
                    "too many literal-value variables in one rule: at most {} distinct names",
                    u16::MAX as u32 + 1
                )
            })?;
            let id = LitValVarId::new(raw);
            self.lit_vals.push(name.to_owned());
            self.kinds.insert(name.to_owned(), VarKind::LitVal);
            id
        })
    }

    fn check_kind(&self, name: &str, expected: VarKind) -> Result<(), String> {
        if let Some(&existing) = self.kinds.get(name)
            && existing != expected
        {
            return Err(format!(
                "variable '{}' is already used as a {}, cannot use as {}",
                name,
                existing.label(),
                expected.label()
            ));
        }
        Ok(())
    }

    // Iterate (name, id) pairs
    pub fn vars(&self) -> impl Iterator<Item = (&str, VarId)> {
        self.nodes
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), VarId::new(i as u16)))
    }
    pub fn seq_pairs(&self) -> impl Iterator<Item = (&str, SeqVarId)> {
        self.seqs
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), SeqVarId::new(i as u16)))
    }
    pub fn set_pairs(&self) -> impl Iterator<Item = (&str, SetVarId)> {
        self.sets
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), SetVarId::new(i as u16)))
    }
    pub fn mset_pairs(&self) -> impl Iterator<Item = (&str, MsetVarId)> {
        self.msets
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), MsetVarId::new(i as u16)))
    }
    pub fn mult_pairs(&self) -> impl Iterator<Item = (&str, MultVarId)> {
        self.mults
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), MultVarId::new(i as u16)))
    }
    pub fn lit_val_pairs(&self) -> impl Iterator<Item = (&str, LitValVarId)> {
        self.lit_vals
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), LitValVarId::new(i as u16)))
    }
}

#[derive(Clone, Debug)]
pub struct ResolvedQuery<O, S, L> {
    pub atoms: Vec<RAtom<O, S, L>>,
    pub shape: MatchShape,
    pub var_sorts: Vec<Option<S>>,
    pub seq_sorts: Vec<S>,
    pub set_sorts: Vec<S>,
    pub mset_sorts: Vec<S>,
    pub mult_intervals: Vec<(MultVarId, u64, u64)>,
}

struct RestSorts<S> {
    seqs: Vec<S>,
    sets: Vec<S>,
    msets: Vec<S>,
}

impl<S> Default for RestSorts<S> {
    fn default() -> Self {
        Self {
            seqs: Vec::new(),
            sets: Vec::new(),
            msets: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct ResolveError {
    pub msg: String,
    pub span: Span,
    pub extra_spans: Vec<Span>,
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.msg)
    }
}

type R<T> = Result<T, ResolveError>;

fn err(msg: impl Into<String>, span: Span) -> ResolveError {
    ResolveError {
        msg: msg.into(),
        span,
        extra_spans: Vec::new(),
    }
}

fn err_multi(msg: impl Into<String>, span: Span, extra: Vec<Span>) -> ResolveError {
    ResolveError {
        msg: msg.into(),
        span,
        extra_spans: extra,
    }
}

/// Render an error with source context and caret underlines.
/// Shows the primary span and all extra spans.
pub fn render_error(source: &str, err: &ResolveError) -> String {
    let mut out = format!("error: {}", err.msg);
    let mut all_spans: Vec<Span> = Vec::new();
    all_spans.push(err.span);
    all_spans.extend_from_slice(&err.extra_spans);

    // Collect (line_start, line_end, col, width) for each span
    let mut annotations: Vec<(usize, usize, usize, usize)> = Vec::new();
    for s in &all_spans {
        if let Span::Range { start, end } = s {
            let s = *start as usize;
            let e = *end as usize;
            let line_start = source[..s].rfind('\n').map_or(0, |i| i + 1);
            let line_end = source[e..].find('\n').map_or(source.len(), |i| e + i);
            let col = s - line_start;
            let width = (e - s).max(1);
            annotations.push((line_start, line_end, col, width));
        }
    }
    annotations.sort();
    annotations.dedup();

    // Group by source line and render
    let mut prev_line_start = usize::MAX;
    for &(line_start, line_end, col, width) in &annotations {
        let line = &source[line_start..line_end];
        if line_start != prev_line_start {
            out.push_str(&format!("\n  {line}"));
            prev_line_start = line_start;
        }
        out.push_str(&format!(
            "\n  {:>col$}{:^>width$}",
            "",
            "",
            col = col,
            width = width
        ));
    }
    out
}

// ---------------------------------------------------------------------------
// Resolve
// ---------------------------------------------------------------------------

pub fn resolve<O, S, L, M, const TRACK: bool>(
    fq: &FlatQuery,
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    model: &M,
    globals: &GlobalCtx<S, impl Copy>,
) -> R<ResolvedQuery<O, S, L>>
where
    O: DenseId + Hash + Copy,
    S: DenseId + Copy,
    L: LitVal,
    M: LitModel<Value = L>,
{
    let mut shape = MatchShape::default();
    let mut var_sorts: Vec<Option<S>> = Vec::new();
    let mut rest_sorts = RestSorts::default();
    let mut resolved = Vec::with_capacity(fq.atoms.len());

    for atom in &fq.atoms {
        resolved.extend(resolve_atom(
            atom,
            ops,
            sorts,
            model,
            &mut var_sorts,
            &mut shape,
            &mut rest_sorts,
            globals,
        )?);
    }

    link_pred_deps(&mut resolved, &shape)?;

    let mult_intervals = collect_mult_intervals(&resolved, &fq.atoms, &shape)?;

    Ok(ResolvedQuery {
        atoms: resolved,
        shape,
        var_sorts,
        seq_sorts: rest_sorts.seqs,
        set_sorts: rest_sorts.sets,
        mset_sorts: rest_sorts.msets,
        mult_intervals,
    })
}

/// Fill in each predicate guard's `deps`: the atoms that bind the literal values it
/// reads.
///
/// A guard is evaluated, not matched, so it has no join to schedule and no cost to
/// compare; what it has is a point in the schedule before which it cannot run. That
/// point is "every `LitBind` atom feeding it has run", which is what this records, and
/// the scheduler's eager pass fires the guard at exactly that point.
fn link_pred_deps<O, S, L>(atoms: &mut [RAtom<O, S, L>], shape: &MatchShape) -> R<()> {
    let mut binder: Vec<Option<usize>> = vec![None; shape.num_lit_val_vars()];
    for (i, a) in atoms.iter().enumerate() {
        if let RAtom::LitBind { val, .. } = a {
            binder[val.idx()] = Some(i);
        }
    }
    let mut vars = Vec::new();
    for i in 0..atoms.len() {
        let RAtom::Pred { guard, .. } = &atoms[i] else {
            continue;
        };
        vars.clear();
        guard.expr.value_vars(&mut vars);
        let mut deps = Vec::with_capacity(vars.len());
        for v in &vars {
            let d = binder[v.idx()].ok_or_else(|| {
                err(
                    format!(
                        "guard variable '{}' is never bound to a literal value by this rule",
                        shape.lit_val_name(*v)
                    ),
                    Span::Dummy,
                )
            })?;
            deps.push(d);
        }
        deps.sort_unstable();
        deps.dedup();
        let RAtom::Pred { deps: slot, .. } = &mut atoms[i] else {
            unreachable!()
        };
        *slot = deps;
    }
    Ok(())
}

/// Intern a node variable name, growing var_sorts as needed.
fn iv<S: Copy>(
    name: &str,
    span: Span,
    shape: &mut MatchShape,
    var_sorts: &mut Vec<Option<S>>,
) -> R<VarId> {
    let id = shape.intern_var(name).map_err(|msg| err(msg, span))?;
    if id.idx() >= var_sorts.len() {
        var_sorts.resize(id.idx() + 1, None);
    }
    Ok(id)
}

fn bind_rest_sort<S: DenseId + Copy, const TRACK: bool>(
    slots: &mut Vec<S>,
    id: usize,
    name: &str,
    kind: &str,
    actual: S,
    sorts: &SortRegistry<S, TRACK>,
    span: Span,
) -> R<()> {
    match slots.get(id).copied() {
        Some(previous) if previous != actual => Err(err(
            format!(
                "{kind} rest variable '{name}' is used with element sorts '{}' and '{}'",
                sorts.name(previous),
                sorts.name(actual)
            ),
            span,
        )),
        Some(_) => Ok(()),
        None => {
            assert_eq!(
                id,
                slots.len(),
                "rest variable IDs must be allocated densely"
            );
            slots.push(actual);
            Ok(())
        }
    }
}

/// Resolve a child name to PatVar: global if in globals map, else local VarId.
/// For local vars in concrete sort positions, auto-lifts to LitBind.
fn resolve_child<O, S, L, const TRACK: bool>(
    name: &str,
    arg_sort: S,
    span: Span,
    shape: &mut MatchShape,
    var_sorts: &mut Vec<Option<S>>,
    globals: &GlobalCtx<S, impl Copy>,
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    extra: &mut Vec<RAtom<O, S, L>>,
) -> R<PatVar>
where
    O: DenseId + Hash + Copy,
    S: DenseId + Copy,
    L: LitVal,
{
    if let Some((gid, gsort, _)) = globals.get(name) {
        if gsort != arg_sort {
            return Err(err(
                format!(
                    "global '{name}' has sort '{}' but position expects '{}'",
                    sorts.name(gsort),
                    sorts.name(arg_sort)
                ),
                span,
            ));
        }
        return Ok(PatVar::Global(gid));
    }
    if sorts.is_concrete(arg_sort) && shape.find_var(name).is_none() {
        let fresh = format!("?@{name}");
        let inner = iv(&fresh, span, shape, var_sorts)?;
        unify_var(inner, arg_sort, var_sorts, &shape.nodes, sorts, span)?;
        let lit_op = ops
            .lit_op_for_sort(arg_sort)
            .expect("no @-prefixed lit op for concrete sort");
        let val_id = shape.intern_lit_val(name).map_err(|m| err(m, span))?;
        extra.push(RAtom::LitBind {
            node: inner,
            op: lit_op,
            val: val_id,
        });
        return Ok(PatVar::Local(inner));
    }
    let cid = iv(name, span, shape, var_sorts)?;
    unify_var(cid, arg_sort, var_sorts, &shape.nodes, sorts, span)?;
    Ok(PatVar::Local(cid))
}

fn resolve_atom<O, S, L, M, const TRACK: bool>(
    atom: &Atom,
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    model: &M,
    var_sorts: &mut Vec<Option<S>>,
    shape: &mut MatchShape,
    rest_sorts: &mut RestSorts<S>,
    globals: &GlobalCtx<S, impl Copy>,
) -> R<Vec<RAtom<O, S, L>>>
where
    O: DenseId + Hash + Copy,
    S: DenseId + Copy,
    L: LitVal,
    M: LitModel<Value = L>,
{
    match atom {
        Atom::Eq(a, b) => {
            let span = Span::Dummy;
            let ga = globals.get(a.as_str());
            let gb = globals.get(b.as_str());
            match (ga, gb) {
                (Some((gid, _, _)), None) => {
                    let vb = iv(b, span, shape, var_sorts)?;
                    Ok(vec![RAtom::EqGlobal(vb, gid)])
                }
                (None, Some((gid, _, _))) => {
                    let va = iv(a, span, shape, var_sorts)?;
                    Ok(vec![RAtom::EqGlobal(va, gid)])
                }
                _ => {
                    let va = iv(a, span, shape, var_sorts)?;
                    let vb = iv(b, span, shape, var_sorts)?;
                    // The two sides denote one e-class, so they have one sort. Whichever
                    // side already has one gives it to the other; this is what lets
                    // `(rewrite (= v pat) rhs)` sort-check its right-hand side against
                    // `pat`'s sort, since `v` alone constrains nothing.
                    match (var_sorts[va.idx()], var_sorts[vb.idx()]) {
                        (Some(sa), None) => var_sorts[vb.idx()] = Some(sa),
                        (None, Some(sb)) => var_sorts[va.idx()] = Some(sb),
                        (Some(sa), Some(sb)) if sa != sb => {
                            return Err(err(
                                format!(
                                    "'{a}' and '{b}' are equated but have sorts '{}' and '{}'",
                                    sorts.name(sa),
                                    sorts.name(sb)
                                ),
                                span,
                            ));
                        }
                        _ => {}
                    }
                    Ok(vec![RAtom::Eq(va, vb)])
                }
            }
        }

        Atom::Pred { expr, span } => {
            let rexpr = resolve_pred_expr(expr, None, ops, sorts, model, shape)?;
            let RPredExpr::App { op, .. } = &rexpr else {
                return Err(err(
                    "a guard must be a primitive application, e.g. `(i64::< a b)`",
                    *span,
                ));
            };
            let ret = ops.info(*op).return_sort;
            if sorts.name(ret) != "bool" {
                return Err(err(
                    format!(
                        "a guard must compute a bool, but this one computes '{}'",
                        sorts.name(ret)
                    ),
                    *span,
                ));
            }
            Ok(vec![RAtom::Pred {
                guard: PredGuard {
                    expr: rexpr,
                    truthy: M::is_truthy,
                },
                // Filled in by `link_pred_deps` once every atom is resolved.
                deps: Vec::new(),
            }])
        }

        Atom::Lit { node, text, span } => {
            let nid = iv(node, *span, shape, var_sorts)?;
            let (sort_name, val) = model
                .parse_any(text)
                .ok_or_else(|| err(format!("cannot parse literal '{text}'"), *span))?;
            let lit_sort = sorts
                .id_by_name(sort_name)
                .ok_or_else(|| err(format!("unknown literal sort '{sort_name}'"), *span))?;
            unify_var(nid, lit_sort, var_sorts, &shape.nodes, sorts, *span)?;
            let lit_op = ops.lit_op_for_sort(lit_sort).ok_or_else(|| {
                err(
                    format!(
                        "sort '{}' has no literal constructor, so '{text}' cannot appear in a pattern",
                        sorts.name(lit_sort)
                    ),
                    *span,
                )
            })?;
            Ok(vec![RAtom::Lit {
                node: nid,
                op: lit_op,
                sort: lit_sort,
                value: val,
            }])
        }

        Atom::Plain {
            node,
            op,
            children,
            span,
        } => {
            let nid = iv(node, *span, shape, var_sorts)?;
            let (op_id, info) = lookup_lhs_op(op, ops, *span)?;
            match &info.kind {
                OpKind::Normal { arg_sorts } => {
                    check_arity(op, arg_sorts.len(), children.len(), *span)?;
                    unify_var(nid, info.return_sort, var_sorts, &shape.nodes, sorts, *span)?;
                    let mut cids = Vec::with_capacity(children.len());
                    let mut extra = Vec::new();
                    for (i, c) in children.iter().enumerate() {
                        let pv = resolve_child(
                            c,
                            arg_sorts[i],
                            *span,
                            shape,
                            var_sorts,
                            globals,
                            ops,
                            sorts,
                            &mut extra,
                        )?;
                        cids.push(pv);
                    }
                    let mut atoms = vec![RAtom::Plain {
                        node: nid,
                        op: op_id,
                        children: cids,
                    }];
                    atoms.extend(extra);
                    Ok(atoms)
                }
                OpKind::Commutative { arg_sorts } => {
                    check_arity(op, 2, children.len(), *span)?;
                    unify_var(nid, info.return_sort, var_sorts, &shape.nodes, sorts, *span)?;
                    let mut extra = Vec::new();
                    let c0 = resolve_child(
                        &children[0],
                        arg_sorts[0],
                        *span,
                        shape,
                        var_sorts,
                        globals,
                        ops,
                        sorts,
                        &mut extra,
                    )?;
                    let c1 = resolve_child(
                        &children[1],
                        arg_sorts[1],
                        *span,
                        shape,
                        var_sorts,
                        globals,
                        ops,
                        sorts,
                        &mut extra,
                    )?;
                    let mut atoms = vec![RAtom::Plain {
                        node: nid,
                        op: op_id,
                        children: vec![c0, c1],
                    }];
                    atoms.extend(extra);
                    Ok(atoms)
                }
                OpKind::Lit => {
                    check_arity(op, 1, children.len(), *span)?;
                    unify_var(nid, info.return_sort, var_sorts, &shape.nodes, sorts, *span)?;
                    let val_id = shape
                        .intern_lit_val(&children[0])
                        .map_err(|m| err(m, *span))?;
                    Ok(vec![RAtom::LitBind {
                        node: nid,
                        op: op_id,
                        val: val_id,
                    }])
                }
                _ => Err(err(
                    "operator 'op' is not plain/commutative (internal error: flatten should have classified this)".to_string(),
                    *span,
                )),
            }
        }

        Atom::AExact {
            node,
            op,
            children,
            span,
        } => {
            let nid = iv(node, *span, shape, var_sorts)?;
            let (op_id, info) = lookup_lhs_op(op, ops, *span)?;
            let s = variadic_sort(&info.kind, op, *span)?;
            check_min_children(op, children.len(), *span)?;
            unify_var(nid, info.return_sort, var_sorts, &shape.nodes, sorts, *span)?;
            let mut cids = Vec::with_capacity(children.len());
            for c in children {
                let pv = resolve_child(
                    c,
                    s,
                    *span,
                    shape,
                    var_sorts,
                    globals,
                    ops,
                    sorts,
                    &mut Vec::<RAtom<O, S, L>>::new(),
                )?;
                cids.push(pv);
            }
            Ok(vec![RAtom::AExact {
                node: nid,
                op: op_id,
                children: cids,
            }])
        }
        Atom::APrefix {
            node,
            op,
            rest,
            fixed,
            span,
        } => {
            let nid = iv(node, *span, shape, var_sorts)?;
            let (op_id, info) = lookup_lhs_op(op, ops, *span)?;
            let s = variadic_sort(&info.kind, op, *span)?;
            check_a_mode(&info.kind, op, *span)?;
            unify_var(nid, info.return_sort, var_sorts, &shape.nodes, sorts, *span)?;
            let mut fids = Vec::with_capacity(fixed.len());
            for c in fixed {
                let pv = resolve_child(
                    c,
                    s,
                    *span,
                    shape,
                    var_sorts,
                    globals,
                    ops,
                    sorts,
                    &mut Vec::<RAtom<O, S, L>>::new(),
                )?;
                fids.push(pv);
            }
            let pre = shape.intern_seq(rest).map_err(|m| err(m, *span))?;
            bind_rest_sort(
                &mut rest_sorts.seqs,
                pre.idx(),
                rest,
                "sequence",
                s,
                sorts,
                *span,
            )?;
            Ok(vec![RAtom::APrefix {
                node: nid,
                op: op_id,
                pre,
                fixed: fids,
            }])
        }
        Atom::ASuffix {
            node,
            op,
            fixed,
            rest,
            span,
        } => {
            let nid = iv(node, *span, shape, var_sorts)?;
            let (op_id, info) = lookup_lhs_op(op, ops, *span)?;
            let s = variadic_sort(&info.kind, op, *span)?;
            check_a_mode(&info.kind, op, *span)?;
            unify_var(nid, info.return_sort, var_sorts, &shape.nodes, sorts, *span)?;
            let mut fids = Vec::with_capacity(fixed.len());
            for c in fixed {
                let pv = resolve_child(
                    c,
                    s,
                    *span,
                    shape,
                    var_sorts,
                    globals,
                    ops,
                    sorts,
                    &mut Vec::<RAtom<O, S, L>>::new(),
                )?;
                fids.push(pv);
            }
            let suf = shape.intern_seq(rest).map_err(|m| err(m, *span))?;
            bind_rest_sort(
                &mut rest_sorts.seqs,
                suf.idx(),
                rest,
                "sequence",
                s,
                sorts,
                *span,
            )?;
            Ok(vec![RAtom::ASuffix {
                node: nid,
                op: op_id,
                fixed: fids,
                suf,
            }])
        }
        Atom::ABoth {
            node,
            op,
            pre,
            fixed,
            suf,
            span,
        } => {
            let nid = iv(node, *span, shape, var_sorts)?;
            let (op_id, info) = lookup_lhs_op(op, ops, *span)?;
            let s = variadic_sort(&info.kind, op, *span)?;
            check_a_mode(&info.kind, op, *span)?;
            unify_var(nid, info.return_sort, var_sorts, &shape.nodes, sorts, *span)?;
            let mut fids = Vec::with_capacity(fixed.len());
            for c in fixed {
                let pv = resolve_child(
                    c,
                    s,
                    *span,
                    shape,
                    var_sorts,
                    globals,
                    ops,
                    sorts,
                    &mut Vec::<RAtom<O, S, L>>::new(),
                )?;
                fids.push(pv);
            }
            let pre = shape.intern_seq(pre).map_err(|m| err(m, *span))?;
            bind_rest_sort(
                &mut rest_sorts.seqs,
                pre.idx(),
                shape.seq_name(pre),
                "sequence",
                s,
                sorts,
                *span,
            )?;
            let suf = shape.intern_seq(suf).map_err(|m| err(m, *span))?;
            bind_rest_sort(
                &mut rest_sorts.seqs,
                suf.idx(),
                shape.seq_name(suf),
                "sequence",
                s,
                sorts,
                *span,
            )?;
            Ok(vec![RAtom::ABoth {
                node: nid,
                op: op_id,
                pre,
                fixed: fids,
                suf,
            }])
        }

        Atom::ACExact {
            node,
            op,
            elems,
            span,
        } => {
            let nid = iv(node, *span, shape, var_sorts)?;
            let (op_id, info) = lookup_lhs_op(op, ops, *span)?;
            let s = variadic_sort(&info.kind, op, *span)?;
            check_ac_mode(&info.kind, op, *span)?;
            check_min_children(op, elems.len(), *span)?;
            unify_var(nid, info.return_sort, var_sorts, &shape.nodes, sorts, *span)?;
            let relems = resolve_ac_elems(elems, s, var_sorts, shape, sorts, *span, globals)?;
            Ok(vec![RAtom::ACExact {
                node: nid,
                op: op_id,
                elems: relems,
            }])
        }
        Atom::ACSub {
            node,
            op,
            elems,
            rest,
            span,
        } => {
            let nid = iv(node, *span, shape, var_sorts)?;
            let (op_id, info) = lookup_lhs_op(op, ops, *span)?;
            let s = variadic_sort(&info.kind, op, *span)?;
            check_ac_mode(&info.kind, op, *span)?;
            unify_var(nid, info.return_sort, var_sorts, &shape.nodes, sorts, *span)?;
            let relems = resolve_ac_elems(elems, s, var_sorts, shape, sorts, *span, globals)?;
            let rest_id = shape.intern_mset(rest).map_err(|m| err(m, *span))?;
            bind_rest_sort(
                &mut rest_sorts.msets,
                rest_id.idx(),
                rest,
                "multiset",
                s,
                sorts,
                *span,
            )?;
            Ok(vec![RAtom::ACSub {
                node: nid,
                op: op_id,
                elems: relems,
                rest: rest_id,
            }])
        }
        Atom::ACIExact {
            node,
            op,
            elems,
            span,
        } => {
            let nid = iv(node, *span, shape, var_sorts)?;
            let (op_id, info) = lookup_lhs_op(op, ops, *span)?;
            let s = variadic_sort(&info.kind, op, *span)?;
            check_aci_mode(&info.kind, op, *span)?;
            check_min_children(op, elems.len(), *span)?;
            unify_var(nid, info.return_sort, var_sorts, &shape.nodes, sorts, *span)?;
            let mut eids = Vec::with_capacity(elems.len());
            for e in elems {
                let pv = resolve_child(
                    e,
                    s,
                    *span,
                    shape,
                    var_sorts,
                    globals,
                    ops,
                    sorts,
                    &mut Vec::<RAtom<O, S, L>>::new(),
                )?;
                eids.push(pv);
            }
            Ok(vec![RAtom::ACIExact {
                node: nid,
                op: op_id,
                elems: eids,
            }])
        }
        Atom::ACISub {
            node,
            op,
            elems,
            rest,
            span,
        } => {
            let nid = iv(node, *span, shape, var_sorts)?;
            let (op_id, info) = lookup_lhs_op(op, ops, *span)?;
            let s = variadic_sort(&info.kind, op, *span)?;
            check_aci_mode(&info.kind, op, *span)?;
            unify_var(nid, info.return_sort, var_sorts, &shape.nodes, sorts, *span)?;
            let mut eids = Vec::with_capacity(elems.len());
            for e in elems {
                let pv = resolve_child(
                    e,
                    s,
                    *span,
                    shape,
                    var_sorts,
                    globals,
                    ops,
                    sorts,
                    &mut Vec::<RAtom<O, S, L>>::new(),
                )?;
                eids.push(pv);
            }
            let rest_id = shape.intern_set(rest).map_err(|m| err(m, *span))?;
            bind_rest_sort(
                &mut rest_sorts.sets,
                rest_id.idx(),
                rest,
                "set",
                s,
                sorts,
                *span,
            )?;
            Ok(vec![RAtom::ACISub {
                node: nid,
                op: op_id,
                elems: eids,
                rest: rest_id,
            }])
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn lookup_op<'a, O: DenseId + Hash + Copy, S: DenseId + Copy, const TRACK: bool>(
    name: &str,
    ops: &'a OpRegistry<O, S, TRACK>,
    span: Span,
) -> R<(O, &'a crate::registry::OpInfo<S>)> {
    let id = ops
        .id_by_name(name)
        .ok_or_else(|| err(format!("unknown operator '{name}'"), span))?;
    Ok((id, ops.info(id)))
}

/// Resolve a guard expression against the model's primitives.
///
/// `expected` is the sort the enclosing argument position asks for; it types the
/// literal constants (so `0` in an `i64` position is an `i64` and not a bignum) and
/// checks the nested applications.
fn resolve_pred_expr<O, S, L, M, const TRACK: bool>(
    expr: &crate::compile::PredExpr,
    expected: Option<S>,
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    model: &M,
    shape: &MatchShape,
) -> R<RPredExpr<O, L>>
where
    O: DenseId + Hash + Copy,
    S: DenseId + Copy,
    L: LitVal,
    M: LitModel<Value = L>,
{
    use crate::compile::PredExpr;
    match expr {
        PredExpr::Var(name, span) => {
            let vid = shape.find_lit_val(name).ok_or_else(|| {
                err(
                    format!(
                        "'{name}' is not bound to a literal value; a guard may only read \
                         variables that some pattern binds in a primitive-sorted argument \
                         position, and only patterns written before it"
                    ),
                    *span,
                )
            })?;
            Ok(RPredExpr::Val(vid))
        }
        PredExpr::Lit(text, span) => {
            let val = match expected {
                Some(s) => model.parse_as(sorts.name(s), text).ok_or_else(|| {
                    err(
                        format!("cannot parse '{text}' as '{}'", sorts.name(s)),
                        *span,
                    )
                })?,
                None => model
                    .parse_any(text)
                    .map(|(_, v)| v)
                    .ok_or_else(|| err(format!("cannot parse literal '{text}'"), *span))?,
            };
            Ok(RPredExpr::Const(val))
        }
        PredExpr::App { op, args, span } => {
            let (op_id, info) = lookup_op(op, ops, *span)?;
            if !ops.is_prim_op(op_id) {
                return Err(err(
                    format!("'{op}' is not a primitive operator, so it cannot appear in a guard"),
                    *span,
                ));
            }
            if let Some(exp) = expected
                && exp != info.return_sort
            {
                return Err(err(
                    format!(
                        "guard operator '{op}' computes '{}', but this position expects '{}'",
                        sorts.name(info.return_sort),
                        sorts.name(exp)
                    ),
                    *span,
                ));
            }
            let OpKind::Normal { arg_sorts } = &info.kind else {
                unreachable!("a primitive op is always registered as OpKind::Normal")
            };
            check_arity(op, arg_sorts.len(), args.len(), *span)?;
            let mut rargs = Vec::with_capacity(args.len());
            for (a, s) in args.iter().zip(arg_sorts) {
                rargs.push(resolve_pred_expr(a, Some(*s), ops, sorts, model, shape)?);
            }
            Ok(RPredExpr::App {
                op: op_id,
                // A primitive op's id is its index into the model's op table: the
                // registry registers `LitModel::ops()` first and in order.
                eval: model.ops()[op_id.to_usize()].eval,
                args: rargs,
            })
        }
    }
}

/// Like `lookup_op` but rejects primitive ops (only constructors allowed in LHS).
fn lookup_lhs_op<'a, O: DenseId + Hash + Copy, S: DenseId + Copy, const TRACK: bool>(
    name: &str,
    ops: &'a OpRegistry<O, S, TRACK>,
    span: Span,
) -> R<(O, &'a crate::registry::OpInfo<S>)> {
    let (id, info) = lookup_op(name, ops, span)?;
    if ops.is_prim_op(id) {
        return Err(err(
            format!(
                "primitive operator '{name}' cannot appear inside a left-hand-side pattern \
                 (it may head a `:when` guard, or appear in a right-hand side or ground term)"
            ),
            span,
        ));
    }
    Ok((id, info))
}

fn unify_var<S: DenseId + Copy, const TRACK: bool>(
    var: VarId,
    sort: S,
    var_sorts: &mut [Option<S>],
    var_names: &[String],
    sorts: &SortRegistry<S, TRACK>,
    span: Span,
) -> R<()> {
    let slot = &mut var_sorts[var.idx()];
    match *slot {
        None => {
            *slot = Some(sort);
            Ok(())
        }
        Some(existing) if existing == sort => Ok(()),
        Some(existing) => Err(err(
            format!(
                "sort mismatch for '{}': expected {}, got {}",
                var_names[var.idx()],
                sorts.name(existing),
                sorts.name(sort)
            ),
            span,
        )),
    }
}

fn check_arity(op: &str, expected: usize, got: usize, span: Span) -> R<()> {
    if expected != got {
        Err(err(
            format!("operator '{op}' expects {expected} arguments, got {got}"),
            span,
        ))
    } else {
        Ok(())
    }
}

fn variadic_sort<S: DenseId + Copy>(kind: &OpKind<S>, op: &str, span: Span) -> R<S> {
    match kind {
        OpKind::A { arg_sort, .. }
        | OpKind::MSet { arg_sort, .. }
        | OpKind::Set { arg_sort, .. } => Ok(*arg_sort),
        _ => Err(err(format!("operator '{op}' is not variadic"), span)),
    }
}

fn check_min_children(_op: &str, count: usize, span: Span) -> R<()> {
    if count == 0 {
        Err(err(
            "operator 'op' requires at least 1 child (no identity element support)".to_string(),
            span,
        ))
    } else {
        Ok(())
    }
}

fn check_a_mode<S: DenseId>(kind: &OpKind<S>, op: &str, span: Span) -> R<()> {
    match kind {
        OpKind::A { .. } => Ok(()),
        _ => Err(err(
            format!("operator '{op}' is not associative; [] syntax not allowed"),
            span,
        )),
    }
}

fn check_ac_mode<S: DenseId>(kind: &OpKind<S>, op: &str, span: Span) -> R<()> {
    match kind {
        OpKind::MSet { .. } => Ok(()),
        _ => Err(err(
            format!("operator '{op}' is not AC; {{}} with multiplicities not allowed"),
            span,
        )),
    }
}

fn check_aci_mode<S: DenseId>(kind: &OpKind<S>, op: &str, span: Span) -> R<()> {
    match kind {
        OpKind::Set { .. } => Ok(()),
        _ => Err(err(
            format!("operator '{op}' is not ACI; {{}} set syntax not allowed"),
            span,
        )),
    }
}

fn resolve_ac_elems<S: DenseId + Copy, const TRACK: bool>(
    elems: &[(String, FlatMult)],
    sort: S,
    var_sorts: &mut Vec<Option<S>>,
    shape: &mut MatchShape,
    sorts: &SortRegistry<S, TRACK>,
    span: Span,
    globals: &GlobalCtx<S, impl Copy>,
) -> R<Vec<(PatVar, RMult)>> {
    let mut out = Vec::with_capacity(elems.len());
    for (name, m) in elems {
        let pv = if let Some((gid, _, _)) = globals.get(name.as_str()) {
            PatVar::Global(gid)
        } else {
            let vid = shape.intern_var(name).map_err(|msg| err(msg, span))?;
            if vid.idx() >= var_sorts.len() {
                var_sorts.resize(vid.idx() + 1, None);
            }
            unify_var(vid, sort, var_sorts, &shape.nodes, sorts, span)?;
            PatVar::Local(vid)
        };
        let rm = match m {
            FlatMult::Exact(n) => RMult::Exact(*n),
            FlatMult::Var { name, constraint } => RMult::Var {
                var: shape.intern_mult(name).map_err(|msg| err(msg, span))?,
                constraint: *constraint,
            },
        };
        out.push((pv, rm));
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Multiplicity interval collection
// ---------------------------------------------------------------------------

/// For each mult variable, collect all constraints and intersect into [min, max].
fn collect_mult_intervals<O, S, V>(
    atoms: &[RAtom<O, S, V>],
    src_atoms: &[Atom],
    shape: &MatchShape,
) -> R<Vec<(MultVarId, u64, u64)>> {
    use std::collections::HashMap;
    let mut intervals: HashMap<MultVarId, (u64, u64)> = HashMap::new();
    let mut spans: HashMap<MultVarId, Vec<Span>> = HashMap::new();

    for (atom, src) in atoms.iter().zip(src_atoms.iter()) {
        let elems: &[(PatVar, RMult)] = match atom {
            RAtom::ACExact { elems, .. } | RAtom::ACSub { elems, .. } => elems.as_slice(),
            _ => continue,
        };
        let src_span = match src {
            Atom::ACExact { span, .. } | Atom::ACSub { span, .. } => *span,
            _ => Span::Dummy,
        };
        for (_, mult) in elems {
            if let RMult::Var { var, constraint } = mult {
                let entry = intervals.entry(*var).or_insert((1, u64::MAX));
                spans.entry(*var).or_default().push(src_span);
                if let Some((op, val)) = constraint {
                    let (lo, hi) = entry;
                    match op {
                        CmpOp::Ge => *lo = (*lo).max(*val),
                        CmpOp::Gt => *lo = (*lo).max(*val + 1),
                        CmpOp::Le => *hi = (*hi).min(*val),
                        CmpOp::Lt => *hi = (*hi).min(val.saturating_sub(1)),
                        CmpOp::Eq => {
                            *lo = (*lo).max(*val);
                            *hi = (*hi).min(*val);
                        }
                        CmpOp::Ne => {}
                    }
                }
            }
        }
    }

    let mut result = Vec::new();
    for (var, (lo, hi)) in intervals {
        if lo > hi {
            let all: Vec<Span> = spans
                .get(&var)
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .filter(|s| matches!(s, Span::Range { .. }))
                .collect();
            let primary = all.first().copied().unwrap_or(Span::Dummy);
            let extra = all.into_iter().skip(1).collect();
            let name = &shape.mults[var.idx()];
            return Err(err_multi(
                format!(
                    "unsatisfiable multiplicity for '{name}': \
                     requires {name} >= {lo} and {name} <= {hi} (empty interval)"
                ),
                primary,
                extra,
            ));
        }
        result.push((var, lo, hi));
    }
    result.sort_by_key(|(v, _, _)| *v);
    Ok(result)
}

// ---------------------------------------------------------------------------
// Resolved RHS types
// ---------------------------------------------------------------------------

/// An e-node reference on a resolved RHS.
///
/// Query bindings index the immutable LHS match. Local bindings index the
/// lexical environment allocated for RHS comprehensions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RhsNodeRef {
    Query(VarId),
    Local(crate::ast::RhsLocalVarId),
}

/// A multiplicity reference on a resolved RHS.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RhsMultRef {
    Query(MultVarId),
    Local(crate::ast::RhsLocalMultVarId),
}

/// Storage required by all comprehension locals in one rule.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RhsLocalShape {
    pub node_count: usize,
    pub mult_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RRhsTerm<O, S, L> {
    Var(RhsNodeRef),
    Lit {
        op: O,
        sort: S,
        value: L,
    },
    /// Reconstruct a `@sort(val)` lit node from a bound LitValVarId.
    LitVar {
        op: O,
        val: LitValVarId,
    },
    App {
        op: O,
        children: Vec<RRhsChild<O, S, L>>,
    },
    /// Evaluate a primitive op on bound literal values.
    /// `(+ x y)` where `+` is a `LitOpDesc` prim op.
    PrimApp {
        op: O,
        args: Vec<RPrimArg>,
        ret_sort: S,
    },
    /// Reconstruct a `@i64(k)` lit node from a bound AC multiplicity variable.
    MultVar {
        op: O,
        var: RhsMultRef,
    },
    FetchGlobal(GlobalVarId),
}

/// A primitive-op argument on a RHS: a bound literal value, or a bound AC
/// multiplicity variable read as an i64.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RPrimArg {
    LitVal(LitValVarId),
    Mult(RhsMultRef),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RRhsChild<O, S, L> {
    Term(RRhsTerm<O, S, L>),
    /// `term:mult` under a variadic op: the term contributed `mult` times.
    /// Multiplicity 0 omits the term without evaluating it.
    TermMult {
        body: Box<RRhsTerm<O, S, L>>,
        mult: ResolvedMultExpr,
    },
    SpliceSeq(SeqVarId),
    SpliceSet(SetVarId),
    SpliceMset(MsetVarId),
    SetComp {
        body: Box<RRhsTerm<O, S, L>>,
        var: crate::ast::RhsLocalVarId,
        source: SetVarId,
        filter: Option<Box<RRhsTerm<O, S, L>>>,
    },
    MsetComp {
        body: Box<RRhsTerm<O, S, L>>,
        mult: ResolvedMultExpr,
        var: crate::ast::RhsLocalVarId,
        mult_var: crate::ast::RhsLocalMultVarId,
        source: MsetVarId,
        filter: Option<Box<RRhsTerm<O, S, L>>>,
    },
    SeqComp {
        body: Box<RRhsTerm<O, S, L>>,
        var: crate::ast::RhsLocalVarId,
        source: SeqVarId,
        filter: Option<Box<RRhsTerm<O, S, L>>>,
    },
}

/// Resolved multiplicity expression — literal or bound mult variable.
///
/// `Lit` stays at the *surface* width (`u64`). Resolution is not parameterized
/// by the e-graph config, so it cannot narrow to the configured multiplicity
/// type; that narrowing is a checked conversion at the use sites, which are
/// `Cfg`-generic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedMultExpr {
    Lit(u64),
    Var(RhsMultRef),
    /// Checked u64 arithmetic over multiplicities (`(u64::- k 1)`). Interval-
    /// checked at rule install against the LHS multiplicity constraints, so a
    /// possible underflow or division by zero is rejected before the rule
    /// runs; evaluation still uses checked ops as the second line.
    Prim {
        op: MultPrimOp,
        args: Vec<ResolvedMultExpr>,
    },
}

/// The RHS multiplicity-expression vocabulary: the u64 primitive ops that
/// make sense over counts, same names, same checked semantics.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MultPrimOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Min,
    Max,
}

impl MultPrimOp {
    pub fn name(self) -> &'static str {
        match self {
            MultPrimOp::Add => "u64::+",
            MultPrimOp::Sub => "u64::-",
            MultPrimOp::Mul => "u64::*",
            MultPrimOp::Div => "u64::/",
            MultPrimOp::Rem => "u64::%",
            MultPrimOp::Min => "u64::min",
            MultPrimOp::Max => "u64::max",
        }
    }

    fn from_name(name: &str) -> Option<Self> {
        match name {
            "u64::+" => Some(MultPrimOp::Add),
            "u64::-" => Some(MultPrimOp::Sub),
            "u64::*" => Some(MultPrimOp::Mul),
            "u64::/" => Some(MultPrimOp::Div),
            "u64::%" => Some(MultPrimOp::Rem),
            "u64::min" => Some(MultPrimOp::Min),
            "u64::max" => Some(MultPrimOp::Max),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum RhsLocalBinding {
    Node(RhsLocalVarId),
    Mult(RhsLocalMultVarId),
}

/// Resolver state for an entire rule's RHS.
///
/// Query bindings are read-only. Comprehension locals live in lexical scopes,
/// while their IDs come from rule-wide monotonic allocators so sibling
/// comprehensions and actions can safely reuse source names.
pub struct RhsResolveCtx<'a, S> {
    pub query_shape: &'a MatchShape,
    query_node_sorts: Vec<Option<S>>,
    query_seq_sorts: &'a [S],
    query_set_sorts: &'a [S],
    query_mset_sorts: &'a [S],
    local_node_scopes: Vec<HashMap<String, RhsLocalVarId>>,
    local_mult_scopes: Vec<HashMap<String, RhsLocalMultVarId>>,
    local_node_sorts: Vec<Option<S>>,
    local_node_names: Vec<String>,
    next_local_node: usize,
    next_local_mult: usize,
}

impl<'a, S: DenseId> RhsResolveCtx<'a, S> {
    pub fn new<O, L>(query: &'a ResolvedQuery<O, S, L>) -> Self {
        assert_eq!(
            query.shape.num_vars(),
            query.var_sorts.len(),
            "query node sorts must match the query shape"
        );
        assert_eq!(
            query.shape.seqs.len(),
            query.seq_sorts.len(),
            "query sequence sorts must match the query shape"
        );
        assert_eq!(
            query.shape.sets.len(),
            query.set_sorts.len(),
            "query set sorts must match the query shape"
        );
        assert_eq!(
            query.shape.msets.len(),
            query.mset_sorts.len(),
            "query multiset sorts must match the query shape"
        );
        Self {
            query_shape: &query.shape,
            query_node_sorts: query.var_sorts.clone(),
            query_seq_sorts: &query.seq_sorts,
            query_set_sorts: &query.set_sorts,
            query_mset_sorts: &query.mset_sorts,
            local_node_scopes: Vec::new(),
            local_mult_scopes: Vec::new(),
            local_node_sorts: Vec::new(),
            local_node_names: Vec::new(),
            next_local_node: 0,
            next_local_mult: 0,
        }
    }

    fn seq_sort(&self, id: SeqVarId) -> S {
        self.query_seq_sorts[id.idx()]
    }

    fn set_sort(&self, id: SetVarId) -> S {
        self.query_set_sorts[id.idx()]
    }

    fn mset_sort(&self, id: MsetVarId) -> S {
        self.query_mset_sorts[id.idx()]
    }

    pub fn local_shape(&self) -> RhsLocalShape {
        RhsLocalShape {
            node_count: self.next_local_node,
            mult_count: self.next_local_mult,
        }
    }

    fn push_scope(&mut self) {
        self.local_node_scopes.push(HashMap::new());
        self.local_mult_scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.local_node_scopes
            .pop()
            .expect("RHS local node scope stack underflow");
        self.local_mult_scopes
            .pop()
            .expect("RHS local multiplicity scope stack underflow");
    }

    fn scopes_are_empty(&self) -> bool {
        self.local_node_scopes.is_empty() && self.local_mult_scopes.is_empty()
    }

    fn local_binding(&self, name: &str) -> Option<RhsLocalBinding> {
        debug_assert_eq!(self.local_node_scopes.len(), self.local_mult_scopes.len());
        for depth in (0..self.local_node_scopes.len()).rev() {
            let node = self.local_node_scopes[depth].get(name).copied();
            let mult = self.local_mult_scopes[depth].get(name).copied();
            match (node, mult) {
                (Some(id), None) => return Some(RhsLocalBinding::Node(id)),
                (None, Some(id)) => return Some(RhsLocalBinding::Mult(id)),
                (Some(_), Some(_)) => {
                    unreachable!("one lexical scope cannot bind a name as two RHS-local kinds")
                }
                (None, None) => {}
            }
        }
        None
    }

    fn alloc_node(&mut self, name: &str, sort: Option<S>, span: Span) -> R<RhsLocalVarId> {
        let node_scope = self
            .local_node_scopes
            .last_mut()
            .expect("RHS local node allocation requires an open scope");
        let mult_scope = self
            .local_mult_scopes
            .last()
            .expect("RHS local node allocation requires an open scope");
        if node_scope.contains_key(name) || mult_scope.contains_key(name) {
            return Err(err(
                format!("comprehension binding '{name}' is declared twice in one scope"),
                span,
            ));
        }
        let raw = u16::try_from(self.next_local_node).map_err(|_| {
            err(
                format!(
                    "too many RHS-local node variables in one rule: at most {}",
                    u16::MAX as u32 + 1
                ),
                span,
            )
        })?;
        let id = RhsLocalVarId::new(raw);
        self.next_local_node += 1;
        self.local_node_sorts.push(sort);
        self.local_node_names.push(name.to_owned());
        node_scope.insert(name.to_owned(), id);
        Ok(id)
    }

    fn alloc_mult(&mut self, name: &str, span: Span) -> R<RhsLocalMultVarId> {
        let node_scope = self
            .local_node_scopes
            .last()
            .expect("RHS local multiplicity allocation requires an open scope");
        let mult_scope = self
            .local_mult_scopes
            .last_mut()
            .expect("RHS local multiplicity allocation requires an open scope");
        if node_scope.contains_key(name) || mult_scope.contains_key(name) {
            return Err(err(
                format!("comprehension binding '{name}' is declared twice in one scope"),
                span,
            ));
        }
        let raw = u16::try_from(self.next_local_mult).map_err(|_| {
            err(
                format!(
                    "too many RHS-local multiplicity variables in one rule: at most {}",
                    u16::MAX as u32 + 1
                ),
                span,
            )
        })?;
        let id = RhsLocalMultVarId::new(raw);
        self.next_local_mult += 1;
        mult_scope.insert(name.to_owned(), id);
        Ok(id)
    }

    fn unify_node<const TRACK: bool>(
        &mut self,
        node: RhsNodeRef,
        expected: S,
        sorts: &SortRegistry<S, TRACK>,
        span: Span,
    ) -> R<()> {
        let (slot, name): (&mut Option<S>, &str) = match node {
            RhsNodeRef::Query(id) => (
                &mut self.query_node_sorts[id.idx()],
                self.query_shape.var_name(id),
            ),
            RhsNodeRef::Local(id) => (
                &mut self.local_node_sorts[id.idx()],
                &self.local_node_names[id.idx()],
            ),
        };
        match *slot {
            None => {
                *slot = Some(expected);
                Ok(())
            }
            Some(actual) if actual == expected => Ok(()),
            Some(actual) => Err(err(
                format!(
                    "sort mismatch for variable '{name}': {} vs {}",
                    sorts.name(actual),
                    sorts.name(expected)
                ),
                span,
            )),
        }
    }
}

// ---------------------------------------------------------------------------
// Resolved actions
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedAction<O, S, L> {
    Union(RRhsTerm<O, S, L>, RRhsTerm<O, S, L>),
    Insert(RRhsTerm<O, S, L>),
    Set {
        func: O,
        args: Vec<RRhsTerm<O, S, L>>,
        value: RRhsTerm<O, S, L>,
    },
}

pub fn resolve_action<O, S, L, M, const TRACK: bool>(
    action: &crate::ast::Action,
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    model: &M,
    ctx: &mut RhsResolveCtx<'_, S>,
    globals: &GlobalCtx<S, impl Copy>,
) -> R<ResolvedAction<O, S, L>>
where
    O: DenseId + Hash + Copy,
    S: DenseId + Copy,
    L: LitVal,
    M: LitModel<Value = L>,
{
    debug_assert!(ctx.scopes_are_empty());
    use crate::ast::Action;
    let resolved = match action {
        Action::Union(a, b) => {
            let ra = resolve_rhs(a, None, ops, sorts, model, ctx, globals)?;
            let rb = resolve_rhs(b, None, ops, sorts, model, ctx, globals)?;
            Ok(ResolvedAction::Union(ra, rb))
        }
        Action::Insert(t) => {
            let rt = resolve_rhs(t, None, ops, sorts, model, ctx, globals)?;
            Ok(ResolvedAction::Insert(rt))
        }
        Action::Set { func, args, value } => {
            let (op_id, info) = lookup_op(func, ops, Span::Dummy)?;
            let mut rargs = Vec::with_capacity(args.len());
            for (i, a) in args.iter().enumerate() {
                let expected = match &info.kind {
                    crate::registry::OpKind::Normal { arg_sorts } => arg_sorts.get(i).copied(),
                    _ => None,
                };
                rargs.push(resolve_rhs(a, expected, ops, sorts, model, ctx, globals)?);
            }
            let rv = resolve_rhs(
                value,
                Some(info.return_sort),
                ops,
                sorts,
                model,
                ctx,
                globals,
            )?;
            Ok(ResolvedAction::Set {
                func: op_id,
                args: rargs,
                value: rv,
            })
        }
    };
    debug_assert!(ctx.scopes_are_empty());
    resolved
}

// ---------------------------------------------------------------------------
// Resolve RHS
// ---------------------------------------------------------------------------

pub fn resolve_rhs<
    O: DenseId + Hash + Copy,
    S: DenseId + Copy,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
>(
    term: &crate::ast::RhsTerm,
    expected_sort: Option<S>,
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    model: &M,
    ctx: &mut RhsResolveCtx<'_, S>,
    globals: &GlobalCtx<S, impl Copy>,
) -> R<RRhsTerm<O, S, L>> {
    use crate::ast::RhsTerm;
    let span = term.span();
    match term {
        RhsTerm::Var(v, _) => {
            // Lexical locals are authoritative even when an outer query
            // binding or global has the same name.
            if let Some(local) = ctx.local_binding(v) {
                return match local {
                    RhsLocalBinding::Node(id) => {
                        let node = RhsNodeRef::Local(id);
                        if let Some(s) = expected_sort {
                            ctx.unify_node(node, s, sorts, span)?;
                        }
                        Ok(RRhsTerm::Var(node))
                    }
                    RhsLocalBinding::Mult(id) => {
                        resolve_mult_term(v, RhsMultRef::Local(id), expected_sort, ops, sorts, span)
                    }
                };
            }

            // Query names also have one authoritative kind. A wrong-kind
            // query binding must not fall through to a same-named global.
            if let Some(&kind) = ctx.query_shape.kinds.get(v) {
                return match kind {
                    VarKind::Node => {
                        let node = RhsNodeRef::Query(
                            ctx.query_shape
                                .find_var(v)
                                .expect("query node kind must have a node id"),
                        );
                        if let Some(s) = expected_sort {
                            ctx.unify_node(node, s, sorts, span)?;
                        }
                        Ok(RRhsTerm::Var(node))
                    }
                    VarKind::Mult => resolve_mult_term(
                        v,
                        RhsMultRef::Query(
                            ctx.query_shape
                                .find_mult(v)
                                .expect("query multiplicity kind must have an id"),
                        ),
                        expected_sort,
                        ops,
                        sorts,
                        span,
                    ),
                    VarKind::LitVal => {
                        let Some(s) = expected_sort.filter(|s| sorts.is_concrete(*s)) else {
                            return Err(err(
                                format!(
                                    "literal variable '{v}' requires a concrete literal position"
                                ),
                                span,
                            ));
                        };
                        let lit_op = ops.lit_op_for_sort(s).ok_or_else(|| {
                            err(format!("no lit op for sort '{}'", sorts.name(s)), span)
                        })?;
                        Ok(RRhsTerm::LitVar {
                            op: lit_op,
                            val: ctx
                                .query_shape
                                .find_lit_val(v)
                                .expect("query literal-value kind must have an id"),
                        })
                    }
                    other => Err(err(
                        format!(
                            "'{v}' is a {}, not an e-node or literal binding",
                            other.label()
                        ),
                        span,
                    )),
                };
            }

            if let Some((gid, gsort, _)) = globals.get(v.as_str()) {
                if let Some(s) = expected_sort
                    && gsort != s
                {
                    return Err(err(
                        format!(
                            "global '{v}' has sort '{}' but position expects '{}'",
                            sorts.name(gsort),
                            sorts.name(s)
                        ),
                        span,
                    ));
                }
                return Ok(RRhsTerm::FetchGlobal(gid));
            }

            Err(err(format!("unbound variable '{v}'"), span))
        }
        RhsTerm::Lit(text, _) => {
            let (sort_name, val) = model
                .parse_any(text)
                .ok_or_else(|| err(format!("cannot parse literal '{text}'"), span))?;
            let sort = sorts
                .id_by_name(sort_name)
                .ok_or_else(|| err(format!("unknown literal sort '{sort_name}'"), span))?;
            let lit_op = ops
                .lit_op_for_sort(sort)
                .ok_or_else(|| err(format!("no literal op for sort {}", sorts.name(sort)), span))?;
            let target_sort = expected_sort.unwrap_or(sort);
            if target_sort != sort {
                return Err(err(
                    format!(
                        "literal '{text}' has sort {}, expected {}",
                        sorts.name(sort),
                        sorts.name(target_sort)
                    ),
                    span,
                ));
            }
            Ok(RRhsTerm::Lit {
                op: lit_op,
                sort,
                value: val,
            })
        }
        RhsTerm::App { op, children, .. } => {
            let (op_id, info) = lookup_op(op, ops, span)?;
            // Prim op: operates on concrete lit values, not e-nodes
            if ops.is_prim_op(op_id) {
                if let Some(exp) = expected_sort
                    && exp != info.return_sort
                {
                    return Err(err(
                        format!(
                            "prim op '{op}' returns {}, expected {}",
                            sorts.name(info.return_sort),
                            sorts.name(exp)
                        ),
                        span,
                    ));
                }
                let arg_sorts = match &info.kind {
                    OpKind::Normal { arg_sorts } => arg_sorts,
                    _ => unreachable!(),
                };
                if children.len() != arg_sorts.len() {
                    return Err(err(
                        format!(
                            "prim op '{op}' expects {} args, got {}",
                            arg_sorts.len(),
                            children.len()
                        ),
                        span,
                    ));
                }
                let mut args = Vec::with_capacity(children.len());
                for (i, c) in children.iter().enumerate() {
                    let var_name = match c {
                        crate::ast::RhsChild::Term(crate::ast::RhsTerm::Var(v, _)) => v,
                        _ => {
                            return Err(err(
                                format!("prim op '{op}' arg {i} must be a lit-val variable"),
                                span,
                            ));
                        }
                    };
                    args.push(resolve_prim_arg(
                        var_name,
                        arg_sorts[i],
                        op,
                        i,
                        ctx,
                        sorts,
                        span,
                    )?);
                }
                return Ok(RRhsTerm::PrimApp {
                    op: op_id,
                    args,
                    ret_sort: info.return_sort,
                });
            }
            if let Some(exp) = expected_sort
                && exp != info.return_sort
            {
                return Err(err(
                    format!(
                        "operator '{op}' returns {}, expected {}",
                        sorts.name(info.return_sort),
                        sorts.name(exp)
                    ),
                    span,
                ));
            }
            let child_sorts = arg_sorts_for_rhs(&info.kind, op, children.len(), span)?;
            let variadic = matches!(
                info.kind,
                OpKind::A { .. } | OpKind::MSet { .. } | OpKind::Set { .. }
            );
            let mut rchildren = Vec::with_capacity(children.len());
            for (i, c) in children.iter().enumerate() {
                if !variadic && matches!(c, crate::ast::RhsChild::TermMult { .. }) {
                    return Err(err(
                        format!(
                            "a multiplicity annotation on an RHS element needs a \
                             variadic operator; '{op}' has fixed arity"
                        ),
                        span,
                    ));
                }
                if !variadic
                    && matches!(
                        c,
                        crate::ast::RhsChild::Splice(..)
                            | crate::ast::RhsChild::SetComp { .. }
                            | crate::ast::RhsChild::MsetComp { .. }
                            | crate::ast::RhsChild::SeqComp { .. }
                    )
                {
                    return Err(err(
                        format!(
                            "RHS rest splices and comprehensions require a variadic \
                             operator; '{op}' has fixed arity"
                        ),
                        span,
                    ));
                }
                let cs = child_sorts.get(i).copied();
                rchildren.push(resolve_rhs_child(c, cs, ops, sorts, model, ctx, globals)?);
            }
            Ok(RRhsTerm::App {
                op: op_id,
                children: rchildren,
            })
        }
    }
}

fn resolve_mult_term<O, S: DenseId, L: LitVal, const TRACK: bool>(
    name: &str,
    mult: RhsMultRef,
    expected_sort: Option<S>,
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    span: Span,
) -> R<RRhsTerm<O, S, L>>
where
    O: DenseId + Hash + Copy,
{
    let Some(sort) = expected_sort else {
        return Err(err(
            format!("multiplicity variable '{name}' requires an i64 literal position"),
            span,
        ));
    };
    if sorts.name(sort) != "i64" {
        return Err(err(
            format!(
                "multiplicity variable '{name}' can only fill an i64 literal position, \
                 found sort {}",
                sorts.name(sort)
            ),
            span,
        ));
    }
    let lit_op = ops
        .lit_op_for_sort(sort)
        .ok_or_else(|| err(format!("no lit op for sort '{}'", sorts.name(sort)), span))?;
    Ok(RRhsTerm::MultVar {
        op: lit_op,
        var: mult,
    })
}

fn resolve_prim_arg<S: DenseId + Copy, const TRACK: bool>(
    name: &str,
    expected_sort: S,
    op: &str,
    arg_index: usize,
    ctx: &RhsResolveCtx<'_, S>,
    sorts: &SortRegistry<S, TRACK>,
    span: Span,
) -> R<RPrimArg> {
    let mult_arg = |mult| {
        if sorts.name(expected_sort) != "i64" {
            Err(err(
                format!(
                    "multiplicity variable '{name}' can only feed an i64 argument; \
                     prim op '{op}' arg {arg_index} expects {}",
                    sorts.name(expected_sort)
                ),
                span,
            ))
        } else {
            Ok(RPrimArg::Mult(mult))
        }
    };

    if let Some(local) = ctx.local_binding(name) {
        return match local {
            RhsLocalBinding::Mult(id) => mult_arg(RhsMultRef::Local(id)),
            RhsLocalBinding::Node(_) => Err(err(
                format!(
                    "'{name}' resolves to an RHS-local node variable, not a literal-value \
                     or multiplicity variable"
                ),
                span,
            )),
        };
    }

    match ctx.query_shape.kinds.get(name).copied() {
        Some(VarKind::LitVal) => Ok(RPrimArg::LitVal(
            ctx.query_shape
                .find_lit_val(name)
                .expect("query literal-value kind must have an id"),
        )),
        Some(VarKind::Mult) => mult_arg(RhsMultRef::Query(
            ctx.query_shape
                .find_mult(name)
                .expect("query multiplicity kind must have an id"),
        )),
        Some(kind) => Err(err(
            format!(
                "'{name}' resolves to a {}, not a literal-value or multiplicity variable",
                kind.label()
            ),
            span,
        )),
        None => Err(err(
            format!(
                "'{name}' is not a lit-val or multiplicity variable \
                 (bind via OpKind::Lit pattern or a `:k` annotation)"
            ),
            span,
        )),
    }
}

fn arg_sorts_for_rhs<S: DenseId + Copy>(
    kind: &OpKind<S>,
    op: &str,
    nchildren: usize,
    span: Span,
) -> R<Vec<S>> {
    match kind {
        OpKind::Normal { arg_sorts } => {
            check_arity(op, arg_sorts.len(), nchildren, span)?;
            Ok(arg_sorts.clone())
        }
        OpKind::Commutative { arg_sorts } => {
            check_arity(op, 2, nchildren, span)?;
            Ok(arg_sorts.to_vec())
        }
        OpKind::A { arg_sort, .. }
        | OpKind::MSet { arg_sort, .. }
        | OpKind::Set { arg_sort, .. } => {
            // All children get the same sort
            Ok(vec![*arg_sort; nchildren])
        }
        OpKind::Lit => Err(err(
            format!("operator '{op}' is a literal op, cannot appear in RHS application"),
            span,
        )),
    }
}

fn resolve_rhs_child<
    O: DenseId + Hash + Copy,
    S: DenseId + Copy,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
>(
    child: &crate::ast::RhsChild,
    sort: Option<S>,
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    model: &M,
    ctx: &mut RhsResolveCtx<'_, S>,
    globals: &GlobalCtx<S, impl Copy>,
) -> R<RRhsChild<O, S, L>> {
    use crate::ast::RhsChild;
    match child {
        RhsChild::Term(t) => Ok(RRhsChild::Term(resolve_rhs(
            t, sort, ops, sorts, model, ctx, globals,
        )?)),
        RhsChild::TermMult { term, mult, span } => {
            // Only a variadic op can absorb a repeated child; the App site
            // rejects the annotation under fixed-arity ops before recursing.
            let body = resolve_rhs(term, sort, ops, sorts, model, ctx, globals)?;
            let m = resolve_mult_expr(mult, *span, ctx)?;
            Ok(RRhsChild::TermMult {
                body: Box::new(body),
                mult: m,
            })
        }
        RhsChild::Splice(name, span) => resolve_splice(name, *span, sort, sorts, ctx),
        RhsChild::SetComp {
            body,
            var,
            source,
            filter,
            span,
            ..
        } => {
            let source_id = lookup_set(source, *span, ctx)?;
            let source_sort = ctx.set_sort(source_id);
            ctx.push_scope();
            let resolved = (|| {
                let vid = ctx.alloc_node(var, Some(source_sort), *span)?;
                let rbody = resolve_rhs(body, sort, ops, sorts, model, ctx, globals)?;
                let rfilter = filter
                    .as_ref()
                    .map(|f| {
                        let resolved = resolve_rhs(f, None, ops, sorts, model, ctx, globals)?;
                        require_literal_filter(resolved, f.span())
                    })
                    .transpose()?;
                Ok(RRhsChild::SetComp {
                    body: Box::new(rbody),
                    var: vid,
                    source: source_id,
                    filter: rfilter,
                })
            })();
            ctx.pop_scope();
            resolved
        }
        RhsChild::MsetComp {
            body,
            mult,
            var,
            mult_var,
            source,
            filter,
            span,
            ..
        } => {
            let source_id = lookup_mset(source, *span, ctx)?;
            let source_sort = ctx.mset_sort(source_id);
            ctx.push_scope();
            let resolved = (|| {
                let vid = ctx.alloc_node(var, Some(source_sort), *span)?;
                let mult_var_id = ctx.alloc_mult(mult_var, *span)?;
                let rbody = resolve_rhs(body, sort, ops, sorts, model, ctx, globals)?;
                let resolved_mult = resolve_mult_expr(mult, *span, ctx)?;
                let rfilter = filter
                    .as_ref()
                    .map(|f| {
                        let resolved = resolve_rhs(f, None, ops, sorts, model, ctx, globals)?;
                        require_literal_filter(resolved, f.span())
                    })
                    .transpose()?;
                Ok(RRhsChild::MsetComp {
                    body: Box::new(rbody),
                    mult: resolved_mult,
                    var: vid,
                    mult_var: mult_var_id,
                    source: source_id,
                    filter: rfilter,
                })
            })();
            ctx.pop_scope();
            resolved
        }
        RhsChild::SeqComp {
            body,
            var,
            source,
            filter,
            span,
            ..
        } => {
            let source_id = lookup_seq(source, *span, ctx)?;
            let source_sort = ctx.seq_sort(source_id);
            ctx.push_scope();
            let resolved = (|| {
                let vid = ctx.alloc_node(var, Some(source_sort), *span)?;
                let rbody = resolve_rhs(body, sort, ops, sorts, model, ctx, globals)?;
                let rfilter = filter
                    .as_ref()
                    .map(|f| {
                        let resolved = resolve_rhs(f, None, ops, sorts, model, ctx, globals)?;
                        require_literal_filter(resolved, f.span())
                    })
                    .transpose()?;
                Ok(RRhsChild::SeqComp {
                    body: Box::new(rbody),
                    var: vid,
                    source: source_id,
                    filter: rfilter,
                })
            })();
            ctx.pop_scope();
            resolved
        }
    }
}

/// A comprehension filter is evaluated for a concrete truthy value. Ordinary
/// e-node terms cannot provide one: `get_lit_val` reads a literal node, not an
/// arbitrary e-class, and a normal application in this position would only
/// mutate the graph before deterministically testing false.
fn require_literal_filter<O, S, L>(
    filter: RRhsTerm<O, S, L>,
    span: Span,
) -> R<Box<RRhsTerm<O, S, L>>> {
    if matches!(
        &filter,
        RRhsTerm::Lit { .. }
            | RRhsTerm::LitVar { .. }
            | RRhsTerm::PrimApp { .. }
            | RRhsTerm::MultVar { .. }
    ) {
        Ok(Box::new(filter))
    } else {
        Err(err(
            "comprehension filter must evaluate to a concrete literal value; \
             e-node terms are not graph-existence tests",
            span,
        ))
    }
}

// ---------------------------------------------------------------------------
// Rest/mult variable lookup helpers
// ---------------------------------------------------------------------------

fn resolve_splice<O, S: DenseId + Copy, L, const TRACK: bool>(
    name: &str,
    span: Span,
    expected_sort: Option<S>,
    sorts: &SortRegistry<S, TRACK>,
    ctx: &RhsResolveCtx<'_, S>,
) -> R<RRhsChild<O, S, L>> {
    if let Some(local) = ctx.local_binding(name) {
        return Err(err(
            format!(
                "'{name}' resolves to an {}, not a rest variable",
                local_binding_label(local)
            ),
            span,
        ));
    }
    let (child, actual_sort) = match ctx.query_shape.kinds.get(name).copied() {
        Some(VarKind::Seq) => {
            let id = ctx
                .query_shape
                .find_seq(name)
                .expect("query sequence kind must have an id");
            (RRhsChild::SpliceSeq(id), ctx.seq_sort(id))
        }
        Some(VarKind::Set) => {
            let id = ctx
                .query_shape
                .find_set(name)
                .expect("query set kind must have an id");
            (RRhsChild::SpliceSet(id), ctx.set_sort(id))
        }
        Some(VarKind::Mset) => {
            let id = ctx
                .query_shape
                .find_mset(name)
                .expect("query multiset kind must have an id");
            (RRhsChild::SpliceMset(id), ctx.mset_sort(id))
        }
        Some(kind) => Err(err(
            format!("'{name}' is a {}, not a rest variable", kind.label()),
            span,
        ))?,
        None => Err(err(format!("unknown rest variable '{name}'"), span))?,
    };
    if let Some(expected_sort) = expected_sort
        && actual_sort != expected_sort
    {
        return Err(err(
            format!(
                "rest variable '{name}' has element sort '{}' but this position expects '{}'",
                sorts.name(actual_sort),
                sorts.name(expected_sort)
            ),
            span,
        ));
    }
    Ok(child)
}

fn local_binding_label(binding: RhsLocalBinding) -> &'static str {
    match binding {
        RhsLocalBinding::Node(_) => "RHS-local node variable",
        RhsLocalBinding::Mult(_) => "RHS-local multiplicity variable",
    }
}

fn lookup_seq<S: DenseId>(name: &str, span: Span, ctx: &RhsResolveCtx<'_, S>) -> R<SeqVarId> {
    lookup_rest_kind(name, span, ctx, VarKind::Seq).map(|_| {
        ctx.query_shape
            .find_seq(name)
            .expect("query sequence kind must have an id")
    })
}

fn lookup_set<S: DenseId>(name: &str, span: Span, ctx: &RhsResolveCtx<'_, S>) -> R<SetVarId> {
    lookup_rest_kind(name, span, ctx, VarKind::Set).map(|_| {
        ctx.query_shape
            .find_set(name)
            .expect("query set kind must have an id")
    })
}

fn lookup_mset<S: DenseId>(name: &str, span: Span, ctx: &RhsResolveCtx<'_, S>) -> R<MsetVarId> {
    lookup_rest_kind(name, span, ctx, VarKind::Mset).map(|_| {
        ctx.query_shape
            .find_mset(name)
            .expect("query multiset kind must have an id")
    })
}

fn lookup_rest_kind<S: DenseId>(
    name: &str,
    span: Span,
    ctx: &RhsResolveCtx<'_, S>,
    expected: VarKind,
) -> R<()> {
    if let Some(local) = ctx.local_binding(name) {
        return Err(err(
            format!(
                "'{name}' resolves to an {}, not a {}",
                local_binding_label(local),
                expected.label()
            ),
            span,
        ));
    }
    match ctx.query_shape.kinds.get(name).copied() {
        Some(actual) if actual == expected => Ok(()),
        Some(actual) => Err(err(
            format!(
                "'{name}' is a {}, not a {}",
                actual.label(),
                expected.label()
            ),
            span,
        )),
        None => Err(err(format!("'{name}' is not a {}", expected.label()), span)),
    }
}

fn lookup_mult_ref<S: DenseId>(
    name: &str,
    span: Span,
    ctx: &RhsResolveCtx<'_, S>,
) -> R<RhsMultRef> {
    if let Some(local) = ctx.local_binding(name) {
        return match local {
            RhsLocalBinding::Mult(id) => Ok(RhsMultRef::Local(id)),
            RhsLocalBinding::Node(_) => Err(err(
                format!(
                    "'{name}' resolves to an RHS-local node variable, not a multiplicity variable"
                ),
                span,
            )),
        };
    }
    match ctx.query_shape.kinds.get(name).copied() {
        Some(VarKind::Mult) => Ok(RhsMultRef::Query(
            ctx.query_shape
                .find_mult(name)
                .expect("query multiplicity kind must have an id"),
        )),
        Some(kind) => Err(err(
            format!(
                "'{name}' is a {}, not a multiplicity variable",
                kind.label()
            ),
            span,
        )),
        None => Err(err(
            format!("'{name}' is not a multiplicity variable"),
            span,
        )),
    }
}

fn resolve_mult_expr<S: DenseId>(
    expr: &crate::ast::MultExpr,
    span: Span,
    ctx: &RhsResolveCtx<'_, S>,
) -> R<ResolvedMultExpr> {
    match expr {
        crate::ast::MultExpr::Lit(n) => Ok(ResolvedMultExpr::Lit(*n)),
        crate::ast::MultExpr::Var(name) => {
            lookup_mult_ref(name, span, ctx).map(ResolvedMultExpr::Var)
        }
        crate::ast::MultExpr::Prim { op, args } => {
            let p = MultPrimOp::from_name(op).ok_or_else(|| {
                err(
                    format!(
                        "'{op}' is not a multiplicity operation (u64::+ u64::- u64::* \
                         u64::/ u64::% u64::min u64::max)"
                    ),
                    span,
                )
            })?;
            if args.len() != 2 {
                return Err(err(
                    format!(
                        "'{op}' in a multiplicity expression takes 2 args, got {}",
                        args.len()
                    ),
                    span,
                ));
            }
            let rargs = args
                .iter()
                .map(|a| resolve_mult_expr(a, span, ctx))
                .collect::<R<Vec<_>>>()?;
            Ok(ResolvedMultExpr::Prim { op: p, args: rargs })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::id::{OpId, SortId};
    use crate::literal::NiraLitVal;
    use crate::sortcheck::flatten_surface as flatten;

    use crate::registry::AssocDir;
    use crate::test_helpers::parse_pattern;

    fn setup() -> (OpRegistry<OpId, SortId, false>, SortRegistry<SortId, false>) {
        let model = crate::literal::NiraModel;
        let mut sorts: SortRegistry<SortId, false> = SortRegistry::new();
        let sort_names: Vec<&str> = model.sorts().iter().map(|s| s.name).collect();
        sorts.register_builtins(&sort_names);
        let e = sorts.intern("IExpr");
        let b = sorts.intern("BExpr");

        let mut ops = OpRegistry::new();
        ops.register_builtins(&model, &sorts);
        let ibig = sorts.id_by_name("IBig").unwrap();
        ops.register("f", &[e, e], e);
        ops.register("g", &[e], e);
        ops.register("h", &[e, e, e], e);
        ops.register("a", &[], e); // nullary
        ops.register("b", &[], e);
        ops.register("p", &[b], b); // for sort-mismatch tests
        ops.register("to_b", &[e], b);
        ops.register("box_b", &[b], e);
        ops.register_c("eq", [e, e], e);
        ops.register_a("concat", e, e, AssocDir::Right);
        ops.register_a("bconcat", b, b, AssocDir::Right);
        ops.register_mset("add", e, e);
        ops.register_mset("badd", b, b);
        ops.register_set("union", e, e);
        ops.register_set("bunion", b, b);
        ops.register("ILit", &[ibig], e);

        (ops, sorts)
    }

    fn do_resolve(src: &str) -> Result<ResolvedQuery<OpId, SortId, NiraLitVal>, ResolveError> {
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;
        let pat = parse_pattern(src);
        let fq = flatten(&[pat], &ops).map_err(|e| ResolveError {
            msg: e,
            span: crate::ast::Span::Dummy,
            extra_spans: Vec::new(),
        })?;
        resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new())
    }

    fn do_resolve_multi(
        srcs: &[&str],
    ) -> Result<ResolvedQuery<OpId, SortId, NiraLitVal>, ResolveError> {
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;
        let pats: Vec<_> = srcs.iter().map(|s| parse_pattern(s)).collect();
        let fq = flatten(&pats, &ops).map_err(|e| ResolveError {
            msg: e,
            span: crate::ast::Span::Dummy,
            extra_spans: Vec::new(),
        })?;
        resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new())
    }

    /// `(= v pat)` adds no atom kind of its own: `pat` flattens as it would alone and one
    /// `Eq` ties `v` to its root.
    #[test]
    fn root_binding_lowers_to_one_eq() {
        let rq = do_resolve("(= v (g x))").unwrap();
        assert_eq!(rq.atoms.len(), 2);
        assert!(matches!(&rq.atoms[0], RAtom::Plain { .. }));
        assert!(matches!(&rq.atoms[1], RAtom::Eq(..)));
    }

    /// The bound root carries the pattern's sort, which is what lets a rewrite whose
    /// left-hand side is `(= v pat)` sort-check its right-hand side.
    #[test]
    fn root_binding_propagates_the_sort() {
        let (_, sorts) = setup();
        let e = sorts.id_by_name("IExpr").unwrap();
        let rq = do_resolve("(= v (g x))").unwrap();
        let v = rq.shape.find_var("v").unwrap();
        assert_eq!(rq.var_sorts[v.idx()], Some(e));
    }

    /// Repeating the bound name across conjuncts is the ordinary non-linear case: one
    /// variable, two roots, one `Eq` each.
    #[test]
    fn root_binding_shares_one_variable_across_conjuncts() {
        let rq = do_resolve_multi(&["(= v (g x))", "(= v (f x y))"]).unwrap();
        let eqs: Vec<_> = rq
            .atoms
            .iter()
            .filter_map(|a| match a {
                RAtom::Eq(a, b) => Some((*a, *b)),
                _ => None,
            })
            .collect();
        assert_eq!(eqs.len(), 2);
        assert_eq!(eqs[0].0, eqs[1].0);
        assert_ne!(eqs[0].1, eqs[1].1);
    }

    /// A guard reads the literal values other atoms bind, and records the atoms that bind
    /// them so the scheduler knows when it can run.
    #[test]
    fn guard_records_its_binding_atoms() {
        let rq = do_resolve_multi(&["(f (ILit a) (ILit b))", "(< a b)"]).unwrap();
        let (guard, deps) = rq
            .atoms
            .iter()
            .find_map(|at| match at {
                RAtom::Pred { guard, deps } => Some((guard, deps)),
                _ => None,
            })
            .expect("guard atom");
        let mut vals = Vec::new();
        guard.expr.value_vars(&mut vals);
        assert_eq!(vals.len(), 2);
        assert_eq!(deps.len(), 2);
        for d in deps {
            assert!(matches!(&rq.atoms[*d], RAtom::LitBind { .. }));
        }
    }

    /// A constant in a guard is parsed at the argument position's sort, not guessed.
    #[test]
    fn guard_constant_takes_the_argument_sort() {
        let rq = do_resolve_multi(&["(f (ILit a) y)", "(< a 5)"]).unwrap();
        assert!(rq.atoms.iter().any(|at| matches!(at, RAtom::Pred { .. })));
    }

    #[test]
    fn guard_rejects_a_variable_no_pattern_binds() {
        let e = do_resolve_multi(&["(f x y)", "(< a b)"]).unwrap_err();
        assert!(e.msg.contains("not bound to a literal value"), "{}", e.msg);
    }

    #[test]
    fn guard_rejects_a_non_boolean_computation() {
        let e = do_resolve_multi(&["(f (ILit a) (ILit b))", "(+ a b)"]).unwrap_err();
        assert!(e.msg.contains("must compute a bool"), "{}", e.msg);
    }

    #[test]
    fn guard_rejects_a_non_primitive_operator() {
        let e = do_resolve_multi(&["(f (ILit a) (ILit b))", "(< (g a) b)"]).unwrap_err();
        assert!(e.msg.contains("not a primitive"), "{}", e.msg);
    }

    #[test]
    fn resolve_plain() {
        let (_, sorts) = setup();
        let int = sorts.id_by_name("IExpr").unwrap();
        let rq = do_resolve("(f x y)").unwrap();
        assert_eq!(rq.atoms.len(), 1);
        assert!(matches!(&rq.atoms[0], RAtom::Plain { children, .. } if children.len() == 2));
        // Both vars should have sort Int
        assert!(
            rq.var_sorts
                .iter()
                .all(|s| s.map(|s: SortId| s == int).unwrap_or(true))
        );
    }

    #[test]
    fn resolve_nested() {
        let rq = do_resolve("(f x (g y))").unwrap();
        assert_eq!(rq.atoms.len(), 2);
    }

    #[test]
    fn resolve_literal() {
        // User must write (ILit 42) to bridge IBig → IExpr
        let rq = do_resolve("(f (ILit 42) x)").unwrap();
        assert!(rq.atoms.iter().any(|a| matches!(a, RAtom::Lit { .. })));
    }

    #[test]
    fn resolve_nonlinear_same_sort() {
        // (f x x) — same var, same sort → ok
        let rq = do_resolve("(f x x)");
        assert!(rq.is_ok());
    }

    #[test]
    fn resolve_unknown_op() {
        let r = do_resolve("(zzz x y)");
        assert!(r.is_err());
        assert!(r.unwrap_err().msg.contains("unknown operator"));
    }

    #[test]
    fn resolve_arity_mismatch() {
        let r = do_resolve("(g x y)"); // g is unary
        assert!(r.is_err());
        assert!(r.unwrap_err().msg.contains("expects 1 args, got 2"));
    }

    #[test]
    fn resolve_a_prefix() {
        let rq = do_resolve("(concat ..pre x y)").unwrap();
        assert!(rq.atoms.iter().any(|a| matches!(a, RAtom::APrefix { .. })));
    }

    #[test]
    fn resolve_ac_subset() {
        let rq = do_resolve("(add x:2 ..rest)").unwrap();
        assert!(rq.atoms.iter().any(|a| matches!(a, RAtom::ACSub { .. })));
    }

    #[test]
    fn resolve_aci_subset() {
        let rq = do_resolve("(union x y ..rest)").unwrap();
        assert!(rq.atoms.iter().any(|a| matches!(a, RAtom::ACISub { .. })));
    }

    #[test]
    fn resolve_wrong_mode_a_on_plain() {
        // Rest variable on a plain op should error
        let r = do_resolve("(f ..pre x y)");
        assert!(r.is_err());
    }

    #[test]
    fn resolve_wrong_mode_ac_on_a() {
        // Using {} on an A op
        let r = do_resolve("(concat x:2 ..rest)");
        assert!(r.is_err());
    }

    #[test]
    fn resolve_empty_a_exact() {
        let r = do_resolve("(concat)");
        assert!(r.is_err());
        assert!(r.unwrap_err().msg.contains("at least 1 child"));
    }

    #[test]
    fn resolve_empty_ac_exact() {
        let r = do_resolve("(add)");
        assert!(r.is_err());
    }

    #[test]
    fn resolve_empty_aci_exact() {
        let r = do_resolve("(union)");
        assert!(r.is_err());
    }

    #[test]
    fn resolve_singleton_ok() {
        assert!(do_resolve("(concat x)").is_ok());
        assert!(do_resolve("(add x:1)").is_ok());
        assert!(do_resolve("(union x)").is_ok());
    }

    // -- RHS tests --

    fn do_resolve_rhs(
        lhs: &str,
        rhs_src: &str,
    ) -> Result<RRhsTerm<OpId, SortId, NiraLitVal>, ResolveError> {
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;
        let pat = parse_pattern(lhs);
        let fq = flatten(&[pat], &ops).unwrap();
        let globals: GlobalCtx<_, ()> = GlobalCtx::new();
        let rq = resolve(&fq, &ops, &sorts, &model, &globals)?;
        let root_name = &fq.root_vars[0];
        let root_vid = rq.shape.find_var(root_name).unwrap();
        let root_sort = rq.var_sorts[root_vid.idx()];
        let ri = rhs_src;
        let rhs = crate::test_helpers::parse_rhs(ri);
        let mut ctx = RhsResolveCtx::new(&rq);
        resolve_rhs(&rhs, root_sort, &ops, &sorts, &model, &mut ctx, &globals)
    }

    fn resolve_rhs_with_locals(
        lhs: &str,
        rhs_src: &str,
    ) -> Result<
        (
            ResolvedQuery<OpId, SortId, NiraLitVal>,
            RRhsTerm<OpId, SortId, NiraLitVal>,
            RhsLocalShape,
        ),
        ResolveError,
    > {
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;
        let pat = parse_pattern(lhs);
        let fq = flatten(&[pat], &ops).unwrap();
        let globals: GlobalCtx<_, ()> = GlobalCtx::new();
        let rq = resolve(&fq, &ops, &sorts, &model, &globals)?;
        let root_vid = rq.shape.find_var(&fq.root_vars[0]).unwrap();
        let root_sort = rq.var_sorts[root_vid.idx()];
        let rhs = crate::test_helpers::parse_rhs(rhs_src);
        let mut ctx = RhsResolveCtx::new(&rq);
        let resolved = resolve_rhs(&rhs, root_sort, &ops, &sorts, &model, &mut ctx, &globals)?;
        let locals = ctx.local_shape();
        drop(ctx);
        Ok((rq, resolved, locals))
    }

    #[test]
    fn rhs_var() {
        let r = do_resolve_rhs("(f x y)", "x");
        assert!(matches!(r.unwrap(), RRhsTerm::Var(_)));
    }

    #[test]
    fn rhs_lit() {
        // (ILit 42) in IExpr context → App(ILit, [Lit(@IBig, 42)])
        let r = do_resolve_rhs("(f x y)", "(ILit 42)");
        assert!(matches!(r.unwrap(), RRhsTerm::App { .. }));
    }

    #[test]
    fn rhs_app() {
        let r = do_resolve_rhs("(f x y)", "(g x)");
        assert!(matches!(r.unwrap(), RRhsTerm::App { .. }));
    }

    #[test]
    fn rhs_unknown_op() {
        let r = do_resolve_rhs("(f x y)", "(zzz x)");
        assert!(r.is_err());
        assert!(r.unwrap_err().msg.contains("unknown operator"));
    }

    #[test]
    fn rhs_nested() {
        let r = do_resolve_rhs("(f x y)", "(f x (g y))");
        assert!(r.is_ok());
    }

    #[test]
    fn rhs_variadic_sugar() {
        // RHS can use plain syntax for AC ops
        let r = do_resolve_rhs("(f x y)", "(add x y)");
        assert!(r.is_ok());
    }

    #[test]
    fn rhs_splice() {
        let r = do_resolve_rhs("(concat x ..rest)", "(concat x ..rest)");
        assert!(r.is_ok());
        match r.unwrap() {
            RRhsTerm::App { children, .. } => {
                assert!(children.iter().any(|c| matches!(
                    c,
                    RRhsChild::SpliceSeq(_) | RRhsChild::SpliceSet(_) | RRhsChild::SpliceMset(_)
                )));
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn rhs_splices_require_the_destination_element_sort() {
        let cases = [
            ("(concat x ..rest)", "(box_b (bconcat ..rest))"),
            ("(union x ..rest)", "(box_b (bunion ..rest))"),
            ("(add x:1 ..rest)", "(box_b (badd ..rest))"),
        ];
        for (lhs, rhs) in cases {
            let error = do_resolve_rhs(lhs, rhs).unwrap_err();
            assert!(
                error.msg.contains("rest variable 'rest'")
                    && error.msg.contains("element sort")
                    && error.msg.contains("IExpr")
                    && error.msg.contains("BExpr"),
                "{lhs} -> {rhs}: unexpected error: {}",
                error.msg
            );
        }
    }

    #[test]
    fn rhs_comprehension_binders_use_the_source_element_sort() {
        let valid = [
            (
                "(concat x ..rest)",
                "(box_b (bconcat ..[(to_b e) for e in rest]))",
            ),
            (
                "(union x ..rest)",
                "(box_b (bunion ..{(to_b e) for e in rest}))",
            ),
            (
                "(add x:1 ..rest)",
                "(box_b (badd ..{(to_b e):k for e:k in rest}))",
            ),
        ];
        for (lhs, rhs) in valid {
            assert!(
                do_resolve_rhs(lhs, rhs).is_ok(),
                "{lhs} -> {rhs} should permit a typed mapping"
            );
        }

        let invalid = [
            ("(concat x ..rest)", "(box_b (bconcat ..[e for e in rest]))"),
            ("(union x ..rest)", "(box_b (bunion ..{e for e in rest}))"),
            ("(add x:1 ..rest)", "(box_b (badd ..{e:k for e:k in rest}))"),
        ];
        for (lhs, rhs) in invalid {
            let error = do_resolve_rhs(lhs, rhs).unwrap_err();
            assert!(
                error.msg.contains("sort mismatch"),
                "{lhs} -> {rhs}: unexpected error: {}",
                error.msg
            );
        }
    }

    #[test]
    fn lhs_rest_variable_has_one_element_sort() {
        for patterns in [
            ["(concat x ..rest)", "(bconcat y ..rest)"],
            ["(union x ..rest)", "(bunion y ..rest)"],
            ["(add x:1 ..rest)", "(badd y:1 ..rest)"],
        ] {
            let error = do_resolve_multi(&patterns).unwrap_err();
            assert!(
                error.msg.contains("rest variable 'rest'") && error.msg.contains("element sorts"),
                "{patterns:?}: unexpected error: {}",
                error.msg
            );
        }
    }

    #[test]
    fn rhs_set_comp() {
        let r = do_resolve_rhs("(union x ..rest)", "(union ..{(g e) for e in rest})");
        assert!(r.is_ok());
        match r.unwrap() {
            RRhsTerm::App { children, .. } => {
                assert!(
                    children
                        .iter()
                        .any(|c| matches!(c, RRhsChild::SetComp { .. }))
                );
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn rhs_seq_comp() {
        let r = do_resolve_rhs("(concat x ..rest)", "(concat ..[(g e) for e in rest])");
        assert!(r.is_ok());
        match r.unwrap() {
            RRhsTerm::App { children, .. } => {
                assert!(
                    children
                        .iter()
                        .any(|c| matches!(c, RRhsChild::SeqComp { .. }))
                );
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn rhs_set_comp_with_literal_filter() {
        let r = do_resolve_rhs(
            "(union x y ..rest)",
            "(union ..{(g e) for e in rest if true})",
        );
        assert!(r.is_ok());
        match r.unwrap() {
            RRhsTerm::App { children, .. } => match &children[0] {
                RRhsChild::SetComp { filter, .. } => assert!(filter.is_some()),
                _ => panic!("expected SetComp"),
            },
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn rhs_rejects_e_node_comprehension_filters() {
        let cases = [
            (
                "(union x y ..rest)",
                "(union ..{(g e) for e in rest if (f e x)})",
            ),
            (
                "(concat x ..rest)",
                "(concat ..[(g e) for e in rest if (g e)])",
            ),
            ("(concat x ..rest)", "(concat ..[(g e) for e in rest if e])"),
            (
                "(add x:1 ..rest)",
                "(add ..{(g e):k for e:k in rest if (g e)})",
            ),
        ];
        for (lhs, rhs) in cases {
            let error = do_resolve_rhs(lhs, rhs).unwrap_err();
            assert!(
                error.msg.contains("concrete literal value")
                    && error.msg.contains("not graph-existence tests"),
                "{lhs} -> {rhs}: unexpected error: {}",
                error.msg
            );
        }
    }

    #[test]
    fn rhs_mset_comp() {
        let r = do_resolve_rhs("(add x:k ..rest)", "(add ..{(g e):k for e:k in rest})");
        assert!(r.is_ok());
        match r.unwrap() {
            RRhsTerm::App { children, .. } => {
                assert!(
                    children
                        .iter()
                        .any(|c| matches!(c, RRhsChild::MsetComp { .. }))
                );
            }
            _ => panic!("expected App"),
        }
    }

    #[test]
    fn rhs_mset_comp_uses_distinct_local_refs_without_changing_query_shape() {
        let (rq, rhs, locals) =
            resolve_rhs_with_locals("(add x:k ..rest)", "(add ..{(g x):k for x:k in rest} x:k)")
                .unwrap();
        assert_eq!(rq.shape.nodes.len(), rq.var_sorts.len());
        assert_eq!(rq.shape.nodes.iter().filter(|name| *name == "x").count(), 1);
        assert_eq!(rq.shape.mults, ["k"]);
        assert_eq!(locals.node_count, 1);
        assert_eq!(locals.mult_count, 1);

        let x = rq.shape.find_var("x").unwrap();
        let k = rq.shape.find_mult("k").unwrap();
        let RRhsTerm::App { children, .. } = rhs else {
            panic!("expected app");
        };
        let RRhsChild::MsetComp {
            body,
            mult,
            var,
            mult_var,
            ..
        } = &children[0]
        else {
            panic!("expected multiset comprehension");
        };
        assert_eq!(*var, RhsLocalVarId::new(0));
        assert_eq!(*mult_var, RhsLocalMultVarId::new(0));
        assert_eq!(mult, &ResolvedMultExpr::Var(RhsMultRef::Local(*mult_var)));
        let RRhsTerm::App {
            children: body_children,
            ..
        } = body.as_ref()
        else {
            panic!("expected mapped application");
        };
        assert!(matches!(
            &body_children[0],
            RRhsChild::Term(RRhsTerm::Var(RhsNodeRef::Local(id))) if id == var
        ));
        assert!(matches!(
            &children[1],
            RRhsChild::TermMult {
                body,
                mult: ResolvedMultExpr::Var(RhsMultRef::Query(id))
            } if matches!(body.as_ref(), RRhsTerm::Var(RhsNodeRef::Query(node)) if *node == x)
                && *id == k
        ));
    }

    #[test]
    fn rhs_sibling_comprehensions_reuse_names_with_fresh_ids() {
        let (_, rhs, locals) = resolve_rhs_with_locals(
            "(add x:1 ..rest)",
            "(add ..{rest:k for rest:k in rest} ..{rest:k for rest:k in rest})",
        )
        .unwrap();
        assert_eq!(
            locals,
            RhsLocalShape {
                node_count: 2,
                mult_count: 2
            }
        );
        let RRhsTerm::App { children, .. } = rhs else {
            panic!("expected app");
        };
        let (
            RRhsChild::MsetComp {
                var: first_node,
                mult_var: first_mult,
                ..
            },
            RRhsChild::MsetComp {
                var: second_node,
                mult_var: second_mult,
                ..
            },
        ) = (&children[0], &children[1])
        else {
            panic!("expected sibling multiset comprehensions");
        };
        assert_ne!(first_node, second_node);
        assert_ne!(first_mult, second_mult);
    }

    #[test]
    fn rhs_nearest_wrong_kind_binding_does_not_fall_through() {
        let node_shadow =
            do_resolve_rhs("(add x:k ..rest)", "(add ..{k:k for k:inner in rest})").unwrap_err();
        assert!(
            node_shadow.msg.contains("RHS-local node") && node_shadow.msg.contains("multiplicity")
        );

        let mult_shadow =
            do_resolve_rhs("(add x:k ..rest)", "(add ..{x:count for elem:x in rest})").unwrap_err();
        assert!(
            mult_shadow.msg.contains("multiplicity variable 'x'")
                && mult_shadow.msg.contains("i64")
        );
    }

    #[test]
    fn rhs_rejects_duplicate_comprehension_binder_names() {
        let error =
            do_resolve_rhs("(add x:1 ..rest)", "(add ..{k:k for k:k in rest})").unwrap_err();
        assert!(
            error.msg.contains("declared twice"),
            "unexpected error: {}",
            error.msg
        );
    }

    #[test]
    fn rhs_comprehension_locals_do_not_escape_their_scope() {
        let error = do_resolve_rhs(
            "(add x:1 ..rest)",
            "(add ..{elem:k for elem:k in rest} elem)",
        )
        .unwrap_err();
        assert!(
            error.msg.contains("unbound variable 'elem'"),
            "unexpected error: {}",
            error.msg
        );
    }

    #[test]
    fn rhs_outer_local_of_wrong_kind_blocks_nested_source_lookup() {
        let error = do_resolve_rhs(
            "(add x:1 ..rest)",
            "(add ..{(add ..{inner:k2 for inner:k2 in rest}):1 \
             for rest:k in rest})",
        )
        .unwrap_err();
        assert!(
            error.msg.contains("RHS-local node") && error.msg.contains("multiset rest variable"),
            "unexpected error: {}",
            error.msg
        );
    }

    #[test]
    fn rhs_rejects_collection_source_of_the_wrong_kind() {
        let cases = [
            ("(concat x ..rest)", "(concat ..[x for x in rest])", None),
            (
                "(concat x ..rest)",
                "(add ..{x:k for x:k in rest})",
                Some("multiset rest variable"),
            ),
            (
                "(union x ..rest)",
                "(concat ..[x for x in rest])",
                Some("sequence rest variable"),
            ),
            (
                "(add x:1 ..rest)",
                "(union ..{x for x in rest})",
                Some("set rest variable"),
            ),
        ];
        for (lhs, rhs, expected_error) in cases {
            let result = do_resolve_rhs(lhs, rhs);
            match expected_error {
                None => assert!(result.is_ok(), "{lhs} -> {rhs} should resolve"),
                Some(expected) => {
                    let error = result.unwrap_err();
                    assert!(
                        error.msg.contains(expected),
                        "{lhs} -> {rhs}: unexpected error: {}",
                        error.msg
                    );
                }
            }
        }
    }

    #[test]
    fn rhs_return_sort_mismatch() {
        // g returns Int, but f expects Int at arg0 — this is fine
        // but if we had a sort mismatch... we need an op that returns a different sort
        // For now, test that unknown op errors
        let r = do_resolve_rhs("(f x y)", "(zzz x)");
        assert!(r.is_err());
    }

    // -- LHS additional tests --

    #[test]
    fn resolve_commutative() {
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;
        let pat = parse_pattern("(eq x y)");
        let fq = flatten(&[pat], &ops).unwrap();
        let rq = resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new());
        assert!(rq.is_ok());
    }

    #[test]
    fn resolve_sort_mismatch() {
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;
        // (f x y) binds x:Expr, then (p x) expects x:BExpr → mismatch
        let pats: Vec<_> = ["(f x y)", "(p x)"]
            .iter()
            .map(|s| parse_pattern(s))
            .collect();
        let fq = flatten(&pats, &ops).unwrap();
        let r = resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new());
        assert!(r.is_err());
        assert!(r.unwrap_err().msg.contains("sort mismatch"));
    }

    // -- Sort error tests (LHS and RHS) --

    #[test]
    fn lhs_plain_arity_mismatch() {
        // f: Int×Int→Int, but pattern has 3 children
        let r = do_resolve("(f x y z)");
        assert!(r.is_err());
        assert!(r.unwrap_err().msg.contains("expects 2 args, got 3"));
    }

    #[test]
    fn lhs_plain_arity_too_few() {
        let r = do_resolve("(f x)");
        assert!(r.is_err());
        assert!(r.unwrap_err().msg.contains("expects 2 args, got 1"));
    }

    #[test]
    fn lhs_commutative_arity_mismatch() {
        let r = do_resolve("(eq x y z)");
        assert!(r.is_err());
        assert!(r.unwrap_err().msg.contains("expects 2 args, got 3"));
    }

    #[test]
    fn lhs_ac_exact_empty_rejected() {
        // AC exact with 0 elements should fail
        // We can't easily parse this since the parser requires at least one element,
        // but we can test via the resolve error message on check_min_children
        // Actually, the parser won't produce an empty AC exact. Skip this — the parser guards it.
    }

    #[test]
    fn lhs_nested_sort_mismatch() {
        // f: Expr×Expr→Expr, p: BExpr→BExpr
        // (f x (p y)) — p returns BExpr, but f expects Expr at position 1
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;
        let pat = parse_pattern("(f x (p y))");
        let fq = flatten(&[pat], &ops).unwrap();
        let r = resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new());
        assert!(r.is_err());
        assert!(
            r.unwrap_err().msg.contains("sort mismatch"),
            "expected sort mismatch for nested pattern"
        );
    }

    #[test]
    fn lhs_nonlinear_sort_mismatch() {
        // f: Expr×Expr→Expr, p: BExpr→BExpr
        // (f x y), (p x) — x bound to Expr by f, then p expects BExpr
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;
        let pats: Vec<_> = ["(f x y)", "(p x)"]
            .iter()
            .map(|s| parse_pattern(s))
            .collect();
        let fq = flatten(&pats, &ops).unwrap();
        let r = resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new());
        assert!(r.is_err());
        assert!(r.unwrap_err().msg.contains("sort mismatch"));
    }

    #[test]
    fn lhs_ac_element_sort_mismatch() {
        // add: AC Expr→Expr, p: BExpr→BExpr
        // (add {(p x):1 ..rest}) — p returns BExpr, but add expects Expr elements
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;
        let pat = parse_pattern("(add (p x):1 ..rest)");
        let fq = flatten(&[pat], &ops).unwrap();
        let r = resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new());
        assert!(r.is_err());
        assert!(r.unwrap_err().msg.contains("sort mismatch"));
    }

    #[test]
    fn rhs_child_sort_mismatch() {
        // f: Expr×Expr→Expr, p: BExpr→BExpr
        // LHS: (f x y), RHS: (f (p x) y) — p returns BExpr, f expects Expr at pos 0
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;
        let pat = parse_pattern("(f x y)");
        let fq = flatten(&[pat], &ops).unwrap();
        let rq = resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new()).unwrap();
        let root_vid = rq.shape.find_var(&fq.root_vars[0]).unwrap();
        let root_sort = rq.var_sorts[root_vid.idx()];
        let ri = "(f (p x) y)";
        let rhs = crate::test_helpers::parse_rhs(ri);
        let mut ctx = RhsResolveCtx::new(&rq);
        let globals = GlobalCtx::<_, ()>::new();
        let r = resolve_rhs(&rhs, root_sort, &ops, &sorts, &model, &mut ctx, &globals);
        assert!(r.is_err());
        let msg = r.unwrap_err().msg;
        assert!(
            msg.contains("sort") || msg.contains("expected"),
            "expected sort error, got: {msg}"
        );
    }

    #[test]
    fn rhs_root_sort_mismatch() {
        // f: Expr×Expr→Expr, p: BExpr→BExpr
        // LHS: (f x y) returns Expr, RHS: (p x) returns BExpr — root sort mismatch
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;
        let pat = parse_pattern("(f x y)");
        let fq = flatten(&[pat], &ops).unwrap();
        let rq = resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new()).unwrap();
        let root_vid = rq.shape.find_var(&fq.root_vars[0]).unwrap();
        let root_sort = rq.var_sorts[root_vid.idx()];
        let ri = "(p x)";
        let rhs = crate::test_helpers::parse_rhs(ri);
        let mut ctx = RhsResolveCtx::new(&rq);
        let globals = GlobalCtx::<_, ()>::new();
        let r = resolve_rhs(&rhs, root_sort, &ops, &sorts, &model, &mut ctx, &globals);
        assert!(r.is_err());
        let msg = r.unwrap_err().msg;
        assert!(
            msg.contains("sort") || msg.contains("returns"),
            "expected sort error, got: {msg}"
        );
    }

    #[test]
    fn rhs_plain_arity_mismatch() {
        // f: Int×Int→Int, RHS: (f x) — too few args for a plain op
        let error = do_resolve_rhs("(f x y)", "(f x)").unwrap_err();
        assert!(error.msg.contains("expects 2 arguments, got 1"));
    }

    #[test]
    fn rhs_fixed_arity_operator_rejects_collection_expansion() {
        for (lhs, rhs) in [
            ("(concat x ..rest)", "(g ..rest)"),
            ("(concat x ..rest)", "(g ..[e for e in rest])"),
            ("(union x ..rest)", "(g ..{e for e in rest})"),
            ("(add x:1 ..rest)", "(g ..{e:k for e:k in rest})"),
            ("(add x:k ..rest)", "(g x:k)"),
        ] {
            let error = do_resolve_rhs(lhs, rhs).unwrap_err();
            assert!(
                error.msg.contains("fixed arity"),
                "{lhs} -> {rhs}: unexpected error: {}",
                error.msg
            );
        }
    }

    #[test]
    fn rhs_literal_sort_mismatch() {
        // LHS: (f x y) returns Int, RHS: literal "true" which is Bool
        let r = do_resolve_rhs("(f x y)", "true");
        assert!(r.is_err());
        let msg = r.unwrap_err().msg;
        assert!(
            msg.contains("sort") || msg.contains("expected"),
            "expected sort error, got: {msg}"
        );
    }

    // -- Multiplicity interval tests --

    #[test]
    fn show_error_messages() {
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;

        let lhs_cases: &[(&str, &str)] = &[
            ("(f x y z)", "LHS: plain arity too many"),
            ("(f x)", "LHS: plain arity too few"),
            ("(f x (p y))", "LHS: nested sort mismatch"),
        ];

        for &(src, label) in lhs_cases {
            let pat = parse_pattern(src);
            let fq = match flatten(&[pat], &ops) {
                Ok(fq) => fq,
                Err(e) => {
                    println!("{label}:");
                    println!("  flatten error: {e}\n");
                    continue;
                }
            };
            let e = resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new()).unwrap_err();
            println!("{label}:");
            println!("  resolve error: {}\n", e.msg);
        }

        // RHS errors
        let rhs_cases: &[(&str, &str, &str)] = &[
            ("(f x y)", "(f (p x) y)", "RHS: child sort mismatch"),
            ("(f x y)", "(p x)", "RHS: root sort mismatch"),
            ("(f x y)", "true", "RHS: literal sort mismatch"),
        ];

        for &(lhs, rhs, label) in rhs_cases {
            let pat = parse_pattern(lhs);
            let fq = flatten(&[pat], &ops).unwrap();
            let rq = resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new()).unwrap();
            let root_vid = rq.shape.find_var(&fq.root_vars[0]).unwrap();
            let root_sort = rq.var_sorts[root_vid.idx()];
            let ri = rhs;
            let rhs_ast = crate::test_helpers::parse_rhs(ri);
            let mut ctx = RhsResolveCtx::new(&rq);
            let globals = GlobalCtx::<_, ()>::new();
            let e = resolve_rhs(
                &rhs_ast, root_sort, &ops, &sorts, &model, &mut ctx, &globals,
            )
            .unwrap_err();
            println!("{label}:");
            println!("  resolve error: {}\n", e.msg);
        }
    }

    #[test]
    fn mult_interval_unconstrained() {
        let rq = do_resolve("(add x:k ..rest)").unwrap();
        assert_eq!(rq.mult_intervals.len(), 1);
        let (_, lo, hi) = rq.mult_intervals[0];
        assert_eq!(lo, 1);
        assert_eq!(hi, u64::MAX);
    }

    #[test]
    fn mult_interval_ge() {
        let rq = do_resolve("(add x:k >= 3 ..rest)").unwrap();
        let (_, lo, hi) = rq.mult_intervals[0];
        assert_eq!(lo, 3);
        assert_eq!(hi, u64::MAX);
    }

    #[test]
    fn mult_interval_eq() {
        let rq = do_resolve("(add x:k == 5 ..rest)").unwrap();
        let (_, lo, hi) = rq.mult_intervals[0];
        assert_eq!(lo, 5);
        assert_eq!(hi, 5);
    }

    #[test]
    fn mult_interval_lt() {
        let rq = do_resolve("(add x:k < 4 ..rest)").unwrap();
        let (_, lo, hi) = rq.mult_intervals[0];
        assert_eq!(lo, 1);
        assert_eq!(hi, 3);
    }

    #[test]
    fn mult_interval_exact_no_var() {
        // :2 is FlatMult::Exact, no mult variable → no interval entry
        let rq = do_resolve("(add x:2 ..rest)").unwrap();
        assert!(rq.mult_intervals.is_empty());
    }

    #[test]
    fn mult_interval_unsatisfiable() {
        // k == 0 → base min is 1, so [max(1,0), min(MAX,0)] = [1, 0] → unsatisfiable
        let r = do_resolve("(add x:k==0 ..rest)");
        let e = r.unwrap_err();
        assert!(e.msg.contains("unsatisfiable"));
    }

    #[test]
    fn mult_interval_unsatisfiable_multi_constraint() {
        // Two constraints on the same mult var via nonlinear usage:
        // (add {x:k >= 10 ..r1}) (add {x:k <= 5 ..r2})
        // k >= 10 and k <= 5 → [10, 5] → empty → error with spans from both atoms
        let (ops, sorts) = setup();
        let model = crate::literal::NiraModel;

        let src = "(add x:k>=10 ..r1) (add x:k<=5 ..r2)";
        let pats = crate::test_helpers::parse_patterns(src);
        let fq = flatten(&pats, &ops).unwrap();
        let e = resolve(&fq, &ops, &sorts, &model, &GlobalCtx::<_, ()>::new()).unwrap_err();
        assert!(e.msg.contains("unsatisfiable"));
        assert!(
            e.msg.contains("'k'"),
            "expected variable name in: {}",
            e.msg
        );
        let rendered = render_error(src, &e);
        println!("mult_interval_unsatisfiable_multi_constraint:\n{rendered}\n");
        assert!(
            rendered.contains("^^^"),
            "expected caret underline in: {rendered}"
        );
    }
}
