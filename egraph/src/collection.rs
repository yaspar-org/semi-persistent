// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Sequence rules' checker, types, and reference matcher.
//!
//! This module checks a sequence rule (`check`: allowed roots, filters at the root
//! only, the `:except` relation acyclic, at most one bare sequence under AC or ACI)
//! and holds the rule's types ([`Rule`], [`PassReport`]). Its [`pass`] is the first
//! matcher for these rules, a pass over every node of each rule's root operator on the
//! live graph. No command reaches it any more: sequence rules are matched by the
//! `Collect` step of the relational engine (`crate::seq_engine`, design §7.6),
//! in each round on the round's snapshot, and [`pass`] is the reference
//! `tests/seq_differential.rs` checks that engine against. Both assemble through
//! `crate::seq_collect` and evaluate right-hand sides through `crate::seq_rhs`.
//!
//! The first design of these rules (`(each name pattern)`, smallest-id member choice,
//! one maximal match per node, ACI roots only, a pass after each round) is recorded,
//! with what replaced each decision, in design §7.6, "Collection rules (superseded)".

use crate::ast::GlobalVarId;
use crate::ast::Span;
use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::lit_model::LitModel;
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;
use crate::registry::OpKind;
use crate::resolve::GlobalCtx;
use crate::seq_collect::{MultCheck, Slots, Value, dedup_slots, mult_column, value_eq};
use crate::surface_ast::{SurfacePatChild, SurfacePattern};
use std::collections::BTreeMap;

// ── Surface ──────────────────────────────────────────────────────────────────

/// `(rewrite LHS RHS [:let (...)] [:when (...)] [:ruleset r])` with a collection in `LHS`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SurfaceRule {
    pub lhs: SurfacePattern,
    /// The right-hand side, `:let`, and `:when` in `collection.rs`'s own expression
    /// language, where they parse in it: debug builds evaluate them too, to check
    /// `crate::seq_rhs`.
    pub legacy: Option<LegacyRhs>,
    /// The right-hand side, `:let`, and `:when` in the ordinary right-hand-side
    /// language, which `crate::seq_rhs` resolves and evaluates.
    pub rhs_term: crate::ast::RhsTerm,
    pub lets_term: Vec<(String, crate::ast::RhsTerm)>,
    pub when_term: Vec<crate::ast::RhsTerm>,
    pub ruleset: Option<String>,
    /// `:flatten`: the pattern matches its operator on the flattened form.
    pub flatten: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LegacyRhs {
    pub rhs: CExpr,
    pub lets: Vec<(String, CExpr)>,
    pub when: Vec<CExpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CExpr {
    Var(String, Span),
    Lit(String, Span),
    App {
        op: String,
        children: Vec<CChild>,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CChild {
    Expr(CExpr),
    /// `..name`: the classes of a collection or of the rest.
    Splice(String, Span),
    /// `..{body for (x y ...) in source}`.
    Comp {
        body: CExpr,
        vars: Vec<String>,
        source: CExpr,
        span: Span,
    },
}

impl CExpr {
    fn span(&self) -> Span {
        match self {
            CExpr::Var(_, s) | CExpr::Lit(_, s) | CExpr::App { span: s, .. } => *s,
        }
    }
}

/// Whether a pattern has a sequence-pattern child anywhere: a bare `..name` between
/// children or a filtered `(..name base)` (`doc/sequence-patterns.md`).
pub fn has_sequence(p: &SurfacePattern) -> bool {
    match p {
        SurfacePattern::App { children, .. } => children.iter().any(|c| match c {
            SurfacePatChild::Elem(p) | SurfacePatChild::ElemMult(p, _) => has_sequence(p),
            SurfacePatChild::Seq(..) | SurfacePatChild::Filter { .. } => true,
        }),
        _ => false,
    }
}

// ── Checked ──────────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
enum Pat<O, L> {
    /// A variable slot, bound to a class or, under a literal sort, to its value.
    Var {
        slot: usize,
        literal: bool,
    },
    /// A global `let` name: the class it is bound to.
    Global(GlobalVarId),
    /// A literal of the argument's literal sort, read through the model.
    Lit(L),
    App(O, Vec<Pat<O, L>>),
}

/// `(..name[:mult] base [:except other])`.
#[derive(Clone, Debug)]
struct Filter<O, L> {
    name: String,
    pat: Pat<O, L>,
    /// Variable names by slot, local to one element.
    vars: Vec<String>,
    /// The index, among the rule's filters, of the filter named by `:except`.
    except: Option<usize>,
    /// The multiplicity annotation, AC only.
    mult: Option<MultCheck>,
    /// Sort names of `vars`, by slot.
    sorts: Vec<String>,
}

/// One child item of the root node.
#[derive(Clone, Debug)]
enum RItem<O, L> {
    /// A simple pattern: one child. Its variables share the rule's scalar slots.
    /// Under AC, an unannotated item takes a child of multiplicity 1 and an
    /// annotated one a child its annotation accepts (maximum partition).
    One(Pat<O, L>, Option<MultCheck>),
    /// `..name`: a bare sequence.
    Bare(String),
    /// `(..name base)`: an index into `Rule::filters`.
    Filter(usize),
}

/// A checked sequence rule.
#[derive(Clone, Debug)]
pub struct Rule<O, S, L> {
    pub name: String,
    /// The id the interpreter registers the rule under when it is installed; the
    /// justification of every union the rule makes in proof mode.
    pub rule_id: Option<crate::id::RuleId>,
    pub ruleset: Option<crate::apply::RulesetId>,
    root: O,
    /// The root is associative (`:assoc` or a fold): items are matched in order.
    assoc: bool,
    /// The root is AC with multiplicities: sequences carry multiplicity columns.
    ac: bool,
    items: Vec<RItem<O, L>>,
    filters: Vec<Filter<O, L>>,
    /// Scalar variable names by slot (the simple items' variables).
    scalars: Vec<String>,
    /// Globals the right-hand side, `:let`, or `:when` name, bound in every match.
    rhs_globals: Vec<(String, GlobalVarId)>,
    /// The right-hand side in `collection.rs`'s language, where its checker accepts
    /// it: its evaluator then checks `seq_rhs`'s in debug builds.
    legacy: Option<LegacyRhs>,
    /// The match layout of the rule and its right-hand side resolved against it
    /// (`crate::seq_rhs`), evaluated by the relational engine.
    pub seq_shape: crate::resolve::MatchShape,
    pub seq_rhs: crate::seq_rhs::SeqRhs<O, L>,
    /// The left-hand side as the assembly reads it (`crate::seq_collect`).
    pub spec: crate::seq_collect::Spec,
    /// Each filter's base as an ordinary sub-query with a distinguished root
    /// (`crate::seq_query`), in `filters` order.
    pub filter_queries: Vec<crate::seq_query::SubQuery<O, S, L>>,
    /// The relational engine's query: `Join n ← ByOp(root); Collect(n)`, over
    /// `seq_shape` with the root node `root_var` (`crate::seq_engine`).
    pub query: crate::resolve::ResolvedQuery<O, S, L>,
    pub root_var: crate::ast::VarId,
    /// `:flatten` (`SurfaceRule::flatten`). The root is n-ary by construction, so the
    /// tag always has an operator to act on.
    pub flatten: bool,
    pub span: Span,
}

/// The type of a name or an expression: a scalar or a sequence of one sort, or the
/// tuples a sequence primitive returns. Sorts are named as the registry and the
/// literal model name them (`i64`, `MLTL`).
#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Scalar(String),
    Seq(String),
    Tuples(Vec<String>),
}

const REDUCTIONS: &[&str] = &["min", "max", "sum", "count"];

/// Registered sequence primitives: their arity (0 for any) and, from the element
/// sorts of their arguments, the sorts of the tuples they return.
fn seq_primitive_sig(name: &str) -> Option<(usize, fn(&[String]) -> Vec<String>)> {
    match name {
        // (union-by p l u) -> (q a b): q of p's sort, a and b of l's and u's.
        "union-by" => Some((3, |a| vec![a[0].clone(), a[1].clone(), a[2].clone()])),
        // (narrow c d r a b q) -> (r2 c2 d2).
        "narrow" | "narrowed" => Some((6, |a| vec![a[2].clone(), a[0].clone(), a[1].clone()])),
        "zip" => Some((0, |a| a.to_vec())),
        _ => None,
    }
}

type CheckResult<T> = Result<T, (String, Span)>;

/// Check a sequence rule against the declared operators and the globals in scope.
pub fn check<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
>(
    r: &SurfaceRule,
    ruleset: Option<crate::apply::RulesetId>,
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    model: &M,
    globals: &GlobalCtx<Cfg::S>,
    index: usize,
) -> CheckResult<Rule<Cfg::O, Cfg::S, L>>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let SurfacePattern::App {
        op,
        prefix,
        children,
        suffix,
        span,
    } = &r.lhs
    else {
        return Err((
            "a sequence rule's left-hand side is an application".into(),
            r.lhs.span(),
        ));
    };
    let root = eg
        .op(op)
        .ok_or_else(|| (format!("unknown operator '{op}'"), *span))?;
    let info = eg.ops().info(root);
    let assoc = matches!(info.kind, OpKind::A { .. });
    let ac = matches!(info.kind, OpKind::MSet { .. });
    let child_sort = match &info.kind {
        OpKind::Set { arg_sort, .. }
        | OpKind::A { arg_sort, .. }
        | OpKind::MSet { arg_sort, .. } => *arg_sort,
        OpKind::Commutative { .. } => {
            return Err((
                format!(
                    "sequence patterns are not allowed under the commutative operator '{op}': it has exactly \
                     two children, so write the rule with two simple patterns"
                ),
                *span,
            ));
        }
        _ => {
            if children.iter().any(SurfacePatChild::is_sequence) {
                return Err((
                    format!(
                        "a sequence pattern needs an associative, AC, or ACI operator; '{op}' is none"
                    ),
                    *span,
                ));
            }
            return Err((
                format!(
                    "sequence patterns below the root node are not supported yet: '{op}' is the root"
                ),
                *span,
            ));
        }
    };
    let root_sort = sort_name(eg, child_sort);
    let mut env: BTreeMap<String, Ty> = BTreeMap::new();
    let bind = |env: &mut BTreeMap<String, Ty>, n: &str, t: Ty, s: Span| -> CheckResult<()> {
        if globals.get(n).is_some() {
            return Err((
                format!("'{n}' names a global; a sequence cannot rebind it"),
                s,
            ));
        }
        if env.insert(n.to_string(), t).is_some() {
            return Err((format!("'{n}' is bound twice"), s));
        }
        Ok(())
    };
    let mut items = Vec::new();
    let mut filters = Vec::new();
    let mut filter_queries = Vec::new();
    // The simple items' patterns, in item order, for their sub-queries.
    let mut one_pats: Vec<&SurfacePattern> = Vec::new();
    let mut excepts: Vec<(usize, String, Span)> = Vec::new();
    let mut bare = 0;
    let mut scalars: Vec<String> = Vec::new();
    let mut scalar_sorts: Vec<String> = Vec::new();
    // A name is a multiplicity or a pattern variable, not both, as in the ordinary
    // language (`MatchShape::check_kind`): the simple items' names, then each filter's.
    let kinds_disjoint =
        |pats: &[&SurfacePattern], mults: &[&crate::ast::MultSpec], s: Span| -> CheckResult<()> {
            let mut names = Vec::new();
            for p in pats {
                pattern_vars(p, &mut names);
            }
            for m in mults {
                if let crate::ast::MultSpec::Var { name, .. } = m
                    && names.contains(name)
                {
                    return Err((
                        format!("'{name}' is bound as a multiplicity and as a pattern variable"),
                        s,
                    ));
                }
            }
            Ok(())
        };
    {
        let mut pats = Vec::new();
        let mut mults = Vec::new();
        for c in children {
            match c {
                SurfacePatChild::Elem(p) => pats.push(p),
                SurfacePatChild::ElemMult(p, m) => {
                    pats.push(p);
                    mults.push(m);
                }
                SurfacePatChild::Filter {
                    base,
                    mult,
                    span: fs,
                    ..
                } => kinds_disjoint(&[&**base], &mult.iter().collect::<Vec<_>>(), *fs)?,
                SurfacePatChild::Seq(..) => {}
            }
        }
        kinds_disjoint(&pats, &mults, *span)?;
    }
    if let Some((n, s)) = prefix {
        bind(&mut env, n, Ty::Seq(root_sort.clone()), *s)?;
        items.push(RItem::Bare(n.clone()));
        bare += 1;
    }
    for c in children {
        match c {
            SurfacePatChild::Elem(p) => {
                // "§Semantics table, AC and ACI: `pattern`: any one child not taken by
                // another item". Its variables are scalars, shared by all simple items.
                let pat = check_pat(
                    eg,
                    model,
                    globals,
                    p,
                    child_sort,
                    &mut scalars,
                    &mut scalar_sorts,
                )?;
                one_pats.push(p);
                items.push(RItem::One(pat, None));
            }
            SurfacePatChild::ElemMult(p, m) => {
                if !ac {
                    return Err((
                        format!(
                            "a multiplicity annotation needs an AC operator; '{op}' is not one"
                        ),
                        p.span(),
                    ));
                }
                let pat = check_pat(
                    eg,
                    model,
                    globals,
                    p,
                    child_sort,
                    &mut scalars,
                    &mut scalar_sorts,
                )?;
                one_pats.push(p);
                let mc = mult_check(m, &mut scalars, &mut scalar_sorts, p.span())?;
                items.push(RItem::One(pat, Some(mc)));
            }
            SurfacePatChild::Seq(n, s) => {
                bind(&mut env, n, Ty::Seq(root_sort.clone()), *s)?;
                items.push(RItem::Bare(n.clone()));
                bare += 1;
            }
            SurfacePatChild::Filter {
                name,
                mult,
                base,
                except,
                span: fs,
            } => {
                let mut vars = Vec::new();
                let mut sorts = Vec::new();
                let pat = check_pat(eg, model, globals, base, child_sort, &mut vars, &mut sorts)?;
                // The pattern's variables, before the annotation adds its own.
                filter_queries.push(
                    crate::seq_query::sub_query(
                        base,
                        child_sort,
                        &vars,
                        eg.ops(),
                        eg.sorts(),
                        model,
                        globals,
                    )
                    .map_err(|m| (m, *fs))?,
                );
                // "§Multiplicities and `zip`: A filter may carry the ordinary
                // multiplicity annotation after its name ... Under ACI every
                // multiplicity is 1, and an annotation is accepted only if 1 satisfies it."
                let mult = match mult {
                    None => None,
                    Some(m) => {
                        if assoc {
                            return Err((
                                format!(
                                    "a multiplicity annotation needs an AC operator; '{op}' is associative"
                                ),
                                *fs,
                            ));
                        }
                        let mc = mult_check(m, &mut vars, &mut sorts, *fs)?;
                        if !ac && !mc.accepts(1) {
                            return Err((
                                format!(
                                    "the annotation of '{name}' rejects multiplicity 1, the only one under '{op}' (ACI)"
                                ),
                                *fs,
                            ));
                        }
                        Some(mc)
                    }
                };
                bind(&mut env, name, Ty::Seq(root_sort.clone()), *fs)?;
                for (v, so) in vars.iter().zip(&sorts) {
                    bind(&mut env, v, Ty::Seq(so.clone()), *fs)?;
                }
                if let Some((other, es)) = except {
                    if assoc {
                        return Err(("`:except` is an AC and ACI construct; under an associative operator order separates runs".into(), *es));
                    }
                    excepts.push((filters.len(), other.clone(), *es));
                }
                items.push(RItem::Filter(filters.len()));
                filters.push(Filter {
                    name: name.clone(),
                    pat,
                    vars,
                    except: None,
                    mult,
                    sorts,
                });
            }
        }
    }
    if let Some((n, s)) = suffix {
        bind(&mut env, n, Ty::Seq(root_sort.clone()), *s)?;
        items.push(RItem::Bare(n.clone()));
        bare += 1;
    }
    // "§Semantics table, under AC, ACI: `..name` ... at most one per node". Under A
    // any number of gaps is allowed: position tells them apart.
    if !assoc && bare > 1 {
        return Err((
            format!(
                "two bare sequences under '{op}' (AC or ACI): the children they share are indistinguishable"
            ),
            *span,
        ));
    }
    for (fi, other, es) in excepts {
        let Some(oi) = filters
            .iter()
            .position(|f| f.name == other)
            .filter(|&oi| oi != fi)
        else {
            return Err((format!("`:except {other}` names no sibling filter"), es));
        };
        filters[fi].except = Some(oi);
    }
    // "§Edge cases 4: The checker rejects a cycle in the `:except` relation". Each
    // filter excepts at most one other, so following `except` from a filter either
    // stops or returns to it within `filters.len()` steps.
    for start in 0..filters.len() {
        let mut at = start;
        for _ in 0..filters.len() {
            match filters[at].except {
                Some(next) if next == start => {
                    let mut cycle = vec![filters[start].name.clone()];
                    let mut k = filters[start]
                        .except
                        .expect("the cycle starts with an except");
                    while k != start {
                        cycle.push(filters[k].name.clone());
                        k = filters[k].except.expect("a cycle member has an except");
                    }
                    cycle.push(filters[start].name.clone());
                    return Err((
                        format!(
                            "an `:except` cycle ({}): a child matching every filter of it would go to none",
                            cycle.join(" -> ")
                        ),
                        *span,
                    ));
                }
                Some(next) => at = next,
                None => break,
            }
        }
    }
    for (v, so) in scalars.iter().zip(&scalar_sorts) {
        bind(&mut env, v, Ty::Scalar(so.clone()), *span)?;
    }
    // The right-hand side, `:let`, and `:when` in the ordinary right-hand-side
    // language, resolved against the match layout the relational engine fills
    // (`crate::seq_rhs`): the rule's typing and its evaluation.
    let mult_scalars: Vec<String> = items
        .iter()
        .filter_map(|i| {
            if let RItem::One(_, Some(MultCheck { slot: Some(sl), .. })) = i {
                Some(scalars[*sl].clone())
            } else {
                None
            }
        })
        .collect();
    let (mut seq_shape, names) = seq_shape(
        eg,
        &items,
        &filters,
        &scalars,
        &scalar_sorts,
        &mult_scalars,
        assoc,
        ac,
        child_sort,
        *span,
    )?;
    let seq_rhs = crate::seq_rhs::resolve(
        &r.rhs_term,
        &r.lets_term,
        &r.when_term,
        info.return_sort,
        &seq_shape,
        &names,
        eg.ops(),
        eg.sorts(),
        model,
        globals,
    )?;
    // The same, in `collection.rs`'s own expression language, where its checker
    // accepts them: debug builds evaluate both and compare (step 2 of
    // `doc/goal-sequence-patterns-engine.md`).
    let mut rhs_globals = Vec::new();
    let legacy =
        r.legacy
            .as_ref()
            .filter(|l| {
                (|| -> CheckResult<()> {
                    for (name, e) in &l.lets {
                        let t = infer(eg, model, globals, &env, &mut rhs_globals, e)?;
                        let Ty::Scalar(_) = t else {
                            return Err((sequence_as_scalar(), e.span()));
                        };
                        bind(&mut env, name, t, e.span())?;
                    }
                    for g in &l.when {
                        match infer(eg, model, globals, &env, &mut rhs_globals, g)? {
                            Ty::Scalar(so) if so == "bool" => {}
                            Ty::Scalar(so) => {
                                return Err((
                                    format!("a guard of sort '{so}'; a guard is a bool"),
                                    g.span(),
                                ))
                            }
                            _ => return Err((sequence_as_scalar(), g.span())),
                        }
                    }
                    match infer(eg, model, globals, &env, &mut rhs_globals, &l.rhs)? {
                        Ty::Scalar(so) if so == sort_name(eg, info.return_sort) => {}
                        Ty::Scalar(so) => return Err((
                            format!(
                                "the right-hand side has sort '{so}'; the left-hand side has '{}'",
                                sort_name(eg, info.return_sort)
                            ),
                            l.rhs.span(),
                        )),
                        _ => return Err((sequence_as_scalar(), l.rhs.span())),
                    }
                    rhs_globals.sort();
                    rhs_globals.dedup();
                    Ok(())
                })()
                .is_ok()
            })
            .cloned();
    let mut ones = 0;
    let spec = crate::seq_collect::Spec {
        assoc,
        ac,
        items: items
            .iter()
            .map(|i| match i {
                RItem::One(_, m) => {
                    ones += 1;
                    crate::seq_collect::SItem::One(ones - 1, *m)
                }
                RItem::Bare(n) => crate::seq_collect::SItem::Bare(n.clone()),
                RItem::Filter(fi) => crate::seq_collect::SItem::Filter(*fi),
            })
            .collect(),
        filters: filters
            .iter()
            .map(|f| crate::seq_collect::SFilter {
                name: f.name.clone(),
                vars: f.vars.clone(),
                except: f.except,
                mult: f.mult,
            })
            .collect(),
        scalars: scalars.clone(),
    };
    // The outer query of the relational engine: `Join n ← ByOp(root); Collect(n)`
    // over the rule's layout (Semper design §7.6, "Lowering").
    let root_var = seq_shape.intern_var("?root").map_err(|m| (m, *span))?;
    if one_pats.len() != ones {
        return Err((
            format!(
                "internal: {} simple-item patterns for {ones} simple items",
                one_pats.len()
            ),
            *span,
        ));
    }
    let mut one_queries = Vec::with_capacity(one_pats.len());
    let mut one_slots = Vec::with_capacity(one_pats.len());
    for p in &one_pats {
        let mut vs = Vec::new();
        pattern_vars(p, &mut vs);
        let mut seen = Vec::new();
        vs.retain(|v| {
            globals.get(v).is_none() && !seen.contains(v) && {
                seen.push(v.clone());
                true
            }
        });
        let sq =
            crate::seq_query::sub_query(p, child_sort, &vs, eg.ops(), eg.sorts(), model, globals)
                .map_err(|m| (m, p.span()))?;
        let slots = sq
            .vars
            .iter()
            .map(|(n, _)| {
                scalars
                    .iter()
                    .position(|v| v == n)
                    .ok_or_else(|| (format!("internal: '{n}' is not a scalar"), p.span()))
            })
            .collect::<CheckResult<Vec<usize>>>()?;
        one_queries.push(sq);
        one_slots.push(slots);
    }
    let layout = crate::seq_engine::Layout {
        filters: seq_shape
            .filters
            .iter()
            .map(|f| (f.elems, f.cols.iter().map(|(_, c)| *c).collect()))
            .collect(),
        bare: items
            .iter()
            .filter_map(|i| {
                if let RItem::Bare(n) = i {
                    Some(n)
                } else {
                    None
                }
            })
            .map(|n| {
                let rr = if assoc {
                    seq_shape.find_seq(n).map(crate::resolve::RestRef::Seq)
                } else if ac {
                    seq_shape.find_mset(n).map(crate::resolve::RestRef::Mset)
                } else {
                    seq_shape.find_set(n).map(crate::resolve::RestRef::Set)
                };
                rr.map(|r| (n.clone(), r))
                    .ok_or_else(|| (format!("internal: ..{n} is not in the layout"), *span))
            })
            .collect::<CheckResult<Vec<_>>>()?,
        scalars: scalars
            .iter()
            .map(|n| {
                use crate::seq_engine::ScalarRef;
                let r = if mult_scalars.contains(n) {
                    seq_shape.find_mult(n).map(ScalarRef::Mult)
                } else if let Some(l) = seq_shape.find_lit_val(n) {
                    Some(ScalarRef::Lit(l))
                } else {
                    seq_shape.find_var(n).map(ScalarRef::Node)
                };
                r.ok_or_else(|| (format!("internal: '{n}' is not in the layout"), *span))
            })
            .collect::<CheckResult<Vec<_>>>()?,
    };
    let collect =
        crate::seq_engine::CollectRef(std::sync::Arc::new(crate::seq_engine::CollectSpec {
            asm: std::sync::Arc::new(crate::seq_engine::Assembly {
                spec: spec.clone(),
                one_slots,
                layout,
            }),
            filters: filter_queries.clone(),
            ones: one_queries,
            op: root,
            // Which filters the rule cannot fire without: the candidates may then come
            // from those filters alone, and part 2 is skipped (§7.6).
            required: seq_rhs.required_nonempty(&seq_shape, model),
            flatten: r.flatten,
        }));
    let mut var_sorts = vec![None; seq_shape.num_vars()];
    var_sorts[root_var.idx()] = Some(info.return_sort);
    for (n, s) in &names.node_sorts {
        if let Some(v) = seq_shape.find_var(n) {
            var_sorts[v.idx()] = Some(*s);
        }
    }
    let rest_sort = |n: &String| {
        names
            .rest_sorts
            .get(n)
            .or_else(|| names.col_sorts.get(n))
            .copied()
            .unwrap_or(child_sort)
    };
    let query = crate::resolve::ResolvedQuery {
        atoms: vec![crate::resolve::RAtom::Collect {
            node: root_var,
            op: root,
            collect,
        }],
        seq_sorts: seq_shape.seqs.iter().map(rest_sort).collect(),
        set_sorts: seq_shape.sets.iter().map(rest_sort).collect(),
        mset_sorts: seq_shape.msets.iter().map(rest_sort).collect(),
        shape: seq_shape.clone(),
        var_sorts,
        mult_intervals: Vec::new(),
        // The sequence rule's `:flatten` is read by its `Collect` step, not by the
        // ordinary n-ary lowering: the query has no other atom.
        flatten: false,
    };
    Ok(Rule {
        name: format!("collection_rule_{index}"),
        rule_id: None,
        ruleset,
        root,
        assoc,
        ac,
        items,
        filters,
        scalars,
        rhs_globals,
        legacy,
        seq_shape,
        seq_rhs,
        spec,
        filter_queries,
        query,
        root_var,
        flatten: r.flatten,
        span: r.span,
    })
}

/// The match layout of a sequence rule: each filter's children in the pool of the
/// root's kind (a sequence under A, a set under ACI, a multiset under AC) and its
/// pattern variables as columns (a class-valued one in `seq_pool`, a literal-valued
/// one in `lit_seq_pool`, an AC filter's multiplicity variable read from its
/// multiset); a bare sequence as a rest; a simple item's variables as scalars.
#[allow(clippy::too_many_arguments)]
fn seq_shape<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>(
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    items: &[RItem<Cfg::O, L>],
    filters: &[Filter<Cfg::O, L>],
    scalars: &[String],
    scalar_sorts: &[String],
    mult_scalars: &[String],
    assoc: bool,
    ac: bool,
    child_sort: Cfg::S,
    span: Span,
) -> CheckResult<(crate::resolve::MatchShape, crate::seq_rhs::SeqNames<Cfg::S>)>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    use crate::resolve::{ColRef, FilterShape, MatchShape, RestRef};
    let e = |m: String| (m, span);
    let sort = |so: &str| {
        eg.sorts()
            .id_by_name(so)
            .ok_or_else(|| (format!("unknown sort '{so}'"), span))
    };
    let mut shape = MatchShape::default();
    let mut names = crate::seq_rhs::SeqNames {
        node_sorts: std::collections::HashMap::new(),
        lit_sorts: std::collections::HashMap::new(),
        rest_sorts: std::collections::HashMap::new(),
        col_sorts: std::collections::HashMap::new(),
    };
    let rest = |shape: &mut MatchShape, name: &str| -> CheckResult<RestRef> {
        Ok(if assoc {
            RestRef::Seq(shape.intern_seq(name).map_err(e)?)
        } else if ac {
            RestRef::Mset(shape.intern_mset(name).map_err(e)?)
        } else {
            RestRef::Set(shape.intern_set(name).map_err(e)?)
        })
    };
    for f in filters {
        let elems = rest(&mut shape, &f.name)?;
        names.rest_sorts.insert(f.name.clone(), child_sort);
        let mult_var = f.mult.and_then(|m| m.slot).map(|sl| f.vars[sl].clone());
        let mut cols = Vec::with_capacity(f.vars.len());
        for (v, so) in f.vars.iter().zip(&f.sorts) {
            let s = sort(so)?;
            let col = if Some(v) == mult_var.as_ref() {
                let RestRef::Mset(m) = elems else {
                    return Err((format!("'{v}': a multiplicity column outside AC"), span));
                };
                ColRef::Mult(m)
            } else if eg.ops().lit_op_for_sort(s).is_some() {
                ColRef::Lit(shape.intern_lit_seq(v).map_err(e)?)
            } else {
                ColRef::Node(shape.intern_seq(v).map_err(e)?)
            };
            names.col_sorts.insert(v.clone(), s);
            cols.push((v.clone(), col));
        }
        shape.filters.push(FilterShape {
            name: f.name.clone(),
            elems,
            cols,
        });
    }
    for i in items {
        if let RItem::Bare(n) = i {
            rest(&mut shape, n)?;
            names.rest_sorts.insert(n.clone(), child_sort);
        }
    }
    for (v, so) in scalars.iter().zip(scalar_sorts) {
        if mult_scalars.contains(v) {
            shape.intern_mult(v).map_err(e)?;
            continue;
        }
        let s = sort(so)?;
        if eg.ops().lit_op_for_sort(s).is_some() {
            shape.intern_lit_val(v).map_err(e)?;
            names.lit_sorts.insert(v.clone(), s);
        } else {
            shape.intern_var(v).map_err(e)?;
            names.node_sorts.insert(v.clone(), s);
        }
    }
    Ok((shape, names))
}

/// A multiplicity annotation as an interval, the variable it binds added to `vars`
/// with sort `i64` (a multiplicity is read as an integer). The interval is empty,
/// and the rule rejected, when no multiplicity satisfies it.
/// The variable names of a surface pattern, globals included (the check resolves them).
fn pattern_vars(p: &SurfacePattern, out: &mut Vec<String>) {
    match p {
        SurfacePattern::Var(n, _) => out.push(n.clone()),
        SurfacePattern::Lit(..) => {}
        SurfacePattern::App { children, .. } => {
            for c in children {
                if let SurfacePatChild::Elem(q) | SurfacePatChild::ElemMult(q, _) = c {
                    pattern_vars(q, out);
                }
            }
        }
    }
}

fn mult_check(
    m: &crate::ast::MultSpec,
    vars: &mut Vec<String>,
    sorts: &mut Vec<String>,
    span: Span,
) -> CheckResult<MultCheck> {
    use crate::ast::{CmpOp, MultSpec};
    let mut mc = MultCheck {
        lo: 1,
        hi: u64::MAX,
        ne: None,
        slot: None,
    };
    let empty = || {
        (
            "an unsatisfiable multiplicity annotation: no multiplicity satisfies it".to_string(),
            span,
        )
    };
    match m {
        MultSpec::Exact(n) => {
            mc.lo = *n;
            mc.hi = *n;
        }
        MultSpec::Var { name, constraint } => {
            let slot = vars.iter().position(|v| v == name).unwrap_or_else(|| {
                vars.push(name.clone());
                sorts.push("i64".into());
                vars.len() - 1
            });
            mc.slot = Some(slot);
            match constraint {
                None => {}
                Some((CmpOp::Ge, n)) => mc.lo = mc.lo.max(*n),
                Some((CmpOp::Gt, n)) => mc.lo = mc.lo.max(n.checked_add(1).ok_or_else(empty)?),
                Some((CmpOp::Le, n)) => mc.hi = *n,
                Some((CmpOp::Lt, n)) => mc.hi = n.checked_sub(1).ok_or_else(empty)?,
                Some((CmpOp::Eq, n)) => {
                    mc.lo = mc.lo.max(*n);
                    mc.hi = *n;
                }
                Some((CmpOp::Ne, n)) => mc.ne = Some(*n),
            }
        }
    }
    if mc.lo > mc.hi || (mc.lo == mc.hi && mc.ne == Some(mc.lo)) {
        return Err(empty());
    }
    Ok(mc)
}

fn sequence_as_scalar() -> String {
    "a sequence used as a scalar: use it inside a reduction (min, max, sum, count) or a comprehension".into()
}

fn sort_name<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>(
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    s: Cfg::S,
) -> String
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    eg.sorts().name(s).to_string()
}

/// Check a filter's pattern (`base`, `doc/sequence-patterns.md` §Grammar) at a
/// position of sort `sort`, collecting its variables and their sorts.
fn check_pat<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
>(
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    model: &M,
    globals: &GlobalCtx<Cfg::S>,
    p: &SurfacePattern,
    sort: Cfg::S,
    vars: &mut Vec<String>,
    sorts: &mut Vec<String>,
) -> CheckResult<Pat<Cfg::O, L>>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let literal = eg.ops().lit_op_for_sort(sort).is_some();
    match p {
        SurfacePattern::Var(n, s) => {
            // "§Grammar: A name bound by a global `let` is the global, resolved through
            // `GlobalCtx` as in ordinary patterns, inside a filter as elsewhere."
            if let Some((gid, gsort, _)) = globals.get(n) {
                if gsort != sort {
                    return Err((
                        format!(
                            "global '{n}' has sort '{}' but position expects '{}'",
                            sort_name(eg, gsort),
                            sort_name(eg, sort)
                        ),
                        *s,
                    ));
                }
                return Ok(Pat::Global(gid));
            }
            let slot = vars.iter().position(|v| v == n).unwrap_or_else(|| {
                vars.push(n.clone());
                sorts.push(sort_name(eg, sort));
                vars.len() - 1
            });
            Ok(Pat::Var { slot, literal })
        }
        SurfacePattern::Lit(t, s) => {
            if !literal {
                return Err(("a literal where no literal sort is expected".into(), *s));
            }
            // Read through the model for the position's sort, so matching compares
            // literals and not their text.
            let so = sort_name(eg, sort);
            let v = model
                .parse_as(&so, t.trim_matches('"'))
                .ok_or_else(|| (format!("'{t}' is not a literal of sort '{so}'"), *s))?;
            Ok(Pat::Lit(v))
        }
        SurfacePattern::App {
            op,
            prefix,
            children,
            suffix,
            span,
        } => {
            if children
                .iter()
                .any(|c| matches!(c, SurfacePatChild::Filter { .. }))
            {
                return Err((
                    "a filter inside a filter: sequence patterns do not nest".into(),
                    *span,
                ));
            }
            if prefix.is_some()
                || suffix.is_some()
                || children
                    .iter()
                    .any(|c| matches!(c, SurfacePatChild::Seq(..)))
            {
                return Err((
                    "a rest inside a filter's pattern is not supported yet".into(),
                    *span,
                ));
            }
            let o = eg
                .op(op)
                .ok_or_else(|| (format!("unknown operator '{op}'"), *span))?;
            let info = eg.ops().info(o);
            if info.return_sort != sort {
                return Err((
                    format!(
                        "'{op}' returns '{}' but position expects '{}'",
                        sort_name(eg, info.return_sort),
                        sort_name(eg, sort)
                    ),
                    *span,
                ));
            }
            let OpKind::Normal { arg_sorts } = &info.kind else {
                return Err((
                    format!(
                        "'{op}' inside a filter must be a plain operator; others are not supported yet"
                    ),
                    *span,
                ));
            };
            if arg_sorts.len() != children.len() {
                return Err((
                    format!(
                        "'{op}' takes {} arguments, not {}",
                        arg_sorts.len(),
                        children.len()
                    ),
                    *span,
                ));
            }
            let mut kids = Vec::new();
            for (c, &s) in children.iter().zip(arg_sorts.iter()) {
                let SurfacePatChild::Elem(c) = c else {
                    return Err((
                        "a multiplicity inside a filter's pattern is not supported".into(),
                        *span,
                    ));
                };
                kids.push(check_pat(eg, model, globals, c, s, vars, sorts)?);
            }
            Ok(Pat::App(o, kids))
        }
    }
}

/// The type of an expression over the rule's names, recording the globals it names.
fn infer<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
>(
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    model: &M,
    globals: &GlobalCtx<Cfg::S>,
    env: &BTreeMap<String, Ty>,
    used: &mut Vec<(String, GlobalVarId)>,
    e: &CExpr,
) -> CheckResult<Ty>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let rec = |env: &BTreeMap<String, Ty>, used: &mut Vec<(String, GlobalVarId)>, e: &CExpr| {
        infer(eg, model, globals, env, used, e)
    };
    match e {
        CExpr::Lit(t, s) => {
            if t.starts_with('"') {
                return Ok(Ty::Scalar("String".into()));
            }
            model
                .parse_any(t)
                .map(|(so, _)| Ty::Scalar(so.to_string()))
                .ok_or_else(|| (format!("cannot read literal '{t}'"), *s))
        }
        CExpr::Var(n, s) => {
            if let Some(t) = env.get(n) {
                return Ok(t.clone());
            }
            if let Some((gid, gsort, _)) = globals.get(n) {
                used.push((n.clone(), gid));
                return Ok(Ty::Scalar(sort_name(eg, gsort)));
            }
            Err((format!("unbound variable '{n}'"), *s))
        }
        CExpr::App { op, children, span } => {
            let exprs = || -> CheckResult<Vec<&CExpr>> {
                children
                    .iter()
                    .map(|c| match c {
                        CChild::Expr(e) => Ok(e),
                        CChild::Splice(_, s) | CChild::Comp { span: s, .. } => {
                            Err((format!("'{op}' takes no spliced arguments"), *s))
                        }
                    })
                    .collect()
            };
            if REDUCTIONS.contains(&op.as_str()) {
                let args = exprs()?;
                if args.len() != 1 {
                    return Err((format!("'{op}' takes one sequence"), *span));
                }
                return match (op.as_str(), rec(env, used, args[0])?) {
                    ("count", Ty::Seq(_) | Ty::Tuples(_)) => Ok(Ty::Scalar("i64".into())),
                    (_, Ty::Seq(so)) => {
                        let prim = if op == "sum" { "+" } else { op.as_str() };
                        if model
                            .find_op(&format!("{so}::{prim}"))
                            .or_else(|| model.find_op(prim))
                            .is_none()
                        {
                            return Err((
                                format!("'{op}' over sort '{so}': no primitive '{prim}'"),
                                *span,
                            ));
                        }
                        Ok(Ty::Scalar(so))
                    }
                    _ => Err((format!("'{op}' reduces a sequence"), *span)),
                };
            }
            if let Some((arity, ret)) = seq_primitive_sig(op) {
                let args = exprs()?;
                if arity != 0 && args.len() != arity {
                    return Err((format!("'{op}' takes {arity} sequences"), *span));
                }
                let mut elems = Vec::new();
                for a in args {
                    match rec(env, used, a)? {
                        Ty::Seq(so) => elems.push(so),
                        _ => return Err((format!("'{op}' takes sequences"), a.span())),
                    }
                }
                return Ok(Ty::Tuples(ret(&elems)));
            }
            if op == "if" {
                let args = exprs()?;
                if args.len() != 3 {
                    return Err(("(if cond then else)".into(), *span));
                }
                match rec(env, used, args[0])? {
                    Ty::Scalar(so) if so == "bool" => {}
                    _ => return Err(("the condition of an if is a bool".into(), args[0].span())),
                }
                let (a, b) = (rec(env, used, args[1])?, rec(env, used, args[2])?);
                if a != b {
                    return Err((
                        format!("the branches of an if differ: {a:?} and {b:?}"),
                        *span,
                    ));
                }
                let Ty::Scalar(_) = a else {
                    return Err((sequence_as_scalar(), args[1].span()));
                };
                return Ok(a);
            }
            if let Some(o) = eg.op(op)
                && is_term_op(eg, o)
            {
                let info = eg.ops().info(o);
                let ret = Ty::Scalar(sort_name(eg, info.return_sort));
                let expect = |got: Ty, want: Cfg::S, s: Span| -> CheckResult<()> {
                    let want = sort_name(eg, want);
                    match got {
                        Ty::Scalar(so) if so == want => Ok(()),
                        Ty::Scalar(so) => Err((
                            format!("an argument of sort '{so}' to '{op}', which expects '{want}'"),
                            s,
                        )),
                        _ => Err((sequence_as_scalar(), s)),
                    }
                };
                match &info.kind {
                    OpKind::Normal { arg_sorts } => {
                        let args = exprs()?;
                        if args.len() != arg_sorts.len() {
                            return Err((
                                format!(
                                    "'{op}' takes {} arguments, not {}",
                                    arg_sorts.len(),
                                    args.len()
                                ),
                                *span,
                            ));
                        }
                        for (a, &so) in args.iter().zip(arg_sorts) {
                            expect(rec(env, used, a)?, so, a.span())?;
                        }
                    }
                    OpKind::Commutative { arg_sorts } => {
                        let args = exprs()?;
                        if args.len() != 2 {
                            return Err((format!("'{op}' takes 2 arguments"), *span));
                        }
                        for (a, &so) in args.iter().zip(arg_sorts) {
                            expect(rec(env, used, a)?, so, a.span())?;
                        }
                    }
                    OpKind::A { arg_sort, .. }
                    | OpKind::MSet { arg_sort, .. }
                    | OpKind::Set { arg_sort, .. } => {
                        let want = sort_name(eg, *arg_sort);
                        for c in children {
                            match c {
                                CChild::Expr(a) => expect(rec(env, used, a)?, *arg_sort, a.span())?,
                                CChild::Splice(n, s) => match env.get(n) {
                                    Some(Ty::Seq(so)) if *so == want => {}
                                    Some(Ty::Seq(so)) => {
                                        return Err((
                                            format!(
                                                "..{n} splices '{so}' into '{op}', which takes '{want}'"
                                            ),
                                            *s,
                                        ));
                                    }
                                    _ => {
                                        return Err((
                                            format!("..{n} splices a sequence of classes"),
                                            *s,
                                        ));
                                    }
                                },
                                CChild::Comp {
                                    body,
                                    vars,
                                    source,
                                    span: cs,
                                } => {
                                    let cols = match rec(env, used, source)? {
                                        Ty::Tuples(ts) => ts,
                                        Ty::Seq(so) => vec![so],
                                        Ty::Scalar(_) => {
                                            return Err((
                                                "a comprehension over a scalar".into(),
                                                *cs,
                                            ));
                                        }
                                    };
                                    if cols.len() != vars.len() {
                                        return Err((
                                            format!(
                                                "a comprehension binding {} names needs a source of that width",
                                                vars.len()
                                            ),
                                            *cs,
                                        ));
                                    }
                                    let mut inner = env.clone();
                                    for (v, so) in vars.iter().zip(cols) {
                                        inner.insert(v.clone(), Ty::Scalar(so));
                                    }
                                    expect(rec(&inner, used, body)?, *arg_sort, body.span())?;
                                }
                            }
                        }
                    }
                    OpKind::Lit => unreachable!("not a term operator"),
                }
                return Ok(ret);
            }
            // A scalar primitive, resolved as at run time by its first argument's sort
            // (`apply_prim`), element-wise when an argument is a sequence.
            let args = exprs()?;
            let tys = args
                .iter()
                .map(|a| rec(env, used, a))
                .collect::<CheckResult<Vec<_>>>()?;
            let first = tys.first().and_then(|t| match t {
                Ty::Scalar(so) | Ty::Seq(so) => Some(so.clone()),
                Ty::Tuples(_) => None,
            });
            let d = first
                .as_ref()
                .and_then(|so| model.find_op(&format!("{so}::{op}")))
                .or_else(|| model.find_op(op))
                .ok_or_else(|| (format!("unknown operator or primitive '{op}'"), *span))?;
            if d.arg_sorts.len() != tys.len() {
                return Err((
                    format!("'{op}' takes {} arguments", d.arg_sorts.len()),
                    *span,
                ));
            }
            let mut seq = false;
            for ((t, want), a) in tys.iter().zip(d.arg_sorts).zip(&args) {
                let so = match t {
                    Ty::Scalar(so) => so,
                    Ty::Seq(so) => {
                        seq = true;
                        so
                    }
                    Ty::Tuples(_) => return Err((format!("'{op}' cannot take tuples"), a.span())),
                };
                if so != want {
                    return Err((
                        format!("an argument of sort '{so}' to '{op}', which expects '{want}'"),
                        a.span(),
                    ));
                }
            }
            Ok(if seq {
                Ty::Seq(d.ret_sort.to_string())
            } else {
                Ty::Scalar(d.ret_sort.to_string())
            })
        }
    }
}

/// An operator that builds a term: not a literal and not a primitive, which both
/// return a literal sort.
fn is_term_op<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>(
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    o: Cfg::O,
) -> bool
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let info = eg.ops().info(o);
    !matches!(info.kind, OpKind::Lit) && eg.ops().lit_op_for_sort(info.return_sort).is_none()
}

// ── Values ───────────────────────────────────────────────────────────────────

/// A class's members, smallest id first, computed once per pass.
struct View<G> {
    members: BTreeMap<usize, Vec<G>>,
}

struct Ctx<
    'a,
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
> where
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    eg: &'a EGraph<Cfg, L, TRACK, PROOFS>,
    model: &'a M,
    view: &'a View<Cfg::G>,
    globals: &'a GlobalCtx<Cfg::S, Cfg::G>,
}

impl<
    'a,
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
> Ctx<'a, Cfg, L, M, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    fn members(&self, class: Cfg::G) -> &[Cfg::G] {
        self.view
            .members
            .get(&self.eg.class_repr(class).to_usize())
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// A global's value: its class, or the literal it holds.
    fn global(&self, gid: GlobalVarId) -> Value<Cfg::G, L> {
        let c = self.eg.class_repr(self.globals.binding(gid));
        match self.literal(c) {
            Some(l) => Value::Lit(l),
            None => Value::Class(c),
        }
    }

    /// Whether `id` is matchable. `FLAG_CONGRUENT_DUP` is deliberately *not* consulted:
    /// matching a congruent duplicate repeats its twin's bindings, which the row and match
    /// deduplication already collapses, and excluding it here would diverge from the
    /// relational engine, whose index keeps it for the reason given in `node_types.rs`.
    fn live(&self, id: Cfg::G) -> bool {
        self.eg.node_flags(id) & crate::node_types::FLAG_SUBSUMED == 0
    }

    /// A node's children as classes with their multiplicities (1 except under AC).
    fn children(&self, id: Cfg::G) -> Result<Vec<(Cfg::G, u64)>, String> {
        let mut out = Vec::new();
        let mut wide = false;
        self.eg.for_each_child(id, |c, m| match m.to_u64() {
            Some(m) => out.push((self.eg.class_repr(c), m)),
            None => wide = true,
        });
        if wide {
            return Err("a multiplicity wider than 64 bits".into());
        }
        Ok(out)
    }

    /// The literal a class holds: its first literal member.
    fn literal(&self, class: Cfg::G) -> Option<L> {
        self.members(class)
            .iter()
            .find_map(|&m| self.eg.get_lit_val(m).cloned())
    }

    /// Every match of `p` against `class`, extending `b`: one per member, and per
    /// member of the classes below, that matches ("§Semantics, Member choice: each
    /// is a separate match").
    fn match_all(
        &self,
        p: &Pat<Cfg::O, L>,
        class: Cfg::G,
        b: &Slots<Cfg::G, L>,
    ) -> Result<Vec<Slots<Cfg::G, L>>, String> {
        Ok(match p {
            Pat::Var { slot, literal } => {
                let v = if *literal {
                    match self.literal(class) {
                        Some(l) => Value::Lit(l),
                        None => return Ok(vec![]),
                    }
                } else {
                    Value::Class(self.eg.class_repr(class))
                };
                match &b[*slot] {
                    None => {
                        let mut b = b.clone();
                        b[*slot] = Some(v);
                        vec![b]
                    }
                    Some(old) if value_eq(old, &v) => vec![b.clone()],
                    Some(_) => vec![],
                }
            }
            Pat::Global(gid) => {
                if self.eg.class_repr(self.globals.binding(*gid)) == self.eg.class_repr(class) {
                    vec![b.clone()]
                } else {
                    vec![]
                }
            }
            Pat::Lit(want) => {
                if self.literal(class).is_some_and(|l| l == *want) {
                    vec![b.clone()]
                } else {
                    vec![]
                }
            }
            Pat::App(op, kids) => {
                let mut out = Vec::new();
                for &m in self.members(class) {
                    if self.eg.node_op(m) != *op || !self.live(m) {
                        continue;
                    }
                    let cs = self.children(m)?;
                    if cs.len() != kids.len() {
                        continue;
                    }
                    let mut acc = vec![b.clone()];
                    for (k, (c, _)) in kids.iter().zip(cs) {
                        let mut next = Vec::new();
                        for bb in &acc {
                            next.extend(self.match_all(k, c, bb)?);
                        }
                        acc = next;
                        if acc.is_empty() {
                            break;
                        }
                    }
                    out.extend(acc);
                }
                out
            }
        })
    }
}

// ── The pass ─────────────────────────────────────────────────────────────────

/// One match of a rule: its root node's class and the bindings.
struct Match<G, L> {
    class: G,
    env: BTreeMap<String, Value<G, L>>,
}

/// What a pass did, beyond the merges.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PassReport {
    /// Merges that changed the graph.
    pub changed: usize,
    /// Matches whose right-hand side has no value ("§Edge cases 1"): not fired.
    pub no_value: usize,
    /// Nodes skipped for producing more than `MAX_MATCHES` matches ("§Edge cases 2").
    pub skipped_nodes: usize,
    /// Matches skipped for a right-hand side over `crate::seq_rhs::MAX_WIDTH`.
    pub too_wide: usize,
}

impl PassReport {
    pub fn add(&mut self, o: &PassReport) {
        self.changed = self.changed.saturating_add(o.changed);
        self.no_value = self.no_value.saturating_add(o.no_value);
        self.skipped_nodes = self.skipped_nodes.saturating_add(o.skipped_nodes);
        self.too_wide = self.too_wide.saturating_add(o.too_wide);
    }

    /// A match whose right-hand side has no value is not fired and is reported, not
    /// an error (`doc/sequence-patterns.md`, Edge cases 1).
    pub fn warn(&self) {
        if self.no_value > 0 {
            eprintln!(
                "warning: sequence rules: {} matches with a right-hand side of no value were not fired",
                self.no_value
            );
        }
        if self.skipped_nodes > 0 {
            eprintln!(
                "warning: sequence rules: {} node(s) not matched: over the match bound or a \
                 flattened-view bound, or a flattened count past the multiplicity width",
                self.skipped_nodes
            );
        }
    }
}

/// Match every rule on the graph as it stands, then build every right-hand side
/// and merge it into its match's class.
///
/// Route 1, retired as a run mode on 2026-10-02 (`doc/goal-stable-extraction.md`,
/// step 0): no command reaches it. It stays as the reference implementation that
/// `tests/seq_differential.rs` checks the relational engine against.
pub fn pass<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
>(
    eg: &mut EGraph<Cfg, L, TRACK, PROOFS>,
    model: &M,
    globals: &GlobalCtx<Cfg::S, Cfg::G>,
    rules: &[&Rule<Cfg::O, Cfg::S, L>],
) -> Result<PassReport, String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let mut report = PassReport::default();
    let mut members: BTreeMap<usize, Vec<Cfg::G>> = BTreeMap::new();
    for id in eg.node_ids() {
        members
            .entry(eg.class_repr(id).to_usize())
            .or_default()
            .push(id);
    }
    for v in members.values_mut() {
        v.sort_by_key(|id| id.to_usize());
    }
    let view = View { members };
    // Debug builds evaluate each match with `collection.rs`'s evaluator too, where its
    // checker accepted the rule, and require the same verdict and the same term.
    let parity = cfg!(debug_assertions);
    struct Cand<G, L> {
        rule: usize,
        m: Match<G, L>,
        /// `collection.rs`'s verdict: the environment with its `:let`s if it fires.
        legacy: Option<Option<BTreeMap<String, Value<G, L>>>>,
    }
    let mut cands: Vec<Cand<Cfg::G, L>> = Vec::new();
    {
        let cx = Ctx {
            eg,
            model,
            view: &view,
            globals,
        };
        let stats = std::env::var_os("SEMPER_COLLECTION_STATS");
        for id in eg.node_ids() {
            if !cx.live(id) {
                continue;
            }
            let op = eg.node_op(id);
            for (ri, r) in rules.iter().enumerate() {
                if r.root != op {
                    continue;
                }
                if let Some(path) = &stats {
                    record_overlap(&cx, r, id, path);
                }
                let ms = match match_root(&cx, r, id) {
                    Ok(ms) => ms,
                    Err(e) if crate::seq_collect::is_over_bound(&e) => {
                        eprintln!("warning: {}: a node with {e} skipped", r.name);
                        report.skipped_nodes += 1;
                        continue;
                    }
                    Err(e) => return Err(format!("{}: {e}", r.name)),
                };
                for m in ms {
                    let legacy = match &r.legacy {
                        Some(l) if parity => Some(legacy_verdict(&cx, r, l, &m.env)?),
                        _ => None,
                    };
                    cands.push(Cand {
                        rule: ri,
                        m,
                        legacy,
                    });
                }
            }
        }
    }
    // Every guard is read before any right-hand side is built or merged.
    let mut plans = Vec::new();
    for c in cands {
        let r = rules[c.rule];
        let q = to_query(eg, r, &c.m.env).map_err(|e| format!("{}: {e}", r.name))?;
        let lets = crate::seq_rhs::prelude(&r.seq_rhs, &r.seq_shape, &q, eg, model)
            .map_err(|e| format!("{}: {e}", r.name))?;
        if let Some(l) = &c.legacy
            && l.is_some() != lets.is_some()
        {
            return Err(format!(
                "{}: parity: collection.rs {} a match that seq_rhs {}",
                r.name,
                fire_word(l.is_some()),
                fire_word(lets.is_some())
            ));
        }
        if let Some(lets) = lets {
            plans.push((c.rule, c.m.class, q, lets, c.legacy.flatten()));
        }
    }
    for (ri, class, q, lets, legacy) in plans {
        let r = rules[ri];
        let new =
            match crate::seq_rhs::build(&r.seq_rhs, lets, &r.seq_shape, &q, eg, model, globals) {
                Ok(g) => Some(g),
                // "§Edge cases 1": a right-hand side with no value does not fire.
                Err(e) if e == crate::seq_rhs::NO_FIRE => None,
                Err(e) if e == crate::seq_rhs::TOO_WIDE => {
                    eprintln!(
                        "warning: {}: a right-hand side of {} skipped",
                        r.name,
                        crate::seq_rhs::TOO_WIDE
                    );
                    report.too_wide += 1;
                    continue;
                }
                Err(e) => return Err(format!("{}: {e}", r.name)),
            };
        if let (Some(env), Some(l)) = (legacy, &r.legacy) {
            let old = match build(eg, model, &env, &l.rhs) {
                Ok(Value::Class(g)) => Some(g),
                Ok(_) => return Err(format!("{}: the right-hand side is not a term", r.name)),
                Err(e) if e == NO_VALUE || e == EMPTY => None,
                Err(e) => return Err(format!("{}: {e}", r.name)),
            };
            if old.map(|g| eg.find(g)) != new.map(|g| eg.find(g)) {
                return Err(format!(
                    "{}: parity: the right-hand sides differ (collection.rs {old:?}, seq_rhs {new:?})",
                    r.name
                ));
            }
        }
        let Some(new) = new else {
            report.no_value += 1;
            continue;
        };
        let merged = match r.rule_id {
            Some(rule_id) if PROOFS => eg
                .merge_justified(
                    new,
                    class,
                    crate::union_find::Justification::Rewrite { rule_id },
                )
                .is_some(),
            _ => eg.merge(new, class).is_some(),
        };
        if merged {
            report.changed += 1;
        }
    }
    eg.rebuild();
    Ok(report)
}

fn fire_word(f: bool) -> &'static str {
    if f { "fires" } else { "does not fire" }
}

/// `collection.rs`'s verdict on a match: the environment with its `:let`s when the
/// rule fires, none when a guard fails or a reduction has no value.
fn legacy_verdict<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
>(
    cx: &Ctx<Cfg, L, M, TRACK, PROOFS>,
    r: &Rule<Cfg::O, Cfg::S, L>,
    l: &LegacyRhs,
    env: &BTreeMap<String, Value<Cfg::G, L>>,
) -> Result<Option<BTreeMap<String, Value<Cfg::G, L>>>, String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let env = match bind_lets(cx, l, env.clone()) {
        Ok(e) => e,
        Err(e) if e == EMPTY => return Ok(None),
        Err(e) => return Err(format!("{}: {e}", r.name)),
    };
    for g in &l.when {
        match eval(cx, &env, g) {
            Ok(Value::Lit(l)) if M::is_truthy(&l) => {}
            Err(e) if e != EMPTY => return Err(format!("{}: {e}", r.name)),
            _ => return Ok(None),
        }
    }
    Ok(Some(env))
}

/// A match of `collection.rs` in the layout of `Rule::seq_shape`, which the
/// relational engine fills: literals interned, multiplicities narrowed to the
/// configuration's width.
fn to_query<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>(
    eg: &mut EGraph<Cfg, L, TRACK, PROOFS>,
    r: &Rule<Cfg::O, Cfg::S, L>,
    env: &BTreeMap<String, Value<Cfg::G, L>>,
) -> Result<crate::ematch::Match<Cfg>, String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    use crate::resolve::{ColRef, RestRef};
    let shape = &r.seq_shape;
    let mut q = crate::ematch::Match::<Cfg>::new(shape);
    let seq = |n: &str| match env.get(n) {
        Some(Value::Seq(xs)) => Ok(xs.clone()),
        _ => Err(format!("'{n}' is not a sequence of the match")),
    };
    let classes = |xs: &[Value<Cfg::G, L>]| {
        xs.iter()
            .map(|x| {
                if let Value::Class(g) = x {
                    Ok(*g)
                } else {
                    Err("a class expected".to_string())
                }
            })
            .collect::<Result<Vec<_>, _>>()
    };
    let narrow = |m: u64| {
        Cfg::M::try_from_u64(m).ok_or_else(|| {
            format!("multiplicity overflow: the count {m} is beyond the configured width")
        })
    };
    let push_rest =
        |q: &mut crate::ematch::Match<Cfg>, name: &str, rr: RestRef| -> Result<(), String> {
            let gs = classes(&seq(name)?)?;
            match rr {
                RestRef::Seq(v) => q.push_seq(v, &gs),
                RestRef::Set(v) => q.push_set(v, &gs),
                RestRef::Mset(v) => {
                    let ms = seq(&mult_column(name))?;
                    let mut cs = Vec::with_capacity(gs.len());
                    for (g, m) in gs.iter().zip(&ms) {
                        let Value::Count(m) = m else {
                            return Err(format!("..{name}: a multiplicity column of non-counts"));
                        };
                        cs.push(Cfg::mset_child_with_mult(*g, narrow(*m)?));
                    }
                    q.push_mset(v, &cs);
                }
            }
            Ok(())
        };
    for f in &shape.filters {
        push_rest(&mut q, &f.name, f.elems)?;
        for (name, col) in &f.cols {
            match col {
                ColRef::Node(v) => q.push_seq(*v, &classes(&seq(name)?)?),
                ColRef::Lit(v) => {
                    let mut vs = Vec::new();
                    for x in seq(name)? {
                        let Value::Lit(l) = x else {
                            return Err(format!("'{name}': a literal column of non-literals"));
                        };
                        vs.push(eg.intern_lit(l));
                    }
                    q.push_lit_seq(*v, &vs);
                }
                ColRef::Mult(_) => {}
            }
        }
    }
    for i in &r.items {
        if let RItem::Bare(n) = i {
            let rr = if r.assoc {
                shape.find_seq(n).map(RestRef::Seq)
            } else if r.ac {
                shape.find_mset(n).map(RestRef::Mset)
            } else {
                shape.find_set(n).map(RestRef::Set)
            };
            push_rest(
                &mut q,
                n,
                rr.ok_or_else(|| format!("..{n} is not in the match layout"))?,
            )?;
        }
    }
    for n in &r.scalars {
        match env.get(n) {
            Some(Value::Class(g)) => q.set(
                shape
                    .find_var(n)
                    .ok_or_else(|| format!("'{n}' is not a node variable of the layout"))?,
                *g,
            ),
            Some(Value::Lit(l)) => {
                let v = shape
                    .find_lit_val(n)
                    .ok_or_else(|| format!("'{n}' is not a literal variable of the layout"))?;
                let l = eg.intern_lit(l.clone());
                q.set_lit_val(v, l);
            }
            Some(Value::Count(m)) => q.set_mult(
                shape
                    .find_mult(n)
                    .ok_or_else(|| format!("'{n}' is not a multiplicity of the layout"))?,
                narrow(*m)?,
            ),
            _ => return Err(format!("'{n}' is not a scalar of the match")),
        }
    }
    Ok(q)
}

impl<O: Copy, S, L> Rule<O, S, L> {
    /// The operator at the root of the rule's left-hand side.
    pub fn root_op(&self) -> O {
        self.root
    }

    /// Per filter, whether the rule cannot fire when it is empty (the `Collect` atom's
    /// non-emptiness analysis, `SeqRhs::required_nonempty`).
    pub fn filter_required(&self) -> Vec<bool> {
        self.query
            .atoms
            .iter()
            .find_map(|a| match a {
                crate::resolve::RAtom::Collect { collect, .. } => Some(collect.0.required.clone()),
                _ => None,
            })
            .unwrap_or_default()
    }

    /// The relational engine's assembly of this rule (its `Collect` atom's).
    pub fn query_assembly(&self) -> Option<std::sync::Arc<crate::seq_engine::Assembly>> {
        self.query.atoms.iter().find_map(|a| match a {
            crate::resolve::RAtom::Collect { collect, .. } => {
                Some(std::sync::Arc::clone(&collect.0.asm))
            }
            _ => None,
        })
    }

    /// Whether `collection.rs`'s own checker accepted the right-hand side, `:let`, and
    /// `:when`, so that debug builds compare its evaluation with `crate::seq_rhs`'s.
    #[doc(hidden)]
    pub fn legacy_checked(&self) -> bool {
        self.legacy.is_some()
    }
}

/// Test support: every match of `r` at node `id`, as the pass computes them, with
/// the left-hand side's bindings rendered as text: a class as `c<representative id>`,
/// a literal or a multiplicity as its value, a sequence as `[x, y]`. The differential
/// tests of `doc/goal-sequence-patterns.md` compare these with the reference
/// matcher's. A node over the match bound gives no matches.
#[doc(hidden)]
pub fn matches_at<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
>(
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    model: &M,
    globals: &GlobalCtx<Cfg::S, Cfg::G>,
    r: &Rule<Cfg::O, Cfg::S, L>,
    id: Cfg::G,
) -> Vec<BTreeMap<String, String>>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let mut members: BTreeMap<usize, Vec<Cfg::G>> = BTreeMap::new();
    for n in eg.node_ids() {
        members
            .entry(eg.class_repr(n).to_usize())
            .or_default()
            .push(n);
    }
    for v in members.values_mut() {
        v.sort_by_key(|n| n.to_usize());
    }
    let view = View { members };
    let cx = Ctx {
        eg,
        model,
        view: &view,
        globals,
    };
    fn render<G: DenseId, L: LitVal>(v: &Value<G, L>) -> String {
        match v {
            Value::Class(c) => format!("c{}", c.to_usize()),
            Value::Lit(l) => l.to_string(),
            Value::Count(n) => n.to_string(),
            Value::Seq(s) => format!("[{}]", s.iter().map(render).collect::<Vec<_>>().join(", ")),
            Value::Tuples(t) => format!("{t:?}"),
        }
    }
    let rhs: Vec<&String> = r.rhs_globals.iter().map(|(n, _)| n).collect();
    match_root(&cx, r, id)
        .unwrap_or_default()
        .into_iter()
        .map(|m| {
            m.env
                .iter()
                .filter(|(k, _)| !rhs.contains(k))
                .map(|(k, v)| (k.clone(), render(v)))
                .collect()
        })
        .collect()
}

/// The matches of a rule at one root node, as `doc/sequence-patterns.md` defines them
/// (`crate::seq_collect::assemble`), each with its root's class and the globals the
/// right-hand side names.
fn match_root<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
>(
    cx: &Ctx<Cfg, L, M, TRACK, PROOFS>,
    r: &Rule<Cfg::O, Cfg::S, L>,
    id: Cfg::G,
) -> Result<Vec<Match<Cfg::G, L>>, String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let envs = if r.flatten {
        // The same views the relational engine reads, from the live graph.
        let kind = crate::flatten::FlatKind::of(r.spec.assoc, r.spec.ac);
        let views = crate::flatten::views_u64(cx, id, r.root, kind)?;
        crate::seq_collect::assemble_views(&r.spec, &mut Live { cx, r }, &views)?
    } else {
        let kids = cx.children(id)?;
        crate::seq_collect::assemble(&r.spec, &mut Live { cx, r }, &kids)?
    };
    let class = cx.eg.class_repr(id);
    Ok(envs
        .into_iter()
        .map(|mut env| {
            for (name, gid) in &r.rhs_globals {
                env.insert(name.clone(), cx.global(*gid));
            }
            Match { class, env }
        })
        .collect())
}

/// Route 1's view of the live graph for `:flatten` (`crate::flatten::Members`): a
/// class's members as the pass listed them, a node's operator when it is live, and its
/// children canonical by the live representatives.
impl<Cfg: EGraphConfig, L: LitVal, M: LitModel<Value = L>, const TRACK: bool, const PROOFS: bool>
    crate::flatten::Members<Cfg::G, Cfg::O, Cfg::M> for Ctx<'_, Cfg, L, M, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    fn members(&self, class: Cfg::G) -> &[Cfg::G] {
        Ctx::members(self, class)
    }

    fn op(&self, node: Cfg::G) -> Option<Cfg::O> {
        self.live(node).then(|| self.eg.node_op(node))
    }

    fn children(
        &self,
        node: Cfg::G,
        kind: crate::flatten::FlatKind,
        kids: &mut Vec<(Cfg::G, Cfg::M)>,
        ids: &mut Vec<Cfg::G>,
    ) {
        crate::flatten::read_children(self.eg, node, kind, kids, ids);
        for k in kids.iter_mut() {
            k.0 = self.eg.class_repr(k.0);
        }
    }

    fn laws(&self, op: Cfg::O) -> crate::nary_canon::NaryLaws<Cfg::G, Cfg::O> {
        self.eg.nary_laws(op)
    }

    fn inverse_class(&self, inv: Cfg::O, x: Cfg::G) -> Option<Cfg::G> {
        self.eg.inverse_class(inv, x)
    }
}

/// Route 1's rows: each item's pattern matched against the live e-graph.
struct Live<
    'c,
    'a,
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
> where
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    cx: &'c Ctx<'a, Cfg, L, M, TRACK, PROOFS>,
    r: &'c Rule<Cfg::O, Cfg::S, L>,
}

impl<Cfg: EGraphConfig, L: LitVal, M: LitModel<Value = L>, const TRACK: bool, const PROOFS: bool>
    crate::seq_collect::Source<Cfg::G, L> for Live<'_, '_, Cfg, L, M, TRACK, PROOFS>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    fn one(
        &mut self,
        item: usize,
        class: Cfg::G,
        scalars: &Slots<Cfg::G, L>,
    ) -> Result<Vec<Slots<Cfg::G, L>>, String> {
        let p = self
            .r
            .items
            .iter()
            .filter_map(|i| {
                if let RItem::One(p, _) = i {
                    Some(p)
                } else {
                    None
                }
            })
            .nth(item)
            .ok_or("internal: no such simple item")?;
        self.cx.match_all(p, class, scalars)
    }
    fn filter(
        &mut self,
        fi: usize,
        class: Cfg::G,
        init: &Slots<Cfg::G, L>,
    ) -> Result<Vec<Slots<Cfg::G, L>>, String> {
        self.cx.match_all(&self.r.filters[fi].pat, class, init)
    }
}

/// A multiplicity as the `i64` literal a rule reads it as.
fn mult_lit<M: LitModel>(model: &M, m: u64) -> Result<M::Value, String> {
    let m = i64::try_from(m)
        .map_err(|_| format!("multiplicity overflow: the count {m} is beyond i64"))?;
    int(model, m)
}

/// Measurement only (`SEMPER_COLLECTION_STATS=FILE`): for one node, how many children
/// each filter's pattern matches on its own (`M_i`), how many children match two or
/// more (the overlap), and the base-2 logarithms of the matches an enumerating
/// semantics would produce: the product over children of the filters each matches
/// (partitions), and of the members matching each filter (member choices). One JSON
/// line per rule and node; matching itself is unchanged. A node whose children
/// cannot be read is not recorded.
fn record_overlap<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
>(
    cx: &Ctx<Cfg, L, M, TRACK, PROOFS>,
    r: &Rule<Cfg::O, Cfg::S, L>,
    id: Cfg::G,
    path: &std::ffi::OsStr,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    use std::io::Write;
    let Ok(kids) = cx.children(id) else { return };
    let mut sizes = vec![0usize; r.filters.len()];
    let (mut n, mut overlap, mut max_colls, mut max_members) = (0usize, 0usize, 0usize, 0usize);
    let (mut log_parts, mut log_members) = (0f64, 0f64);
    for (k, _) in kids {
        n += 1;
        let mut hit = 0usize;
        for (ci, c) in r.filters.iter().enumerate() {
            // The filter's rows on the child: one per distinct binding of a matching
            // member, which is what the enumeration multiplies by.
            let matching = cx
                .match_all(&c.pat, k, &vec![None; c.vars.len()])
                .map(|rows| dedup_slots(rows).len())
                .unwrap_or(0);
            if matching > 0 {
                hit += 1;
                sizes[ci] += 1;
                // A logarithm for the report, where the rounding of the count is immaterial.
                log_members += (matching as f64).log2();
                max_members = max_members.max(matching);
            }
        }
        if hit >= 2 {
            overlap += 1;
        }
        if hit >= 1 {
            log_parts += (hit as f64).log2();
        }
        max_colls = max_colls.max(hit);
    }
    if sizes.iter().all(|&s| s == 0) {
        return;
    }
    let line = format!(
        "{{\"rule\":\"{}\",\"node\":{},\"children\":{n},\"sizes\":{:?},\"overlap\":{overlap},\"max_colls\":{max_colls},\"log2_partitions\":{log_parts:.3},\"max_members\":{max_members},\"log2_member_choices\":{log_members:.3}}}\n",
        r.name,
        id.to_usize(),
        sizes
    );
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        let _ = f.write_all(line.as_bytes());
    }
}

fn bind_lets<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
>(
    cx: &Ctx<Cfg, L, M, TRACK, PROOFS>,
    l: &LegacyRhs,
    mut env: BTreeMap<String, Value<Cfg::G, L>>,
) -> Result<BTreeMap<String, Value<Cfg::G, L>>, String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    for (n, e) in &l.lets {
        let v = eval(cx, &env, e)?;
        env.insert(n.clone(), v);
    }
    Ok(env)
}

/// The error of `min` or `max` over an empty sequence, which has no value: the rule
/// does not fire on that node.
const EMPTY: &str = "a reduction over an empty sequence";

/// A right-hand side with no value ("§Edge cases 1"): an A application of no
/// children, or an AC or ACI one without an identity. The rule does not fire.
const NO_VALUE: &str = "a right-hand side with no value";

// ── Evaluation ───────────────────────────────────────────────────────────────

/// An `i64` literal, built through the model's reader for the sort.
fn int<M: LitModel>(model: &M, x: i64) -> Result<M::Value, String> {
    model
        .parse_as("i64", &x.to_string())
        .ok_or_else(|| "the model has no i64 sort".to_string())
}

/// A scalar primitive by surface name, resolved by the sort of its first argument.
fn apply_prim<M: LitModel>(model: &M, op: &str, args: &[&M::Value]) -> Result<M::Value, String> {
    let sort = args.first().map(|a| M::sort_of(a)).unwrap_or("");
    let d = model
        .find_op(&format!("{sort}::{op}"))
        .or_else(|| model.find_op(op))
        .ok_or_else(|| format!("no primitive '{op}' on {sort}"))?;
    (d.eval)(args).ok_or_else(|| {
        format!(
            "{op} is undefined on ({})",
            args.iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    })
}

/// Evaluate an expression that builds no term.
fn eval<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
>(
    cx: &Ctx<Cfg, L, M, TRACK, PROOFS>,
    env: &BTreeMap<String, Value<Cfg::G, L>>,
    e: &CExpr,
) -> Result<Value<Cfg::G, L>, String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let is_term = |op: &str| cx.eg.op(op).is_some_and(|o| is_term_op(cx.eg, o));
    scalar_eval(cx.model, env, e, &is_term, &|_| false, &mut |_, _| {
        Err("a term in a guard or :let".into())
    })
}

type Builder<'b, G, L> = dyn FnMut(&str, Vec<Value<G, L>>) -> Result<Value<G, L>, String> + 'b;

/// Evaluate `e`; a term is handed to `term` with its evaluated children. `repeats`
/// says whether an operator keeps copies (A and AC), so that splicing an AC sequence
/// under it repeats each child by its multiplicity ("§Edge cases 3").
fn scalar_eval<G: Copy + PartialEq + std::fmt::Debug, L: LitVal, M: LitModel<Value = L>>(
    model: &M,
    env: &BTreeMap<String, Value<G, L>>,
    e: &CExpr,
    is_term: &dyn Fn(&str) -> bool,
    repeats: &dyn Fn(&str) -> bool,
    term: &mut Builder<'_, G, L>,
) -> Result<Value<G, L>, String> {
    match e {
        CExpr::Lit(t, _) => {
            let t2 = t.trim_matches('"');
            let v = if t.starts_with('"') {
                model.parse_as("String", t2)
            } else {
                model.parse_any(t).map(|(_, v)| v)
            };
            v.map(Value::Lit)
                .ok_or_else(|| format!("cannot read literal '{t}'"))
        }
        CExpr::Var(n, _) => as_scalar(model, env.get(n).ok_or_else(|| format!("unbound '{n}'"))?),
        CExpr::App { op, children, .. } => {
            let op = op.as_str();
            let exprs: Vec<&CExpr> = children
                .iter()
                .filter_map(|c| {
                    if let CChild::Expr(e) = c {
                        Some(e)
                    } else {
                        None
                    }
                })
                .collect();
            if REDUCTIONS.contains(&op) {
                let v = scalar_eval(model, env, exprs[0], is_term, repeats, term)?;
                let items: Vec<Value<G, L>> = match v {
                    Value::Seq(s) => s,
                    Value::Tuples(t) => t.into_iter().map(Value::Seq).collect(),
                    _ => return Err(format!("'{op}' reduces a sequence")),
                };
                if op == "count" {
                    let n = i64::try_from(items.len())
                        .map_err(|_| "multiplicity overflow: a count beyond i64".to_string())?;
                    return int(model, n).map(Value::Lit);
                }
                let mut acc: Option<L> = None;
                for it in items {
                    let Value::Lit(x) = it else {
                        return Err(format!("'{op}' reduces literals"));
                    };
                    acc = Some(match acc {
                        None => x,
                        Some(a) => {
                            apply_prim(model, if op == "sum" { "+" } else { op }, &[&a, &x])?
                        }
                    });
                }
                return match acc {
                    Some(a) => Ok(Value::Lit(a)),
                    None if op == "sum" => int(model, 0).map(Value::Lit),
                    None => Err(EMPTY.into()),
                };
            }
            if seq_primitive_sig(op).is_some() {
                let args = exprs
                    .iter()
                    .map(|a| scalar_eval(model, env, a, is_term, repeats, term))
                    .collect::<Result<Vec<_>, _>>()?;
                return seq_primitive(model, op, &args).map(Value::Tuples);
            }
            if op == "if" {
                let c = scalar_eval(model, env, exprs[0], is_term, repeats, term)?;
                let Value::Lit(c) = c else {
                    return Err("if: a literal condition".into());
                };
                return scalar_eval(
                    model,
                    env,
                    if M::is_truthy(&c) { exprs[1] } else { exprs[2] },
                    is_term,
                    repeats,
                    term,
                );
            }
            if is_term(op) {
                // A term: children in order, splices and comprehensions expanded.
                let mut kids = Vec::new();
                for c in children {
                    match c {
                        CChild::Expr(e) => {
                            kids.push(scalar_eval(model, env, e, is_term, repeats, term)?)
                        }
                        CChild::Splice(n, _) => {
                            let Some(Value::Seq(s)) = env.get(n) else {
                                return Err(format!("..{n} is not a sequence"));
                            };
                            // An AC sequence under an operator that keeps copies: each
                            // child repeated by its multiplicity.
                            match env.get(&mult_column(n)) {
                                Some(Value::Seq(ms)) if repeats(op) => {
                                    for (x, m) in s.iter().zip(ms) {
                                        let Value::Count(m) = m else {
                                            return Err(format!(
                                                "..{n}: a multiplicity column of non-counts"
                                            ));
                                        };
                                        let m = usize::try_from(*m).map_err(|_| {
                                            format!(
                                                "..{n}: multiplicity overflow: a count beyond usize"
                                            )
                                        })?;
                                        for _ in 0..m {
                                            kids.push(x.clone());
                                        }
                                    }
                                }
                                _ => kids.extend(s.iter().cloned()),
                            }
                        }
                        CChild::Comp {
                            body, vars, source, ..
                        } => {
                            let rows: Vec<Vec<Value<G, L>>> =
                                match scalar_eval(model, env, source, is_term, repeats, term)? {
                                    Value::Tuples(t) => t,
                                    Value::Seq(s) => s.into_iter().map(|x| vec![x]).collect(),
                                    _ => return Err("a comprehension over a scalar".into()),
                                };
                            for row in rows {
                                let mut inner = env.clone();
                                for (v, x) in vars.iter().zip(row) {
                                    inner.insert(v.clone(), x);
                                }
                                kids.push(scalar_eval(
                                    model, &inner, body, is_term, repeats, term,
                                )?);
                            }
                        }
                    }
                }
                return term(op, kids);
            }
            // A scalar primitive, element-wise over sequences.
            let args = exprs
                .iter()
                .map(|a| scalar_eval(model, env, a, is_term, repeats, term))
                .collect::<Result<Vec<_>, _>>()?;
            let len = args.iter().find_map(|a| {
                if let Value::Seq(s) = a {
                    Some(s.len())
                } else {
                    None
                }
            });
            let at = |a: &Value<G, L>, i: usize| -> Result<L, String> {
                match a {
                    Value::Lit(l) => Ok(l.clone()),
                    Value::Seq(s) => match s.get(i) {
                        Some(Value::Lit(l)) => Ok(l.clone()),
                        Some(_) => Err(format!("'{op}' on a class")),
                        None => Err(format!("'{op}' over sequences of different lengths")),
                    },
                    _ => Err(format!("'{op}' on a class")),
                }
            };
            match len {
                None => {
                    let ls = (0..args.len())
                        .map(|j| at(&args[j], 0))
                        .collect::<Result<Vec<_>, _>>()?;
                    apply_prim(model, op, &ls.iter().collect::<Vec<_>>()).map(Value::Lit)
                }
                Some(n) => {
                    let mut out = Vec::with_capacity(n);
                    for i in 0..n {
                        let ls = (0..args.len())
                            .map(|j| at(&args[j], i))
                            .collect::<Result<Vec<_>, _>>()?;
                        out.push(Value::Lit(apply_prim(
                            model,
                            op,
                            &ls.iter().collect::<Vec<_>>(),
                        )?));
                    }
                    Ok(Value::Seq(out))
                }
            }
        }
    }
}

/// A named value as an expression reads it: a multiplicity as its `i64` literal.
fn as_scalar<G: Clone, L: Clone, M: LitModel<Value = L>>(
    model: &M,
    v: &Value<G, L>,
) -> Result<Value<G, L>, String> {
    Ok(match v {
        Value::Count(m) => Value::Lit(mult_lit(model, *m)?),
        Value::Seq(xs) => Value::Seq(
            xs.iter()
                .map(|x| as_scalar(model, x))
                .collect::<Result<_, _>>()?,
        ),
        Value::Tuples(rows) => Value::Tuples(
            rows.iter()
                .map(|r| {
                    r.iter()
                        .map(|x| as_scalar(model, x))
                        .collect::<Result<_, _>>()
                })
                .collect::<Result<_, _>>()?,
        ),
        other => other.clone(),
    })
}

/// Build a right-hand side into the graph.
fn build<
    Cfg: EGraphConfig,
    L: LitVal,
    M: LitModel<Value = L>,
    const TRACK: bool,
    const PROOFS: bool,
>(
    eg: &mut EGraph<Cfg, L, TRACK, PROOFS>,
    model: &M,
    env: &BTreeMap<String, Value<Cfg::G, L>>,
    e: &CExpr,
) -> Result<Value<Cfg::G, L>, String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let (terms, repeating): (
        std::collections::BTreeSet<String>,
        std::collections::BTreeSet<String>,
    ) = {
        let mut ops = Vec::new();
        app_ops(e, &mut ops);
        let terms: std::collections::BTreeSet<String> = ops
            .iter()
            .filter(|op| eg.op(op).is_some_and(|o| is_term_op(eg, o)))
            .cloned()
            .collect();
        let repeating = ops
            .iter()
            .filter(|op| {
                eg.op(op).is_some_and(|o| {
                    matches!(
                        eg.ops().info(o).kind,
                        OpKind::A { .. } | OpKind::MSet { .. }
                    )
                })
            })
            .cloned()
            .collect();
        (terms, repeating)
    };
    let is_term = |op: &str| terms.contains(op);
    let repeats = |op: &str| repeating.contains(op);
    let mut term = |op: &str, kids: Vec<Value<Cfg::G, L>>| -> Result<Value<Cfg::G, L>, String> {
        let o = eg
            .op(op)
            .ok_or_else(|| format!("unknown operator '{op}'"))?;
        let kind = eg.ops().info(o).kind.clone();
        let arg_sort = |i: usize| match &kind {
            OpKind::Normal { arg_sorts } => arg_sorts.get(i).copied(),
            _ => None,
        };
        let mut ids = Vec::with_capacity(kids.len());
        for (i, k) in kids.into_iter().enumerate() {
            ids.push(match k {
                Value::Class(c) => c,
                Value::Lit(l) => {
                    let sort =
                        arg_sort(i).ok_or_else(|| format!("a literal argument to '{op}'"))?;
                    let lit_op = eg
                        .ops()
                        .lit_op_for_sort(sort)
                        .ok_or_else(|| format!("argument {i} of '{op}' is not a literal sort"))?;
                    let v = eg.intern_lit(l);
                    eg.add_lit(lit_op, v)
                }
                _ => return Err(format!("a sequence as an argument to '{op}'")),
            });
        }
        // The unit law: an AC or ACI application of one child is the child.
        if matches!(kind, OpKind::Set { .. } | OpKind::MSet { .. }) && ids.len() == 1 {
            return Ok(Value::Class(ids[0]));
        }
        // "§Edge cases 1": an A application of no children, or an AC or ACI one
        // without an identity, has no value; the e-graph refuses to build either.
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
        if ids.is_empty()
            && matches!(
                kind,
                OpKind::A { .. } | OpKind::Set { .. } | OpKind::MSet { .. }
            )
            && !empty_ok
        {
            return Err(NO_VALUE.into());
        }
        Ok(Value::Class(eg.add(o, &ids)))
    };
    scalar_eval(model, env, e, &is_term, &repeats, &mut term)
}

fn app_ops(e: &CExpr, out: &mut Vec<String>) {
    if let CExpr::App { op, children, .. } = e {
        out.push(op.clone());
        for c in children {
            match c {
                CChild::Expr(e) => app_ops(e, out),
                CChild::Splice(..) => {}
                CChild::Comp { body, source, .. } => {
                    app_ops(body, out);
                    app_ops(source, out);
                }
            }
        }
    }
}

// ── Sequence primitives ──────────────────────────────────────────────────────

/// Integer comparisons and arithmetic on literals, through the model's primitives:
/// the literal type is opaque to this module, and the model's checked arithmetic
/// reports an overflow as an undefined primitive rather than wrapping.
struct Ints<'m, M: LitModel> {
    model: &'m M,
    one: M::Value,
}

impl<'m, M: LitModel> Ints<'m, M> {
    fn new(model: &'m M) -> Result<Self, String> {
        Ok(Ints {
            model,
            one: int(model, 1)?,
        })
    }
    fn le(&self, a: &M::Value, b: &M::Value) -> Result<bool, String> {
        apply_prim(self.model, "<=", &[a, b]).map(|v| M::is_truthy(&v))
    }
    fn lt(&self, a: &M::Value, b: &M::Value) -> Result<bool, String> {
        apply_prim(self.model, "<", &[a, b]).map(|v| M::is_truthy(&v))
    }
    fn succ(&self, a: &M::Value) -> Result<M::Value, String> {
        apply_prim(self.model, "+", &[a, &self.one])
    }
    fn pred(&self, a: &M::Value) -> Result<M::Value, String> {
        apply_prim(self.model, "-", &[a, &self.one])
    }
    fn max(&self, a: &M::Value, b: &M::Value) -> Result<M::Value, String> {
        Ok(if self.le(a, b)? { b.clone() } else { a.clone() })
    }
    fn min(&self, a: &M::Value, b: &M::Value) -> Result<M::Value, String> {
        Ok(if self.le(a, b)? { a.clone() } else { b.clone() })
    }

    /// Unions of closed integer windows into maximal runs; `[0,3]` and `[4,6]` join.
    /// Windows are ordered by lower then upper bound (an insertion sort: the
    /// comparison can fail, and the groups are small).
    fn union(&self, w: Vec<(M::Value, M::Value)>) -> Result<Vec<(M::Value, M::Value)>, String> {
        let mut sorted: Vec<(M::Value, M::Value)> = Vec::with_capacity(w.len());
        for x in w {
            let mut at = sorted.len();
            for (i, y) in sorted.iter().enumerate() {
                let before =
                    self.lt(&x.0, &y.0)? || (!self.lt(&y.0, &x.0)? && self.lt(&x.1, &y.1)?);
                if before {
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

/// The registered sequence primitives.
///
/// - `(union-by p l u)`: the windows `[l, u]` grouped by the class `p`, each group
///   unioned into maximal runs, as `(p a b)` tuples.
/// - `(narrow c d r a b q)`: each window `[c, d]` over class `r`, narrowed against
///   the union of the windows `[a, b]` whose class `q` is `r`, as `(r c' d')`
///   tuples. A window covering the start pushes it past its end; one covering the
///   end pulls it before its start; repeated to a fixpoint. A window narrowed to
///   nothing is returned unchanged.
/// - `(narrowed c d r a b q)`: the tuples of `narrow` whose window changed.
/// - `(zip x y ...)`: parallel sequences as tuples, stopping at the shortest
///   (`doc/sequence-patterns.md`, "Multiplicities and `zip`").
fn seq_primitive<G: Copy + PartialEq + std::fmt::Debug, L: LitVal, M: LitModel<Value = L>>(
    model: &M,
    op: &str,
    args: &[Value<G, L>],
) -> Result<Vec<Vec<Value<G, L>>>, String> {
    let seq = |i: usize| -> Result<&Vec<Value<G, L>>, String> {
        match &args[i] {
            Value::Seq(s) => Ok(s),
            _ => Err(format!("'{op}' takes sequences")),
        }
    };
    let lits = |i: usize| -> Result<Vec<L>, String> {
        seq(i)?
            .iter()
            .map(|v| {
                if let Value::Lit(l) = v {
                    Ok(l.clone())
                } else {
                    Err(format!("'{op}': a class where an integer is expected"))
                }
            })
            .collect()
    };
    let classes = |i: usize| -> Result<Vec<G>, String> {
        seq(i)?
            .iter()
            .map(|v| {
                if let Value::Class(c) = v {
                    Ok(*c)
                } else {
                    Err(format!("'{op}': an integer where a class is expected"))
                }
            })
            .collect()
    };
    let same_len = |xs: &[usize]| -> Result<usize, String> {
        let n = xs.first().copied().unwrap_or(0);
        if xs.iter().any(|&m| m != n) {
            return Err(format!("'{op}': columns of different lengths"));
        }
        Ok(n)
    };
    match op {
        "zip" => {
            let mut cols = Vec::with_capacity(args.len());
            for i in 0..args.len() {
                cols.push(seq(i)?);
            }
            let n = cols.iter().map(|c| c.len()).min().unwrap_or(0);
            Ok((0..n)
                .map(|j| cols.iter().map(|c| c[j].clone()).collect())
                .collect())
        }
        "union-by" => {
            let ints = Ints::new(model)?;
            let (p, l, u) = (classes(0)?, lits(1)?, lits(2)?);
            same_len(&[p.len(), l.len(), u.len()])?;
            let mut groups: Vec<(G, Vec<(L, L)>)> = Vec::new();
            for i in 0..p.len() {
                match groups.iter_mut().find(|(g, _)| *g == p[i]) {
                    Some((_, w)) => w.push((l[i].clone(), u[i].clone())),
                    None => groups.push((p[i], vec![(l[i].clone(), u[i].clone())])),
                }
            }
            let mut out = Vec::new();
            for (g, w) in groups {
                for (a, b) in ints.union(w)? {
                    out.push(vec![Value::Class(g), Value::Lit(a), Value::Lit(b)]);
                }
            }
            Ok(out)
        }
        "narrow" | "narrowed" => {
            let ints = Ints::new(model)?;
            let (c, d, r) = (lits(0)?, lits(1)?, classes(2)?);
            let (a, b, q) = (lits(3)?, lits(4)?, classes(5)?);
            same_len(&[c.len(), d.len(), r.len()])?;
            same_len(&[a.len(), b.len(), q.len()])?;
            let mut out = Vec::new();
            for i in 0..c.len() {
                let windows = ints.union(
                    (0..q.len())
                        .filter(|&j| q[j] == r[i])
                        .map(|j| (a[j].clone(), b[j].clone()))
                        .collect(),
                )?;
                let (mut lo, mut hi) = (c[i].clone(), d[i].clone());
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
                    (c[i].clone(), d[i].clone())
                };
                if op == "narrow" || lo != c[i] || hi != d[i] {
                    out.push(vec![Value::Class(r[i]), Value::Lit(lo), Value::Lit(hi)]);
                }
            }
            Ok(out)
        }
        _ => Err(format!("no sequence primitive '{op}'")),
    }
}
