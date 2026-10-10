// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The filter sub-queries of a sequence pattern (Semper design §7.6,
//! "Relational formulation" and "Plans").
//!
//! A filter `(..gs base)` defines the relation `F(c, m, ȳ)`: member `m` of class `c`
//! matches `base` with bindings `ȳ`. `base` is an ordinary pattern, so `F` is an
//! ordinary conjunctive query with a distinguished root variable, resolved to a
//! `ResolvedQuery` and run by the leapfrog join. It has two plans: the bound-root
//! plan, scheduled with the root bound, which probes one class; and the free-root
//! plan, scheduled by selectivity with nothing bound, which lists every row of the
//! round and may start anywhere in the pattern.
//!
//! Rows are deduplicated by their bindings, not by member (`doc/sequence-patterns.md`,
//! Edge cases 2): the right-hand side reads only bindings.

use crate::ast::{LitValVarId, VarId};
use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::ematch::{MatchPool, MatchView};
use crate::index::VariantIndex;
use crate::lit_model::LitModel;
use crate::literal::LitVal;
use crate::registry::{OpRegistry, SortRegistry};
use crate::resolve::{GlobalCtx, MatchShape, RAtom, ResolvedQuery};
use crate::schedule::{IndexStats, QueryPlan};
use crate::surface_ast::SurfacePattern;
use std::hash::Hash;

/// Where a filter's pattern variable is bound in its sub-query.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SubVar {
    /// A class: the variable's node binding, canonicalized against the snapshot.
    Node(VarId),
    /// A literal value.
    Lit(LitValVarId),
}

/// One filter's sub-query, resolved at check time.
#[derive(Clone, Debug)]
pub struct SubQuery<O, S, L> {
    pub query: ResolvedQuery<O, S, L>,
    /// The distinguished root: the member (or, for a variable base, the class)
    /// matching `base`.
    pub root: VarId,
    /// The filter's pattern variables, in `collection::Filter::vars` order.
    pub vars: Vec<(String, SubVar)>,
    /// The base is a variable of a non-literal sort: every class matches it, so its
    /// rows are not a relation a plan can list, and only the probe path serves it.
    pub every_class: bool,
}

/// A sub-query's two plans, scheduled against a round's statistics.
#[derive(Clone, Debug)]
pub struct FilterPlans<O, I, L> {
    pub root: VarId,
    pub vars: Vec<SubVar>,
    /// Scheduled with `root` bound; run from a seed binding `root := class`.
    pub bound: QueryPlan<O, I, L>,
    /// Scheduled with nothing bound; `None` when every class matches
    /// (`SubQuery::every_class`).
    pub free: Option<QueryPlan<O, I, L>>,
}

/// One row of a filter at a class: the matching member and the bindings, one per
/// entry of `FilterQuery::vars`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row<G, V> {
    pub member: G,
    pub vals: Vec<RowVal<G, V>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowVal<G, V> {
    Class(G),
    Lit(V),
}

/// Resolve `base`, a filter's pattern over children of sort `child_sort`, as an
/// ordinary query with a distinguished root. `vars` are the filter's variable names
/// in the order the rows report them.
pub fn sub_query<O, S, L, M, const TRACK: bool>(
    base: &SurfacePattern,
    child_sort: S,
    vars: &[String],
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    model: &M,
    globals: &GlobalCtx<S>,
) -> Result<SubQuery<O, S, L>, String>
where
    O: DenseId + Hash + Copy,
    S: DenseId + Copy,
    L: LitVal,
    M: LitModel<Value = L>,
{
    let (query, root, every_class) = root_query(base, child_sort, ops, sorts, model, globals)?;
    let mut out = Vec::with_capacity(vars.len());
    for v in vars {
        let sv = match (query.shape.find_var(v), query.shape.find_lit_val(v)) {
            (_, Some(l)) => SubVar::Lit(l),
            (Some(n), None) => SubVar::Node(n),
            (None, None) => {
                return Err(format!(
                    "the filter variable '{v}' is not bound by its sub-query"
                ));
            }
        };
        out.push((v.clone(), sv));
    }
    Ok(SubQuery {
        query,
        root,
        vars: out,
        every_class,
    })
}

impl<O: DenseId + Hash + Copy, S: DenseId + Copy, L: Clone> SubQuery<O, S, L> {
    /// The bound-root and free-root plans, priced with `stats`.
    pub fn plans<I: crate::containers::IndexLike>(
        &self,
        stats: &IndexStats<O>,
    ) -> FilterPlans<O, I, L> {
        FilterPlans {
            root: self.root,
            vars: self.vars.iter().map(|(_, v)| *v).collect(),
            bound: crate::schedule::schedule_with_bound(&self.query, stats, &[self.root]),
            free: (!self.every_class)
                .then(|| crate::schedule::schedule_with_stats(&self.query, stats)),
        }
    }
}

/// The sub-query of `base`, its root, and whether every class matches it.
fn root_query<O, S, L, M, const TRACK: bool>(
    base: &SurfacePattern,
    child_sort: S,
    ops: &OpRegistry<O, S, TRACK>,
    sorts: &SortRegistry<S, TRACK>,
    model: &M,
    globals: &GlobalCtx<S>,
) -> Result<(ResolvedQuery<O, S, L>, VarId, bool), String>
where
    O: DenseId + Hash + Copy,
    S: DenseId + Copy,
    L: LitVal,
    M: LitModel<Value = L>,
{
    // A variable or a global flattens to no atom, which `resolve` has no root for;
    // those bases are built here, the rest flatten and resolve as a rule body does.
    if let SurfacePattern::Var(name, _) = base {
        let mut shape = MatchShape::default();
        let mut atoms = Vec::new();
        let (root, every_class) = if let Some((gid, _, _)) = globals.get(name) {
            let root = shape.intern_var("?filter")?;
            atoms.push(RAtom::EqGlobal(root, gid));
            (root, false)
        } else if let Some(lit_op) = ops.lit_op_for_sort(child_sort) {
            let root = shape.intern_var("?filter")?;
            let val = shape.intern_lit_val(name)?;
            atoms.push(RAtom::LitBind {
                node: root,
                op: lit_op,
                val,
            });
            (root, false)
        } else {
            (shape.intern_var(name)?, true)
        };
        let var_sorts = vec![Some(child_sort); shape.num_vars()];
        let query = ResolvedQuery {
            atoms,
            shape,
            var_sorts,
            seq_sorts: Vec::new(),
            set_sorts: Vec::new(),
            mset_sorts: Vec::new(),
            mult_intervals: Vec::new(),
            flatten: false,
        };
        return Ok((query, root, every_class));
    }
    let fq = crate::sortcheck::flatten_surface(std::slice::from_ref(base), ops)?;
    let root_name = fq
        .root_vars
        .first()
        .ok_or("a filter's pattern flattened to no root")?
        .clone();
    let query: ResolvedQuery<O, S, L> =
        crate::resolve::resolve(&fq, ops, sorts, model, globals).map_err(|e| e.to_string())?;
    let root = query
        .shape
        .find_var(&root_name)
        .ok_or_else(|| format!("a filter's pattern has no root variable '{root_name}'"))?;
    Ok((query, root, false))
}

impl<O, I, L> FilterPlans<O, I, L> {
    /// The rows of the filter at `class`, by the bound-root plan: one per distinct
    /// binding. `class` is a snapshot representative.
    pub fn probe<Cfg, SG: Copy, const T: bool, const P: bool>(
        &self,
        eg: &EGraph<Cfg, L, T, P>,
        index: &VariantIndex<'_, Cfg>,
        globals: &GlobalCtx<SG, Cfg::G>,
        pool: &mut MatchPool<Cfg>,
        class: Cfg::G,
    ) -> Vec<Row<Cfg::G, Cfg::V>>
    where
        Cfg: EGraphConfig<O = O, Index = I>,
        L: LitVal,
        MSetCanon: VarCanon<Cfg::G, Cfg::C>,
        Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
    {
        crate::ematch::run_query_seeded_into(
            &self.bound,
            eg,
            index,
            globals,
            pool,
            &[(self.root, class)],
        );
        let mut out: Vec<Row<Cfg::G, Cfg::V>> = Vec::with_capacity(pool.len());
        for j in 0..pool.len() {
            let row = self.row(eg, index, &pool.row(j));
            if !out.iter().any(|r| r.vals == row.vals) {
                out.push(row);
            }
        }
        out
    }

    /// Every row of the round, by the free-root plan, each with its member's class
    /// (a snapshot representative) and deduplicated by class and binding. `None` when
    /// every class matches (`SubQuery::every_class`).
    pub fn all<Cfg, SG: Copy, const T: bool, const P: bool>(
        &self,
        eg: &EGraph<Cfg, L, T, P>,
        index: &VariantIndex<'_, Cfg>,
        globals: &GlobalCtx<SG, Cfg::G>,
        pool: &mut MatchPool<Cfg>,
    ) -> Option<Vec<(Cfg::G, Row<Cfg::G, Cfg::V>)>>
    where
        Cfg: EGraphConfig<O = O, Index = I>,
        L: LitVal,
        MSetCanon: VarCanon<Cfg::G, Cfg::C>,
        Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
    {
        let plan = self.free.as_ref()?;
        crate::ematch::run_query_into(plan, eg, index, globals, pool);
        let mut out: Vec<(Cfg::G, Row<Cfg::G, Cfg::V>)> = Vec::with_capacity(pool.len());
        for j in 0..pool.len() {
            let row = self.row(eg, index, &pool.row(j));
            let class = crate::ematch::round_canon(index, eg, row.member);
            if !out.iter().any(|(c, r)| *c == class && r.vals == row.vals) {
                out.push((class, row));
            }
        }
        Some(out)
    }

    fn row<Cfg, const T: bool, const P: bool>(
        &self,
        eg: &EGraph<Cfg, L, T, P>,
        index: &VariantIndex<'_, Cfg>,
        m: &dyn MatchView<Cfg>,
    ) -> Row<Cfg::G, Cfg::V>
    where
        Cfg: EGraphConfig<O = O, Index = I>,
        L: LitVal,
        MSetCanon: VarCanon<Cfg::G, Cfg::C>,
        Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
    {
        let vals = self
            .vars
            .iter()
            .map(|sv| match *sv {
                SubVar::Node(v) => RowVal::Class(crate::ematch::round_canon(index, eg, m.get(v))),
                SubVar::Lit(v) => RowVal::Lit(m.get_lit_val(v)),
            })
            .collect();
        Row {
            member: m.get(self.root),
            vals,
        }
    }
}
