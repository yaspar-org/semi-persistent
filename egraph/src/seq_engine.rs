// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Sequence patterns in the relational matcher (Semper design §7.6): the
//! `Collect` atom's payload, its plan, the step that assembles a node's matches from
//! its children's filter rows on the round's snapshot, and the application of a
//! sequence rule's matches.
//!
//! The outer query of a sequence rule is `Join n ← ByOp(root); Collect(n)`. `Collect`
//! reads `n`'s children through the snapshot (`ematch::round_canon`), probes each
//! item's sub-query at each child (the bound-root plans of `crate::seq_query`),
//! assembles the matches (`crate::seq_collect::assemble`, the code route 1 runs
//! too), and writes each into the match's pools in the rule's layout, which the
//! right-hand side (`crate::seq_rhs`) reads.

use crate::ast::{LitValVarId, MultVarId, VarId};
use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::egraph::EGraph;
use crate::ematch::{Match, MatchPool};
use crate::index::VariantIndex;
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;
use crate::resolve::{ColRef, GlobalCtx, RestRef};
use crate::seq_collect::{Env, Slots, Source, Spec, Value, mult_column, value_eq};
use crate::seq_query::{FilterPlans, RowVal, SubQuery};
use std::sync::Arc;

/// Where a scalar (a simple item's variable) lives in the match.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarRef {
    Node(VarId),
    Lit(LitValVarId),
    Mult(MultVarId),
}

/// The layout the assembled matches are written in: the rule's `MatchShape`
/// (`collection::seq_shape`), by `Spec` index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    /// Per filter: its children's pool and its variables' columns, in
    /// `SFilter::vars` order.
    pub filters: Vec<(RestRef, Vec<ColRef>)>,
    /// The bare sequences, by name.
    pub bare: Vec<(String, RestRef)>,
    /// Per scalar slot.
    pub scalars: Vec<ScalarRef>,
}

/// What the assembly and the write need, independent of sorts and index widths.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Assembly {
    pub spec: Spec,
    /// Per simple item: the scalar slot of each of its sub-query's variables.
    pub one_slots: Vec<Vec<usize>>,
    pub layout: Layout,
}

/// The `Collect` atom's payload: the assembly and every item's sub-query.
#[derive(Debug)]
pub struct CollectSpec<O, S, L> {
    pub asm: Arc<Assembly>,
    pub filters: Vec<SubQuery<O, S, L>>,
    pub ones: Vec<SubQuery<O, S, L>>,
    /// The root operator.
    pub op: O,
    /// Per filter: the rule cannot fire when it is empty (`SeqRhs::required_nonempty`).
    pub required: Vec<bool>,
    /// `:flatten`: a node's matches are its flattened views' (`crate::flatten`), and a
    /// filter drive climbs through nesting to find its candidates.
    pub flatten: bool,
}

/// How a `Collect` finds its nodes (Semper design §7.6, "Choosing where to
/// start"). Both give the same match set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Drive {
    /// Every node of the root operator, assembled in full.
    Root,
    /// Candidates from the driving filters' rows: the variadic parents of each class
    /// holding a row, assembled in full (part 1); then, when part 2 runs, the other nodes
    /// of the root operator, assembled with every filter empty, which is exact because
    /// none of their children has a row of any filter.
    Filters,
}

/// How a filter's rows at a child class are obtained under a filter drive.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Access {
    /// Run the bound-root plan at the class.
    Probe,
    /// Run the free-root plan once per round and look the class up in its rows.
    Materialize,
}

thread_local! {
    /// Test support: force the drive and the access path for every `Collect` scheduled
    /// on this thread (the plan-invariance tests). `None` lets the cost model choose.
    static PLAN_OVERRIDE: std::cell::Cell<Option<(Drive, Access)>> = const { std::cell::Cell::new(None) };
}

/// Force (`Some`) or release (`None`) the plan of every `Collect` scheduled on this
/// thread. A forced filter drive falls back to the root when a driving filter has no
/// free-root plan (a variable base), since its rows cannot be listed; a filter without
/// one is always probed.
#[doc(hidden)]
pub fn set_plan_override(p: Option<(Drive, Access)>) {
    PLAN_OVERRIDE.with(|c| c.set(p));
}

/// `SEMPER_SEQ_FORCE_DRIVE=root|filters`: force every `Collect`'s drive, for the
/// measurement against the root drive (task 5 of
/// `doc/goal-flatten-and-engine-completion.md`). Read once. A forced filter drive keeps
/// the access the cost model would give it under that drive; any other value is
/// ignored, as is the variable when unset.
fn forced_drive() -> Option<(Drive, Access)> {
    static FORCED: std::sync::OnceLock<Option<(Drive, Access)>> = std::sync::OnceLock::new();
    *FORCED.get_or_init(
        || match std::env::var("SEMPER_SEQ_FORCE_DRIVE").as_deref() {
            Ok("root") => Some((Drive::Root, Access::Probe)),
            Ok("filters") => Some((Drive::Filters, Access::Materialize)),
            _ => None,
        },
    )
}

/// Append one rule's drive measurement (see [`drive_stats_dir`]). A write failure is
/// reported once per line and does not stop the run: the file is a measurement.
fn record_drive<Cfg: EGraphConfig, L: LitVal>(
    dir: &std::path::Path,
    r: &SeqRule<Cfg, L>,
    plan: &crate::schedule::QueryPlan<Cfg::O, Cfg::Index, L>,
    index: &crate::index::IndexStore<Cfg>,
    pool: &MatchPool<Cfg>,
    took: std::time::Duration,
    strategy: &str,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let Some(drive) = plan.steps.iter().find_map(|s| match s {
        crate::schedule::Step::Collect { plan, .. } => Some(plan.0.drive),
        _ => None,
    }) else {
        return;
    };
    let by_op = index.nodes_by_op(r.root_op()).len();
    let (p1, p2) = match drive {
        // The root drive assembles every node of the root operator.
        Drive::Root => (by_op, 0),
        Drive::Filters => pool.collect_driven,
    };
    record_line(
        dir,
        &r.name,
        &format!("{drive:?}"),
        p1,
        p2,
        by_op,
        took,
        strategy,
    );
}

/// Append one line to this process's drive-statistics file (see [`drive_stats_dir`]).
fn record_line(
    dir: &std::path::Path,
    rule: &str,
    drive: &str,
    p1: usize,
    p2: usize,
    by_op: usize,
    took: std::time::Duration,
    strategy: &str,
) {
    use std::io::Write;
    let line = format!(
        "{rule}\t{drive}\t{p1}\t{p2}\t{by_op}\t{}\t{strategy}\n",
        took.as_micros()
    );
    let path = dir.join(format!("{}.tsv", std::process::id()));
    let written = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .and_then(|mut f| f.write_all(line.as_bytes()));
    if let Err(e) = written {
        eprintln!("warning: SEMPER_SEQ_DRIVE_STATS: {}: {e}", path.display());
    }
}

/// `SEMPER_SEQ_DRIVE_STATS=DIR`: per rule and round, one line of `{rule} {drive}
/// {part1} {part2} {|ByOp(root)|} {microseconds} {strategy}` into `DIR/{pid}.tsv`, the
/// strategy `naive`, `filter`, or `enumerate` and the time including the guard. Read
/// once.
fn drive_stats_dir() -> Option<&'static std::path::Path> {
    static DIR: std::sync::OnceLock<Option<std::path::PathBuf>> = std::sync::OnceLock::new();
    DIR.get_or_init(|| std::env::var_os("SEMPER_SEQ_DRIVE_STATS").map(Into::into))
        .as_deref()
}

/// `Arc<CollectSpec>` compared by identity, so that `RAtom` keeps its `Eq`: two
/// atoms are one `Collect` exactly when they share their payload.
#[derive(Debug)]
pub struct CollectRef<O, S, L>(pub Arc<CollectSpec<O, S, L>>);

impl<O, S, L> Clone for CollectRef<O, S, L> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}
impl<O, S, L> PartialEq for CollectRef<O, S, L> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl<O, S, L> Eq for CollectRef<O, S, L> {}

/// The `Collect` step's plan: the assembly and every item's two plans.
#[derive(Debug)]
pub struct CollectPlan<O, I, L> {
    pub asm: Arc<Assembly>,
    pub filters: Vec<FilterPlans<O, I, L>>,
    pub ones: Vec<FilterPlans<O, I, L>>,
    pub op: O,
    pub drive: Drive,
    /// Per filter, used under `Drive::Filters`; the root drive always probes.
    pub access: Vec<Access>,
    /// The filters whose rows find the candidates.
    pub drivers: Vec<usize>,
    /// Whether part 2 runs: false when some filter is required non-empty, and then the
    /// candidates are the nodes holding a row of *every* required filter.
    pub part2: bool,
    /// `CollectSpec::flatten`.
    pub flatten: bool,
}

/// `Arc<CollectPlan>` compared by identity, for `Step`'s `Eq`.
#[derive(Debug)]
pub struct CollectPlanRef<O, I, L>(pub Arc<CollectPlan<O, I, L>>);

impl<O, I, L> Clone for CollectPlanRef<O, I, L> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}
impl<O, I, L> PartialEq for CollectPlanRef<O, I, L> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl<O, I, L> Eq for CollectPlanRef<O, I, L> {}

impl<O: crate::DenseId + std::hash::Hash + Copy, S: crate::DenseId + Copy, L: Clone>
    CollectSpec<O, S, L>
{
    /// Every item's plans, priced with `stats`, and the drive and access paths.
    pub fn plans<I: crate::containers::IndexLike>(
        &self,
        stats: &crate::schedule::IndexStats<O>,
    ) -> CollectPlan<O, I, L> {
        let required: Vec<usize> = (0..self.filters.len())
            .filter(|&g| self.required.get(g).copied().unwrap_or(false))
            .collect();
        let part2 = required.is_empty();
        // With part 2, every filter's rows must be listed: a node is left to part 2 only
        // if none of its children has a row of *any* filter.
        let drivers: Vec<usize> = if part2 {
            (0..self.filters.len()).collect()
        } else {
            required
        };
        let drivable = !drivers.is_empty() && drivers.iter().all(|&g| !self.filters[g].every_class);
        let nodes = stats.op_card.get(&self.op).copied().unwrap_or(0);
        let rows = drivers
            .iter()
            .map(|&g| est_rows(&self.filters[g], stats))
            .fold(0usize, usize::saturating_add);
        let forced = PLAN_OVERRIDE.with(|c| c.get()).or_else(forced_drive);
        let drive = match forced {
            Some((Drive::Filters, _)) if drivable => Drive::Filters,
            Some(_) => Drive::Root,
            // Filter-driven when the driving rows are fewer than the root's nodes: each row
            // reaches only its parents, and part 2 probes no filter.
            None if drivable && rows < nodes => Drive::Filters,
            None => Drive::Root,
        };
        let access = self
            .filters
            .iter()
            .map(|q| match forced {
                _ if q.every_class => Access::Probe,
                Some((_, a)) => a,
                None if drive == Drive::Root => Access::Probe,
                None => Access::Materialize,
            })
            .collect();
        CollectPlan {
            asm: Arc::clone(&self.asm),
            filters: self.filters.iter().map(|q| q.plans(stats)).collect(),
            ones: self.ones.iter().map(|q| q.plans(stats)).collect(),
            op: self.op,
            drive,
            access,
            drivers,
            part2,
            flatten: self.flatten,
        }
    }
}

/// An upper bound on a sub-query's rows from the round's statistics: the cardinality of
/// the operator its root atom scans, 1 for a global, unbounded when unknown.
fn est_rows<O: crate::DenseId + std::hash::Hash + Copy, S, L>(
    q: &SubQuery<O, S, L>,
    stats: &crate::schedule::IndexStats<O>,
) -> usize {
    use crate::resolve::RAtom;
    for a in &q.query.atoms {
        match a {
            RAtom::Plain { node, op, .. }
            | RAtom::Lit { node, op, .. }
            | RAtom::LitBind { node, op, .. }
                if *node == q.root =>
            {
                return stats.op_card.get(op).copied().unwrap_or(0);
            }
            RAtom::EqGlobal(v, _) if *v == q.root => return 1,
            _ => {}
        }
    }
    usize::MAX
}

/// A filter's rows for the whole round, by class (a snapshot representative).
type Materialized<G, V> = std::collections::BTreeMap<G, Vec<crate::seq_query::Row<G, V>>>;

/// The round's filter rows shared across rules (`doc/goal-semi-naive-sequence-rules.md`,
/// step 5), keyed by the filter's free-root plan and its row layout: two filters with
/// equal keys list the same rows on one snapshot. `apply_rules` holds one per call, so
/// no entry outlives the snapshot it was computed on.
pub(crate) type RowCache<G, V> = std::collections::HashMap<String, Arc<Materialized<G, V>>>;

thread_local! {
    static FREE_ROW_RUNS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Test support: the free-root plans a filter drive has run on this thread (the cache
/// misses of [`RowCache`]).
#[doc(hidden)]
pub fn free_row_runs() -> u64 {
    FREE_ROW_RUNS.with(|c| c.get())
}

/// Where filter rows come from at one node.
enum FilterRows<'m, G, V> {
    Probe,
    /// Per filter: the round's rows by class when materialized, else probe.
    Materialized(&'m [Option<Arc<Materialized<G, V>>>]),
    /// Part 2: no child of the node has a row of any filter.
    Empty,
}

/// The rows of the snapshot: every item's bound-root plan probed at a child class.
struct Probe<'a, 'p, Cfg: EGraphConfig, L: LitVal, SG, const T: bool, const P: bool>
where
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    plan: &'a CollectPlan<Cfg::O, Cfg::Index, L>,
    eg: &'a EGraph<Cfg, L, T, P>,
    index: &'a VariantIndex<'a, Cfg>,
    globals: &'a GlobalCtx<SG, Cfg::G>,
    pool: &'p mut MatchPool<Cfg>,
    rows: FilterRows<'a, Cfg::G, Cfg::V>,
}

fn row_value<G, V>(v: RowVal<G, V>) -> Value<G, V> {
    match v {
        RowVal::Class(c) => Value::Class(c),
        RowVal::Lit(l) => Value::Lit(l),
    }
}

impl<Cfg, L, SG: Copy, const T: bool, const P: bool> Source<Cfg::G, Cfg::V>
    for Probe<'_, '_, Cfg, L, SG, T, P>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    fn one(
        &mut self,
        item: usize,
        class: Cfg::G,
        scalars: &Slots<Cfg::G, Cfg::V>,
    ) -> Result<Vec<Slots<Cfg::G, Cfg::V>>, String> {
        let plans = self
            .plan
            .ones
            .get(item)
            .ok_or("internal: no plan for a simple item")?;
        let slots = self
            .plan
            .asm
            .one_slots
            .get(item)
            .ok_or("internal: no slots for a simple item")?;
        let mut out = Vec::new();
        'rows: for row in plans.probe(self.eg, self.index, self.globals, self.pool, class) {
            let mut b = scalars.clone();
            for (&slot, v) in slots.iter().zip(row.vals) {
                let v = row_value(v);
                let cell = b
                    .get_mut(slot)
                    .ok_or("internal: a scalar slot out of range")?;
                match cell {
                    // A variable an earlier item bound: the rows must agree (a join).
                    Some(old) if !value_eq(old, &v) => continue 'rows,
                    Some(_) => {}
                    None => *cell = Some(v),
                }
            }
            out.push(b);
        }
        Ok(out)
    }

    fn filter(
        &mut self,
        fi: usize,
        class: Cfg::G,
        init: &Slots<Cfg::G, Cfg::V>,
    ) -> Result<Vec<Slots<Cfg::G, Cfg::V>>, String> {
        let plans = self
            .plan
            .filters
            .get(fi)
            .ok_or("internal: no plan for a filter")?;
        let rows = match &self.rows {
            FilterRows::Empty => return Ok(Vec::new()),
            FilterRows::Materialized(m) => match m.get(fi) {
                Some(Some(by_class)) => by_class.get(&class).cloned().unwrap_or_default(),
                _ => plans.probe(self.eg, self.index, self.globals, self.pool, class),
            },
            FilterRows::Probe => plans.probe(self.eg, self.index, self.globals, self.pool, class),
        };
        let mut out = Vec::new();
        for row in rows {
            let mut b = init.clone();
            for (cell, v) in b.iter_mut().zip(row.vals) {
                *cell = Some(row_value(v));
            }
            out.push(b);
        }
        Ok(out)
    }
}

/// The matches at root node `node`: its children through the snapshot, their rows
/// by probe, assembled. `pool` is scratch for the probes.
pub(crate) fn collect_at<Cfg, L, SG: Copy, const T: bool, const P: bool>(
    plan: &CollectPlan<Cfg::O, Cfg::Index, L>,
    node: Cfg::G,
    eg: &EGraph<Cfg, L, T, P>,
    index: &VariantIndex<'_, Cfg>,
    globals: &GlobalCtx<SG, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
) -> Result<Vec<Env<Cfg::G, Cfg::V>>, String>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    collect_with(plan, node, eg, index, globals, pool, FilterRows::Probe)
}

/// The matches at `node` with filter rows from `rows` (a filter drive).
fn collect_with<'a, Cfg, L, SG: Copy, const T: bool, const P: bool>(
    plan: &'a CollectPlan<Cfg::O, Cfg::Index, L>,
    node: Cfg::G,
    eg: &'a EGraph<Cfg, L, T, P>,
    index: &'a VariantIndex<'a, Cfg>,
    globals: &'a GlobalCtx<SG, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
    rows: FilterRows<'a, Cfg::G, Cfg::V>,
) -> Result<Vec<Env<Cfg::G, Cfg::V>>, String>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    let mut src = Probe {
        plan,
        eg,
        index,
        globals,
        pool,
        rows,
    };
    if plan.flatten {
        let spec = &plan.asm.spec;
        let snap = crate::flatten::Snapshot { eg, index };
        let kind = crate::flatten::FlatKind::of(spec.assoc, spec.ac);
        let views = crate::flatten::views_u64(&snap, node, plan.op, kind)?;
        return crate::seq_collect::assemble_views(spec, &mut src, &views);
    }
    let mut kids = Vec::new();
    let mut wide = false;
    eg.for_each_child(node, |c, m| match m.to_u64() {
        Some(m) => kids.push((crate::ematch::round_canon(index, eg, c), m)),
        None => wide = true,
    });
    if wide {
        return Err("a multiplicity wider than 64 bits".into());
    }
    crate::seq_collect::assemble(&plan.asm.spec, &mut src, &kids)
}

/// A filter drive's nodes for one round: the candidates, sorted and deduplicated
/// (part 1), the other nodes of the root operator when part 2 runs, and the rows of
/// every filter whose access is `Materialize`.
pub(crate) struct Driven<G, V> {
    pub part1: Vec<G>,
    pub part2: Vec<G>,
    rows: Vec<Option<Arc<Materialized<G, V>>>>,
}

/// Compute a filter drive: each driving filter's rows by its free-root plan, and as
/// candidates their classes' variadic parents of the root operator (`by_contains`),
/// the union over the drivers when part 2 runs, else the intersection over the
/// required filters. Every class compared is a snapshot representative.
pub(crate) fn drive<Cfg, L, SG: Copy, const T: bool, const P: bool>(
    plan: &CollectPlan<Cfg::O, Cfg::Index, L>,
    eg: &EGraph<Cfg, L, T, P>,
    index: &VariantIndex<'_, Cfg>,
    globals: &GlobalCtx<SG, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
    mut cache: Option<&mut RowCache<Cfg::G, Cfg::V>>,
) -> Result<Driven<Cfg::G, Cfg::V>, String>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    use crate::containers::DenseId;
    let full = index.full;
    let mut rows: Vec<Option<Arc<Materialized<Cfg::G, Cfg::V>>>> = vec![None; plan.filters.len()];
    let mut per_driver: Vec<Vec<Cfg::G>> = Vec::with_capacity(plan.drivers.len());
    for (fi, fp) in plan.filters.iter().enumerate() {
        let is_driver = plan.drivers.contains(&fi);
        let materialize = plan.access.get(fi) == Some(&Access::Materialize);
        if !is_driver && !materialize {
            continue;
        }
        // The steps and the row layout decide the rows; the shape's variable names
        // do not, and its kinds map has no stable order.
        let key = match (&cache, &fp.free) {
            (Some(_), Some(free)) => Some(format!("{:?}|{:?}", free.steps, fp.vars)),
            _ => None,
        };
        let cached = match (&cache, &key) {
            (Some(c), Some(k)) => c.get(k).cloned(),
            _ => None,
        };
        let by_class = match cached {
            Some(b) => b,
            None => {
                let Some(all) = fp.all(eg, index, globals, pool) else {
                    // No free-root plan (a variable base): `plans` never drives from one
                    // and never materializes it, so reaching this is a planning defect.
                    return Err(format!(
                        "internal: filter {fi} has no free-root plan to drive or materialize"
                    ));
                };
                FREE_ROW_RUNS.with(|c| c.set(c.get().saturating_add(1)));
                let mut by_class: Materialized<Cfg::G, Cfg::V> = std::collections::BTreeMap::new();
                for (c, r) in all {
                    by_class.entry(c).or_default().push(r);
                }
                let by_class = Arc::new(by_class);
                if let (Some(c), Some(k)) = (cache.as_deref_mut(), key) {
                    c.insert(k, Arc::clone(&by_class));
                }
                by_class
            }
        };
        if is_driver {
            let mut cand: Vec<Cfg::G> = Vec::new();
            if plan.flatten {
                climb(full, plan.op, by_class.keys().copied(), &mut cand);
            } else {
                for &c in by_class.keys() {
                    for &n in full.nodes_by_contains(c) {
                        if full.round_op(n) == Some(plan.op) {
                            cand.push(n);
                        }
                    }
                }
            }
            cand.sort_unstable_by_key(|n| n.to_usize());
            cand.dedup();
            per_driver.push(cand);
        }
        if materialize {
            rows[fi] = Some(by_class);
        }
    }
    let part1: Vec<Cfg::G> = if plan.part2 {
        let mut u: Vec<Cfg::G> = per_driver.into_iter().flatten().collect();
        u.sort_unstable_by_key(|n| n.to_usize());
        u.dedup();
        u
    } else {
        // A node where some required filter has no row cannot fire.
        let mut it = per_driver.into_iter();
        let mut acc = it.next().unwrap_or_default();
        for next in it {
            let keep: std::collections::BTreeSet<usize> =
                next.iter().map(|n| n.to_usize()).collect();
            acc.retain(|n| keep.contains(&n.to_usize()));
        }
        acc
    };
    let part2 = if plan.part2 {
        let inside: std::collections::BTreeSet<usize> =
            part1.iter().map(|n| n.to_usize()).collect();
        full.nodes_by_op(plan.op)
            .iter()
            .copied()
            .filter(|n| !inside.contains(&n.to_usize()))
            .collect()
    } else {
        Vec::new()
    };
    Ok(Driven { part1, part2, rows })
}

/// The candidates of a flattened filter drive: every node of operator `op` whose
/// views can hold one of `rows`' classes. A view splices the children of `op` members
/// only, so climbing from a class to its `op` parents (`by_contains`), then to those
/// parents' classes, and so on, reaches every such node. The climb is an explicit
/// stack with a visited set, since its depth follows the nesting and a cyclic class
/// would otherwise repeat. Part 2 stays exact: a node the climb does not reach has no
/// row's class in any of its views.
fn climb<Cfg: EGraphConfig>(
    full: &crate::index::IndexStore<Cfg>,
    op: Cfg::O,
    rows: impl Iterator<Item = Cfg::G>,
    cand: &mut Vec<Cfg::G>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    use crate::containers::DenseId;
    let mut stack: Vec<Cfg::G> = rows.collect();
    let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
    while let Some(x) = stack.pop() {
        if !seen.insert(x.to_usize()) {
            continue;
        }
        for &n in full.nodes_by_contains(x) {
            if full.round_op(n) != Some(op) {
                continue;
            }
            cand.push(n);
            if let Some(k) = full.round_repr(n) {
                stack.push(k);
            }
        }
    }
}

/// A node of a filter drive: a part-1 node with the drive's rows, a part-2 node with
/// every filter empty (the design's `CollectEmpty`; no filter is probed).
#[allow(clippy::too_many_arguments)]
pub(crate) fn collect_driven<'a, Cfg, L, SG: Copy, const T: bool, const P: bool>(
    plan: &'a CollectPlan<Cfg::O, Cfg::Index, L>,
    node: Cfg::G,
    in_part2: bool,
    driven: &'a Driven<Cfg::G, Cfg::V>,
    eg: &'a EGraph<Cfg, L, T, P>,
    index: &'a VariantIndex<'a, Cfg>,
    globals: &'a GlobalCtx<SG, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
) -> Result<Vec<Env<Cfg::G, Cfg::V>>, String>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    let rows = if in_part2 {
        FilterRows::Empty
    } else {
        FilterRows::Materialized(&driven.rows)
    };
    collect_with(plan, node, eg, index, globals, pool, rows)
}

/// Write an assembled match into `m`, in the layout. The caller restores `m`'s pools
/// (`Match::mark`/`restore`) and its node scalars (`unfill`) afterwards.
pub(crate) fn fill<Cfg: EGraphConfig>(
    asm: &Assembly,
    env: &Env<Cfg::G, Cfg::V>,
    m: &mut Match<Cfg>,
) -> Result<(), String> {
    let seq = |n: &str| match env.get(n) {
        Some(Value::Seq(xs)) => Ok(xs),
        _ => Err(format!("internal: '{n}' is not a sequence of the match")),
    };
    let classes = |xs: &[Value<Cfg::G, Cfg::V>]| {
        xs.iter()
            .map(|x| {
                if let Value::Class(g) = x {
                    Ok(*g)
                } else {
                    Err("internal: a class expected".to_string())
                }
            })
            .collect::<Result<Vec<_>, _>>()
    };
    let narrow = |k: u64| {
        Cfg::M::try_from_u64(k).ok_or_else(|| {
            format!("multiplicity overflow: the count {k} is beyond the configured width")
        })
    };
    let push_rest = |m: &mut Match<Cfg>, name: &str, rr: RestRef| -> Result<(), String> {
        let gs = classes(seq(name)?)?;
        match rr {
            RestRef::Seq(v) => m.push_seq(v, &gs),
            RestRef::Set(v) => m.push_set(v, &gs),
            RestRef::Mset(v) => {
                let ms = seq(&mult_column(name))?;
                let mut cs = Vec::with_capacity(gs.len());
                for (g, k) in gs.iter().zip(ms) {
                    let Value::Count(k) = k else {
                        return Err(format!(
                            "internal: ..{name}: a multiplicity column of non-counts"
                        ));
                    };
                    cs.push(Cfg::mset_child_with_mult(*g, narrow(*k)?));
                }
                m.push_mset(v, &cs);
            }
        }
        Ok(())
    };
    for (f, (elems, cols)) in asm.spec.filters.iter().zip(&asm.layout.filters) {
        push_rest(m, &f.name, *elems)?;
        for (name, col) in f.vars.iter().zip(cols) {
            match col {
                ColRef::Node(v) => m.push_seq(*v, &classes(seq(name)?)?),
                ColRef::Lit(v) => {
                    let mut vs = Vec::new();
                    for x in seq(name)? {
                        let Value::Lit(l) = x else {
                            return Err(format!(
                                "internal: '{name}': a literal column of non-literals"
                            ));
                        };
                        vs.push(*l);
                    }
                    m.push_lit_seq(*v, &vs);
                }
                ColRef::Mult(_) => {}
            }
        }
    }
    for (name, rr) in &asm.layout.bare {
        push_rest(m, name, *rr)?;
    }
    for (name, sr) in asm.spec.scalars.iter().zip(&asm.layout.scalars) {
        match (sr, env.get(name)) {
            (ScalarRef::Node(v), Some(Value::Class(g))) => m.set(*v, *g),
            (ScalarRef::Lit(v), Some(Value::Lit(l))) => m.set_lit_val(*v, *l),
            (ScalarRef::Mult(v), Some(Value::Count(k))) => m.set_mult(*v, narrow(*k)?),
            _ => return Err(format!("internal: '{name}' is not a scalar of the match")),
        }
    }
    Ok(())
}

/// Clear the node scalars `fill` bound.
pub(crate) fn unfill<Cfg: EGraphConfig>(asm: &Assembly, m: &mut Match<Cfg>) {
    for sr in &asm.layout.scalars {
        if let ScalarRef::Node(v) = sr {
            m.clear(*v);
        }
    }
}

// ── Application ──────────────────────────────────────────────────────────────

/// One query's matches into `plans`: its skips and its fault reported, and each
/// match's `:let` prelude evaluated (a match whose `:when` fails is dropped here).
#[allow(clippy::type_complexity)]
fn harvest<Cfg, L, M, const T: bool, const P: bool>(
    r: &SeqRule<Cfg, L>,
    ri: usize,
    pool: &MatchPool<Cfg>,
    eg: &EGraph<Cfg, L, T, P>,
    model: &M,
    plans: &mut Vec<(Cfg::G, usize, Match<Cfg>, Vec<L>)>,
    report: &mut crate::collection::PassReport,
) -> Result<(), String>
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    let (skipped, fault) = pool.collect_report();
    if let Some(f) = fault {
        return Err(format!("{}: {f}", r.name));
    }
    if skipped > 0 {
        eprintln!(
            "warning: {}: {skipped} nodes with {} skipped",
            r.name,
            crate::seq_collect::OVER_BOUND
        );
        report.skipped_nodes += skipped;
    }
    for j in 0..pool.len() {
        let row = pool.row(j);
        let lets = crate::seq_rhs::prelude(&r.seq_rhs, &r.seq_shape, &row, eg, model)
            .map_err(|e| format!("{}: {e}", r.name))?;
        if let Some(lets) = lets {
            plans.push((
                crate::ematch::MatchView::get(&row, r.root_var),
                ri,
                pool.clone_match(j),
                lets,
            ));
        }
    }
    Ok(())
}

/// `Δ_collect` for one rule and round (Semper design §7.6, "Semi-naive
/// evaluation"): the root-operator nodes in the delta, and the root-operator parents
/// of the affected classes. The affected classes are the root classes of each item
/// sub-query's delta rows (its variants, one per join atom, against the round's
/// delta) and the classes of the round's subsumed nodes. Under `:flatten` the parents
/// are found by the climb of task 4, from the affected classes and from the class of
/// every touched node, since a class's membership decides which of its ancestors'
/// views exist. `None` means the rule must be matched naively: an item sub-query needs
/// the naive path (`saturate::needs_naive_match`) or has no join atom. The oracle of
/// `doc/goal-semi-naive-sequence-rules.md` (decision 1): the coverage tests pin it, and
/// every semi-naive strategy must select the nodes it selects among naive's candidates.
#[doc(hidden)]
pub fn delta_nodes<Cfg, L, const T: bool, const P: bool>(
    r: &SeqRule<Cfg, L>,
    eg: &EGraph<Cfg, L, T, P>,
    full: &crate::index::IndexStore<Cfg>,
    d: &crate::saturate::RoundDelta<'_, Cfg>,
    globals: &GlobalCtx<Cfg::S, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
) -> Option<Vec<Cfg::G>>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    use crate::containers::DenseId;
    let (op, flatten, affected) = guard(r, eg, full, d, globals, pool)?;
    let mut nodes: Vec<Cfg::G> = d.index.nodes_by_op(op).to_vec();
    if flatten {
        let seeds = affected
            .iter()
            .copied()
            .chain(d.touched.iter().filter_map(|&t| full.round_repr(t)));
        climb(full, op, seeds, &mut nodes);
    } else {
        for &c in &affected {
            for &n in full.nodes_by_contains(c) {
                if full.round_op(n) == Some(op) {
                    nodes.push(n);
                }
            }
        }
    }
    nodes.sort_unstable_by_key(|n| n.to_usize());
    nodes.dedup();
    Some(nodes)
}

/// The guard of the aggregate derivative: the rule's root operator, whether it is
/// `:flatten`, and the affected classes (snapshot representatives, sorted and
/// deduplicated) of `delta_nodes`. `None` when the rule must be matched naively.
#[allow(clippy::type_complexity)]
fn guard<Cfg, L, const T: bool, const P: bool>(
    r: &SeqRule<Cfg, L>,
    eg: &EGraph<Cfg, L, T, P>,
    full: &crate::index::IndexStore<Cfg>,
    d: &crate::saturate::RoundDelta<'_, Cfg>,
    globals: &GlobalCtx<Cfg::S, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
) -> Option<(Cfg::O, bool, Vec<Cfg::G>)>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    use crate::containers::DenseId;
    let Some(crate::resolve::RAtom::Collect { op, collect, .. }) = r.query.atoms.first() else {
        return None;
    };
    let spec = &collect.0;
    let naive = VariantIndex::naive(full);
    let mut affected: Vec<Cfg::G> = Vec::new();
    for sq in spec.filters.iter().chain(&spec.ones) {
        // A variable base matches every class with the class itself as its row, so its
        // rows change only when a class does, which recanonicalizes the parent.
        if sq.every_class {
            continue;
        }
        let atoms = crate::saturate::join_atom_indices(&sq.query);
        if atoms.is_empty() || crate::saturate::needs_naive_match(&sq.query) {
            return None;
        }
        for di in atoms {
            let stats = crate::saturate::variant_stats(&sq.query, di, full, d.index);
            let vindex = VariantIndex::variant(full, d.index, di);
            let plan = crate::schedule::schedule_with_stats(&sq.query, &stats);
            crate::ematch::run_query_into(&plan, eg, &vindex, globals, pool);
            for j in 0..pool.len() {
                let root = crate::ematch::MatchView::get(&pool.row(j), sq.root);
                affected.push(crate::ematch::round_canon(&naive, eg, root));
            }
        }
    }
    affected.extend(d.subsumed.iter().filter_map(|&s| full.round_repr(s)));
    affected.sort_unstable_by_key(|c| c.to_usize());
    affected.dedup();
    Some((*op, spec.flatten, affected))
}

/// Semi-filter's test (`doc/goal-semi-naive-sequence-rules.md`, decision 1 and step 3):
/// a root node is assembled if it is in the delta, or if one of its child classes is
/// affected. Under `:flatten` the test descends from the node through the classes its
/// views splice (members of the root operator), and the seeds include the classes of
/// the touched nodes, as `delta_nodes`' climb does.
pub(crate) struct Keep<O> {
    op: O,
    flatten: bool,
    /// The root-operator nodes in the delta, by id.
    roots: std::collections::HashSet<usize>,
    /// The affected classes (snapshot representatives), by id.
    classes: std::collections::HashSet<usize>,
    /// Semi-enumerate: the nodes `N_D ∪ parents(A)`, listed beforehand; the test is
    /// membership alone.
    exact: Option<std::collections::HashSet<usize>>,
}

impl<O: Copy + Eq> Keep<O> {
    /// Whether root node `node` may have a match it did not have in the previous round.
    pub(crate) fn passes<Cfg, L, const T: bool, const P: bool>(
        &self,
        node: Cfg::G,
        eg: &EGraph<Cfg, L, T, P>,
        index: &VariantIndex<'_, Cfg>,
    ) -> bool
    where
        Cfg: EGraphConfig<O = O>,
        L: LitVal,
        MSetCanon: VarCanon<Cfg::G, Cfg::C>,
        Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
    {
        use crate::containers::DenseId;
        if let Some(exact) = &self.exact {
            return exact.contains(&node.to_usize());
        }
        if self.roots.contains(&node.to_usize()) {
            return true;
        }
        let mut stack: Vec<Cfg::G> = Vec::new();
        eg.for_each_child(node, |c, _| {
            stack.push(crate::ematch::round_canon(index, eg, c))
        });
        if !self.flatten {
            return stack.iter().any(|c| self.classes.contains(&c.to_usize()));
        }
        // An explicit stack with a visited set: the depth follows the nesting, and a
        // cyclic class would otherwise repeat. A descent over the views' work bound
        // keeps the node, so no node whose matches may have changed is skipped.
        let full = index.full;
        let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
        let mut work = 0usize;
        while let Some(k) = stack.pop() {
            if !seen.insert(k.to_usize()) {
                continue;
            }
            if self.classes.contains(&k.to_usize()) {
                return true;
            }
            for &m in full.nodes_by_repr(k) {
                if full.round_op(m) != Some(self.op) {
                    continue;
                }
                work = work.saturating_add(1);
                if work > crate::flatten::MAX_WORK {
                    return true;
                }
                eg.for_each_child(m, |c, _| {
                    stack.push(crate::ematch::round_canon(index, eg, c))
                });
            }
        }
        false
    }
}

/// Semi-enumerate runs only when the nodes it lists, `N_D ∪ parents(A)`, number at most
/// `|ByOp(root)| / ENUMERATE_DIVISOR`; the bound on `parents(A)` is the bucket lengths,
/// read before any bucket is walked. A hub class exceeds it and leaves the round to
/// semi-filter (`doc/goal-semi-naive-sequence-rules.md`, step 4).
const ENUMERATE_DIVISOR: usize = 4;

/// Rule `r`'s semi-naive strategy this round, or `None` for naive: the guard runs only
/// if its estimate is below the naive work it can save (decision 3), and its result is
/// semi-enumerate's node list when that list is short (decision 2), else semi-filter's
/// test. `force` is test support: `Some(false)` semi-filter and `Some(true)`
/// semi-enumerate regardless of the estimates (semi-enumerate still falls back to
/// semi-filter over the walk's bound).
#[allow(clippy::too_many_arguments)]
fn semi_strategy<Cfg, L, const T: bool, const P: bool>(
    r: &SeqRule<Cfg, L>,
    eg: &EGraph<Cfg, L, T, P>,
    full: &crate::index::IndexStore<Cfg>,
    d: &crate::saturate::RoundDelta<'_, Cfg>,
    stats: &crate::schedule::IndexStats<Cfg::O>,
    globals: &GlobalCtx<Cfg::S, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
    plan: &CollectPlan<Cfg::O, Cfg::Index, L>,
    force: Option<bool>,
) -> Option<Keep<Cfg::O>>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    use crate::containers::DenseId;
    let est = semi_estimate_with(r, full, d.index, stats, plan);
    if force.is_none() && !est?.guard_pays() {
        return None;
    }
    let (op, flatten, affected) = guard(r, eg, full, d, globals, pool)?;
    let mut seeds: Vec<Cfg::G> = affected;
    if flatten {
        seeds.extend(d.touched.iter().filter_map(|&t| full.round_repr(t)));
    }
    let roots: Vec<Cfg::G> = d.index.nodes_by_op(op).to_vec();
    let nodes = full.nodes_by_op(op).len();
    let enumerate = match force {
        Some(e) => e,
        None => roots.len() <= nodes / ENUMERATE_DIVISOR,
    };
    let budget = match force {
        Some(_) => usize::MAX,
        None => (nodes / ENUMERATE_DIVISOR).saturating_sub(roots.len()),
    };
    let exact = if enumerate {
        parents_bounded(full, op, flatten, &seeds, budget).map(|ps| {
            roots
                .iter()
                .chain(&ps)
                .map(|n| n.to_usize())
                .collect::<std::collections::HashSet<usize>>()
        })
    } else {
        None
    };
    Some(Keep {
        op,
        flatten,
        roots: roots.iter().map(|n| n.to_usize()).collect(),
        classes: seeds.iter().map(|c| c.to_usize()).collect(),
        exact,
    })
}

/// The root-operator parents of `seeds` (under `:flatten`, the climb of [`climb`]), or
/// `None` when the bucket entries to walk exceed `budget`. Each bucket's length is read
/// and charged before the bucket is walked.
fn parents_bounded<Cfg: EGraphConfig>(
    full: &crate::index::IndexStore<Cfg>,
    op: Cfg::O,
    flatten: bool,
    seeds: &[Cfg::G],
    budget: usize,
) -> Option<Vec<Cfg::G>>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    use crate::containers::DenseId;
    let mut out: Vec<Cfg::G> = Vec::new();
    let mut stack: Vec<Cfg::G> = seeds.to_vec();
    let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
    let mut work = 0usize;
    while let Some(x) = stack.pop() {
        if !seen.insert(x.to_usize()) {
            continue;
        }
        let bucket = full.nodes_by_contains(x);
        work = work.saturating_add(bucket.len());
        if work > budget {
            return None;
        }
        for &n in bucket {
            if full.round_op(n) != Some(op) {
                continue;
            }
            out.push(n);
            if flatten && let Some(k) = full.round_repr(n) {
                stack.push(k);
            }
        }
    }
    Some(out)
}

/// Test support: rule `r` matched by semi-filter (`enumerate` false) or semi-enumerate
/// (true), the guard run regardless of the estimates. The root nodes the `Collect` step
/// was offered, the ones it assembled, and the matches as (root node, match count) per
/// assembled node; `None` when the rule must be matched naively.
#[doc(hidden)]
#[allow(clippy::type_complexity)]
pub fn semi_trace<Cfg, L, const T: bool, const P: bool>(
    r: &SeqRule<Cfg, L>,
    eg: &EGraph<Cfg, L, T, P>,
    full: &crate::index::IndexStore<Cfg>,
    d: &crate::saturate::RoundDelta<'_, Cfg>,
    globals: &GlobalCtx<Cfg::S, Cfg::G>,
    enumerate: bool,
) -> Option<(Vec<Cfg::G>, Vec<Cfg::G>, Vec<(Cfg::G, usize)>)>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    use crate::containers::DenseId;
    let stats = crate::schedule::IndexStats::from_index(full);
    let mut pool = MatchPool::new();
    let naive_plan = crate::schedule::schedule_with_stats(&r.query, &stats);
    let cp = collect_plan_of::<Cfg, L>(&naive_plan)?;
    let keep = semi_strategy(
        r,
        eg,
        full,
        d,
        &stats,
        globals,
        &mut pool,
        cp,
        Some(enumerate),
    )?;
    let plan = schedule_for::<Cfg, L>(r, &keep, &stats);
    pool.collect_keep = Some(Box::new(keep));
    pool.collect_trace = Some((Vec::new(), Vec::new()));
    crate::ematch::run_query_into(&plan, eg, &VariantIndex::naive(full), globals, &mut pool);
    let mut counts: std::collections::BTreeMap<usize, (Cfg::G, usize)> =
        std::collections::BTreeMap::new();
    for j in 0..pool.len() {
        let n = crate::ematch::MatchView::get(&pool.row(j), r.root_var);
        counts.entry(n.to_usize()).or_insert((n, 0)).1 += 1;
    }
    let (offered, assembled) = pool.collect_trace.take()?;
    Some((offered, assembled, counts.into_values().collect()))
}

/// Test support: the strategy `apply_rules` chooses for `r` this round (`"naive"`,
/// `"filter"`, or `"enumerate"`), and the match steps of the semi-naive guard and query
/// against those of naive's query, counted by `ematch::match_steps`.
#[doc(hidden)]
pub fn semi_choice<Cfg, L, const T: bool, const P: bool>(
    r: &SeqRule<Cfg, L>,
    eg: &EGraph<Cfg, L, T, P>,
    full: &crate::index::IndexStore<Cfg>,
    d: &crate::saturate::RoundDelta<'_, Cfg>,
    globals: &GlobalCtx<Cfg::S, Cfg::G>,
) -> (&'static str, u64, u64)
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    let stats = crate::schedule::IndexStats::from_index(full);
    let vindex = VariantIndex::naive(full);
    let mut pool = MatchPool::new();
    let counting = crate::ematch::match_step_counting_enabled();
    crate::ematch::set_match_step_counting(true);
    crate::ematch::reset_match_steps();
    let plan = crate::schedule::schedule_with_stats(&r.query, &stats);
    crate::ematch::run_query_into(&plan, eg, &vindex, globals, &mut pool);
    let naive = crate::ematch::match_steps();
    crate::ematch::reset_match_steps();
    let keep = match collect_plan_of::<Cfg, L>(&plan) {
        Some(cp) => semi_strategy(r, eg, full, d, &stats, globals, &mut pool, cp, None),
        None => None,
    };
    let choice = match &keep {
        None => "naive",
        Some(k) if k.exact.is_some() => "enumerate",
        Some(_) => "filter",
    };
    let plan = match &keep {
        Some(k) if k.exact.is_some() => schedule_for::<Cfg, L>(r, k, &stats),
        _ => plan,
    };
    pool.collect_keep = keep.map(Box::new);
    crate::ematch::run_query_into(&plan, eg, &vindex, globals, &mut pool);
    let semi = crate::ematch::match_steps();
    crate::ematch::set_match_step_counting(counting);
    (choice, semi, naive)
}

/// The rule's plan under `keep`: semi-enumerate's with the root drive, which lists the
/// root operator's nodes and probes the rows of the listed ones only, so no filter's
/// rows are materialized; otherwise the cost model's.
fn schedule_for<Cfg: EGraphConfig, L: LitVal>(
    r: &SeqRule<Cfg, L>,
    keep: &Keep<Cfg::O>,
    stats: &crate::schedule::IndexStats<Cfg::O>,
) -> crate::schedule::QueryPlan<Cfg::O, Cfg::Index, L> {
    if keep.exact.is_none() {
        return crate::schedule::schedule_with_stats(&r.query, stats);
    }
    let prev = PLAN_OVERRIDE.with(|c| c.replace(Some((Drive::Root, Access::Probe))));
    let plan = crate::schedule::schedule_with_stats(&r.query, stats);
    PLAN_OVERRIDE.with(|c| c.set(prev));
    plan
}

/// The estimates that choose a sequence rule's strategy for one round
/// (`doc/goal-semi-naive-sequence-rules.md`, decision 3 and step 2), computed from the
/// indexes' bucket sizes before any of the work they decide about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemiEstimate {
    /// `|ByOp(root)|` in the full index.
    pub nodes: usize,
    /// `|ByOp(root)|` in the delta.
    pub delta_nodes: usize,
    /// The guard: over every item sub-query, over its join atoms, the variant's driver
    /// estimate.
    pub guard: usize,
    /// The nodes naive assembles under the plan the cost model chose.
    pub naive_assembly: usize,
    /// The naive assembly the test of decision 1 is expected to skip.
    pub saving: usize,
}

impl SemiEstimate {
    /// Whether running the guard is expected to pay: it costs less than the naive
    /// assembly it lets the round skip.
    pub fn guard_pays(&self) -> bool {
        self.guard < self.saving
    }
}

/// A variant's driver estimate (§9.2): the least, over the query's join atoms, of
/// that atom's relation in variant `di`, which is the delta for atom `di`, full ∖ delta
/// for the atoms before it, and full for the atoms after it. A variant's join scans at
/// least its driver, so this is the variant's least work; and with the delta equal to the
/// full index, every variant but the first has an empty full ∖ delta atom and costs 0.
fn variant_driver<O: crate::DenseId + std::hash::Hash + Copy, S, L, Cfg>(
    q: &crate::resolve::ResolvedQuery<O, S, L>,
    atoms: &[usize],
    di: usize,
    full: &crate::index::IndexStore<Cfg>,
    delta: &crate::index::IndexStore<Cfg>,
) -> usize
where
    Cfg: EGraphConfig<O = O>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut least = usize::MAX;
    for &j in atoms {
        let Some(op) = q.atoms.get(j).and_then(crate::saturate::atom_op) else {
            continue;
        };
        let f = full.nodes_by_op(op).len();
        let d = delta.nodes_by_op(op).len();
        let card = match j.cmp(&di) {
            std::cmp::Ordering::Equal => d,
            std::cmp::Ordering::Less => f.saturating_sub(d),
            std::cmp::Ordering::Greater => f,
        };
        least = least.min(card);
    }
    if least == usize::MAX { 0 } else { least }
}

/// What one guard variant costs beyond its driver's rows, in nodes assembled: its plan,
/// its variant index, and its query setup, paid even when it returns no row.
///
/// Set from step 6's paired measurement (`tools/measure_seq_semi.sh`, the table of
/// `/tmp/m6/strategy_corpus.txt`). With no such term, the corpus run chose a semi-naive
/// strategy in 1,539 of 11,555 rule rounds whose graphs hold 4 to 32 root nodes, and
/// those rounds cost 1.7 to 2.0 times naive: a guard of about 28 us against an assembly
/// of about 6 us per node, over about 4 variants, so about 1.2 nodes per variant. The
/// value is rounded up to 4 to keep a round whose saving is of the same order as the
/// guard on the naive path, where the measurement found no win.
#[doc(hidden)]
pub const GUARD_SETUP: usize = 4;

/// The estimates for rule `r` this round, or `None` when the guard cannot run (an item
/// sub-query needs the naive path or has no join atom), so that the round is naive.
#[doc(hidden)]
pub fn semi_estimate<Cfg, L>(
    r: &SeqRule<Cfg, L>,
    full: &crate::index::IndexStore<Cfg>,
    delta: &crate::index::IndexStore<Cfg>,
    stats: &crate::schedule::IndexStats<Cfg::O>,
) -> Option<SemiEstimate>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let crate::resolve::RAtom::Collect { collect, .. } = r.query.atoms.first()? else {
        return None;
    };
    // Test support: a caller inside the round passes the plan its query already built.
    let plan: CollectPlan<Cfg::O, Cfg::Index, L> = collect.0.plans(stats);
    semi_estimate_with(r, full, delta, stats, &plan)
}

/// [`semi_estimate`] on an existing `Collect` plan. The plan is the one
/// `schedule_with_stats` built for the rule's query, so the estimate schedules nothing:
/// scheduling every item sub-query a second time per rule and round was measured in step
/// 6 as the estimate's whole cost.
fn semi_estimate_with<Cfg, L>(
    r: &SeqRule<Cfg, L>,
    full: &crate::index::IndexStore<Cfg>,
    delta: &crate::index::IndexStore<Cfg>,
    stats: &crate::schedule::IndexStats<Cfg::O>,
    plan: &CollectPlan<Cfg::O, Cfg::Index, L>,
) -> Option<SemiEstimate>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let Some(crate::resolve::RAtom::Collect { op, collect, .. }) = r.query.atoms.first() else {
        return None;
    };
    let spec = &collect.0;
    let mut guard = 0usize;
    for sq in spec.filters.iter().chain(&spec.ones) {
        if sq.every_class {
            continue;
        }
        let atoms = crate::saturate::join_atom_indices(&sq.query);
        if atoms.is_empty() || crate::saturate::needs_naive_match(&sq.query) {
            return None;
        }
        for &di in &atoms {
            // A variant costs its driver's rows plus the fixed cost of running it: the
            // plan is scheduled, the index is built, and the query is set up even when
            // the variant returns no row. Measured in step 6 (see `GUARD_SETUP`).
            guard = guard
                .saturating_add(variant_driver(&sq.query, &atoms, di, full, delta))
                .saturating_add(GUARD_SETUP);
        }
    }
    let nodes = full.nodes_by_op(*op).len();
    let delta_nodes = delta.nodes_by_op(*op).len();
    let fan = mean_fan(stats, *op);
    let naive_assembly = match plan.drive {
        Drive::Root => nodes,
        // With part 2, every node of the root operator is assembled, part 2's with empty
        // filters; without it, the candidates the driving rows reach.
        Drive::Filters if plan.part2 => nodes,
        Drive::Filters => plan
            .drivers
            .iter()
            .filter_map(|&g| spec.filters.get(g))
            .map(|f| est_rows(f, stats))
            .fold(0usize, usize::saturating_add)
            .saturating_mul(fan)
            .min(nodes),
    };
    // The candidates expected to pass the test: those in the delta, and the parents of
    // the classes the guard's rows reach.
    let passing = delta_nodes
        .saturating_add(guard.saturating_mul(fan))
        .min(nodes);
    let saving = match nodes {
        0 => 0,
        n => naive_assembly.saturating_mul(n - passing) / n,
    };
    Some(SemiEstimate {
        nodes,
        delta_nodes,
        guard,
        naive_assembly,
        saving,
    })
}

/// The `Collect` plan inside a scheduled query, the one its step will run.
fn collect_plan_of<Cfg: EGraphConfig, L: LitVal>(
    plan: &crate::schedule::QueryPlan<Cfg::O, Cfg::Index, L>,
) -> Option<&CollectPlan<Cfg::O, Cfg::Index, L>> {
    plan.steps.iter().find_map(|s| match s {
        crate::schedule::Step::Collect { plan, .. } => Some(&*plan.0),
        _ => None,
    })
}

/// The root operator's measured mean `by_contains` fan-out, rounded up, at least 1.
fn mean_fan<O: Eq + std::hash::Hash>(stats: &crate::schedule::IndexStats<O>, op: O) -> usize {
    match stats.fanouts.by_contains.get(&op) {
        // A float-to-integer cast saturates and maps NaN to 0, which `max(1)` lifts.
        Some(f) if f.is_finite() && *f > 1.0 => (f.ceil() as usize).max(1),
        _ => 1,
    }
}

/// `fan(A)`: the sum of the `by_contains` bucket lengths of `classes`, read and never
/// walked. A bucket holds every parent, of any operator, so this bounds the root
/// operator's parents from above; a hub class shows as a long bucket.
#[doc(hidden)]
pub fn fan_out<Cfg: EGraphConfig>(
    full: &crate::index::IndexStore<Cfg>,
    classes: impl Iterator<Item = Cfg::G>,
) -> usize
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    classes.fold(0usize, |acc, c| {
        acc.saturating_add(full.nodes_by_contains(c).len())
    })
}

type SeqRule<Cfg, L> =
    crate::collection::Rule<<Cfg as EGraphConfig>::O, <Cfg as EGraphConfig>::S, L>;

/// Every rule's matches on the round's snapshot, by its strategy, with their `:let`
/// values, in rule order; and the report of the matching.
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn match_rules<Cfg, L, M, const T: bool, const P: bool>(
    rules: &[&SeqRule<Cfg, L>],
    eg: &EGraph<Cfg, L, T, P>,
    index: &crate::index::IndexStore<Cfg>,
    stats: &crate::schedule::IndexStats<Cfg::O>,
    model: &M,
    globals: &GlobalCtx<Cfg::S, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
    delta: Option<&crate::saturate::RoundDelta<'_, Cfg>>,
    vindex: &VariantIndex<'_, Cfg>,
) -> Result<
    (
        Vec<(Cfg::G, usize, Match<Cfg>, Vec<L>)>,
        crate::collection::PassReport,
    ),
    String,
>
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    let mut report = crate::collection::PassReport::default();
    // (root node, rule, the match, its `:let` values)
    let mut plans: Vec<(Cfg::G, usize, Match<Cfg>, Vec<L>)> = Vec::new();
    for (ri, r) in rules.iter().enumerate() {
        let started = std::time::Instant::now();
        // The rule's query is scheduled once; the estimate reads that plan instead of
        // building a second one. Semi-enumerate is the one strategy that needs another
        // plan (the root drive, probed), so only it pays for a second scheduling.
        let naive_plan = crate::schedule::schedule_with_stats(&r.query, stats);
        let keep = match (delta, collect_plan_of::<Cfg, L>(&naive_plan)) {
            (Some(d), Some(cp)) => semi_strategy(r, eg, index, d, stats, globals, pool, cp, None),
            _ => None,
        };
        let plan = match &keep {
            Some(k) if k.exact.is_some() => schedule_for::<Cfg, L>(r, k, stats),
            _ => naive_plan,
        };
        // Semi-filter assembles a subset of naive's candidates (decision 4), checked
        // every round in a debug build.
        if keep.is_some() && cfg!(debug_assertions) {
            pool.collect_trace = Some((Vec::new(), Vec::new()));
        }
        let strategy = match &keep {
            None => "naive",
            Some(k) if k.exact.is_some() => "enumerate",
            Some(_) => "filter",
        };
        pool.collect_keep = keep.map(Box::new);
        crate::ematch::run_query_into(&plan, eg, vindex, globals, pool);
        pool.collect_keep = None;
        if let Some((offered, assembled)) = pool.collect_trace.take() {
            use crate::containers::DenseId;
            let offered: std::collections::HashSet<usize> =
                offered.iter().map(|n| n.to_usize()).collect();
            debug_assert!(
                assembled.iter().all(|n| offered.contains(&n.to_usize())),
                "{}: semi-filter assembled a node naive did not offer",
                r.name
            );
        }
        if let Some(dir) = drive_stats_dir() {
            record_drive(dir, r, &plan, index, pool, started.elapsed(), strategy);
        }
        harvest(r, ri, pool, eg, model, &mut plans, &mut report)?;
    }
    Ok((plans, report))
}

/// Match every rule on the round's snapshot `index`, then build every right-hand
/// side and merge it into its root's class. All guards are read before any
/// right-hand side is built, and the matches are applied in (root node, rule) order,
/// the order route 1's pass applies them in.
#[allow(clippy::too_many_arguments)]
pub fn apply_rules<Cfg, L, M, const T: bool, const P: bool>(
    rules: &[&SeqRule<Cfg, L>],
    eg: &mut EGraph<Cfg, L, T, P>,
    index: &crate::index::IndexStore<Cfg>,
    stats: &crate::schedule::IndexStats<Cfg::O>,
    model: &M,
    globals: &GlobalCtx<Cfg::S, Cfg::G>,
    pool: &mut MatchPool<Cfg>,
    // The round's delta under semi-naive saturation (`--use-semi-naive`), `None` under
    // naive. One switch covers every rule: with a delta, each sequence rule takes the
    // strategy its estimates choose (`semi_strategy`), naive among them.
    delta: Option<&crate::saturate::RoundDelta<'_, Cfg>>,
) -> Result<crate::collection::PassReport, String>
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    let vindex = VariantIndex::naive(index);
    // One row cache per call: every rule is matched on the same snapshot.
    pool.collect_rows = Some(RowCache::new());
    let matched = match_rules(
        rules, eg, index, stats, model, globals, pool, delta, &vindex,
    );
    pool.collect_rows = None;
    let (mut plans, mut report) = matched?;
    // Stable: a node's matches for one rule keep the assembly's order.
    plans.sort_by_key(|(n, ri, _, _)| (crate::containers::DenseId::to_usize(*n), *ri));
    for (root, ri, m, lets) in plans {
        let r = rules[ri];
        let new =
            match crate::seq_rhs::build(&r.seq_rhs, lets, &r.seq_shape, &m, eg, model, globals) {
                Ok(g) => g,
                // "§Edge cases 1": a right-hand side with no value does not fire.
                Err(e) if e == crate::seq_rhs::NO_FIRE => {
                    report.no_value += 1;
                    continue;
                }
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
        let merged = match r.rule_id {
            Some(rule_id) if P => eg
                .merge_justified(
                    new,
                    root,
                    crate::union_find::Justification::Rewrite { rule_id },
                )
                .is_some(),
            _ => eg.merge(new, root).is_some(),
        };
        if merged {
            report.changed += 1;
        }
    }
    Ok(report)
}

/// Test support: the relational engine's matches of `r` at node `id`, on a snapshot
/// of `eg` as it stands, rendered as `collection::matches_at` renders route 1's: a
/// class as `c<representative id>`, a literal or a multiplicity as its value, a
/// sequence as `[x, y]`, with the multiplicity columns `{name}:mult` under AC. A node
/// over the match bound gives no matches.
#[doc(hidden)]
pub fn matches_at<Cfg, L, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
    globals: &GlobalCtx<Cfg::S, Cfg::G>,
    r: &SeqRule<Cfg, L>,
    id: Cfg::G,
) -> Vec<std::collections::BTreeMap<String, String>>
where
    Cfg: EGraphConfig,
    L: LitVal,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    use crate::containers::DenseId;
    use crate::ematch::MatchView;
    let store = crate::index::IndexStore::build(eg);
    let vindex = VariantIndex::naive(&store);
    let stats = crate::schedule::IndexStats::from_index(&store);
    let plan = crate::schedule::schedule_with_stats(&r.query, &stats);
    let mut pool = MatchPool::new();
    crate::ematch::run_query_into(&plan, eg, &vindex, globals, &mut pool);
    let class = |g: Cfg::G| format!("c{}", crate::ematch::round_canon(&vindex, eg, g).to_usize());
    let list = |xs: Vec<String>| format!("[{}]", xs.join(", "));
    let Some(asm) = r.query_assembly() else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for j in 0..pool.len() {
        let row = pool.row(j);
        if row.get(r.root_var) != id {
            continue;
        }
        let mut env = std::collections::BTreeMap::new();
        let rest = |name: &str,
                    rr: RestRef,
                    env: &mut std::collections::BTreeMap<String, String>| {
            match rr {
                RestRef::Seq(v) => {
                    env.insert(
                        name.to_string(),
                        list(row.seq_slice(v).iter().map(|&g| class(g)).collect()),
                    );
                }
                RestRef::Set(v) => {
                    env.insert(
                        name.to_string(),
                        list(row.set_slice(v).iter().map(|&g| class(g)).collect()),
                    );
                }
                RestRef::Mset(v) => {
                    let cs = row.mset_slice(v);
                    env.insert(
                        name.to_string(),
                        list(cs.iter().map(|c| class(Cfg::mset_child_id(c))).collect()),
                    );
                    env.insert(
                        mult_column(name),
                        list(
                            cs.iter()
                                .map(|c| Cfg::mset_child_mult(c).to_string())
                                .collect(),
                        ),
                    );
                }
            }
        };
        for (f, (elems, cols)) in asm.spec.filters.iter().zip(&asm.layout.filters) {
            rest(&f.name, *elems, &mut env);
            for (name, col) in f.vars.iter().zip(cols) {
                let v = match col {
                    ColRef::Node(v) => list(row.seq_slice(*v).iter().map(|&g| class(g)).collect()),
                    ColRef::Lit(v) => list(
                        row.lit_seq_slice(*v)
                            .iter()
                            .map(|&l| eg.lits().get(l).to_string())
                            .collect(),
                    ),
                    ColRef::Mult(v) => list(
                        row.mset_slice(*v)
                            .iter()
                            .map(|c| Cfg::mset_child_mult(c).to_string())
                            .collect(),
                    ),
                };
                env.insert(name.clone(), v);
            }
        }
        for (name, rr) in &asm.layout.bare {
            rest(name, *rr, &mut env);
        }
        for (name, sr) in asm.spec.scalars.iter().zip(&asm.layout.scalars) {
            let v = match sr {
                ScalarRef::Node(v) => class(row.get(*v)),
                ScalarRef::Lit(v) => eg.lits().get(row.get_lit_val(*v)).to_string(),
                ScalarRef::Mult(v) => row.get_mult(*v).to_string(),
            };
            env.insert(name.clone(), v);
        }
        out.push(env);
    }
    out
}

/// Test support: `matches_at`'s matches, each with whether the rule fires on it (its
/// `:let`s have values and its `:when`s hold). A drive that drops part 2 may change the
/// match set, but must not change the matches that fire; this is what compares them.
#[doc(hidden)]
pub fn firing_at<Cfg, L, M, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
    globals: &GlobalCtx<Cfg::S, Cfg::G>,
    r: &SeqRule<Cfg, L>,
    id: Cfg::G,
    model: &M,
) -> Result<Vec<(std::collections::BTreeMap<String, String>, bool)>, String>
where
    Cfg: EGraphConfig,
    L: LitVal,
    M: crate::lit_model::LitModel<Value = L>,
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, T>,
{
    use crate::ematch::MatchView;
    let rendered = matches_at(eg, globals, r, id);
    // The same plan on the same snapshot, so the rows arrive in the same order.
    let store = crate::index::IndexStore::build(eg);
    let vindex = VariantIndex::naive(&store);
    let stats = crate::schedule::IndexStats::from_index(&store);
    let plan = crate::schedule::schedule_with_stats(&r.query, &stats);
    let mut pool = MatchPool::new();
    crate::ematch::run_query_into(&plan, eg, &vindex, globals, &mut pool);
    let mut fires = Vec::new();
    for j in 0..pool.len() {
        let row = pool.row(j);
        if row.get(r.root_var) != id {
            continue;
        }
        fires.push(crate::seq_rhs::prelude(&r.seq_rhs, &r.seq_shape, &row, eg, model)?.is_some());
    }
    if fires.len() != rendered.len() {
        return Err("internal: the two runs disagree on the match count".into());
    }
    Ok(rendered.into_iter().zip(fires).collect())
}
