// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Query scheduler: order variables and assign index constraints.
//!
//! Given a `ResolvedQuery` (OpId-based), produce a `QueryPlan` that
//! tells the execution engine which variable to bind next and how.

use crate::ast::{GlobalVarId, LitValVarId, MsetVarId, SeqVarId, SetVarId, VarId};
use crate::containers::{DenseId, IndexLike};
use crate::resolve::{MatchShape, PatVar, RAtom, RMult, ResolvedQuery};
use std::hash::Hash;

// ---------------------------------------------------------------------------
// Index lookups — each produces a SortedVec<G> for leapfrog
// ---------------------------------------------------------------------------

/// `I` is the child-position word: [`EGraphConfig::Index`], the same width the
/// e-graph indexes its child pool with. A position is an offset into one node's
/// children, so its range is the node's arity, and a variadic node's arity is a
/// span in that pool — bounded by `I` and by nothing narrower. Hard-coding `u32`
/// here would cap a 63-bit session's node arity at 2^32 children, and the cap
/// would be reached silently: the counter in [`IndexStore::build`] wrapped, and
/// the child at position 2^32 landed in bucket 0, where it would match patterns
/// written for the first argument.
///
/// [`EGraphConfig::Index`]: crate::config::EGraphConfig::Index
/// [`IndexStore::build`]: crate::index::IndexStore::build
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IndexLookup<O, I> {
    ByOp { op: O },
    ByChildPos { child: PatVar, pos: I },
    ByRepr { repr: VarId },
    ByContains { child: PatVar },
}

// ---------------------------------------------------------------------------
// Execution steps
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step<O, I, V> {
    Join {
        target: VarId,
        lookups: Vec<IndexLookup<O, I>>,
        /// Stable atom index in the compile-time numbering. Bridges the
        /// fixed atom order (which defines semi-naive variants) to the
        /// dynamic execution order chosen by the scheduler. Not used by
        /// the naive matcher; consumed by semi-naive variant dispatch.
        atom_id: usize,
    },
    ExtractChild {
        target: VarId,
        parent: VarId,
        /// Child position, `I`-wide for the same reason as
        /// [`IndexLookup::ByChildPos`]: it is read back through
        /// `EGraph::child_at`, which offsets into the node's span in the child pool.
        pos: I,
    },
    CheckChildEq {
        parent: VarId,
        pos: I,
        expected: PatVar,
    },
    CheckEq {
        a: VarId,
        b: VarId,
    },
    CheckEqGlobal {
        local: VarId,
        global: GlobalVarId,
    },
    CopyBinding {
        target: VarId,
        other: VarId,
    },
    ExpandA {
        node: VarId,
        children: Vec<PatVar>,
        pre: Option<SeqVarId>,
        suf: Option<SeqVarId>,
    },
    DecomposeAC {
        node: VarId,
        elems: Vec<(PatVar, RMult)>,
        rest: Option<MsetVarId>,
        idempotent: bool,
    },
    DecomposeACI {
        node: VarId,
        elems: Vec<PatVar>,
        rest: Option<SetVarId>,
    },
    ExtractLitVal {
        node: VarId,
        val: LitValVarId,
    },
    /// Keep the match only if `node`'s literal payload equals `value`. The constant
    /// counterpart of [`Step::ExtractLitVal`]: that one binds the payload to a pattern
    /// variable, this one pins it to a literal written in the pattern.
    CheckLit {
        node: VarId,
        value: V,
    },
}

#[derive(Clone, Debug)]
pub struct QueryPlan<O, I, V> {
    pub steps: Vec<Step<O, I, V>>,
    pub shape: MatchShape,
}

// ---------------------------------------------------------------------------
// Stats
// ---------------------------------------------------------------------------

pub struct IndexStats<O: Eq + Hash> {
    /// Per-op driver-scan cardinality (`|by_op[op]|`). The base estimate for an
    /// atom when no per-atom override is present — correct for naive matching,
    /// where every atom of an op reads the same full bucket.
    pub op_card: std::collections::HashMap<O, usize>,
    /// Per-atom (`atom_id`) driver-scan cardinality, overriding `op_card` for
    /// that atom. Needed for semi-naive: an atom's base cardinality is set by
    /// its **mode** (delta / full / full∖delta), which is per-atom, not per-op —
    /// two atoms with the same op can have different modes in one flavor (e.g.
    /// `(f (f x y) z)` variant 1: atom 0 is full∖delta, atom 1 is delta, both
    /// op `f`). `op_card` cannot represent that; `atom_card` can.
    pub atom_card: std::collections::HashMap<usize, usize>,
}

impl<O: Eq + Hash> Default for IndexStats<O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: Eq + Hash> IndexStats<O> {
    pub fn new() -> Self {
        Self {
            op_card: std::collections::HashMap::new(),
            atom_card: std::collections::HashMap::new(),
        }
    }
}

impl<O: Eq + Hash + Copy> IndexStats<O> {
    pub fn from_index<Cfg>(index: &crate::index::IndexStore<Cfg>) -> Self
    where
        Cfg: crate::config::EGraphConfig<O = O>,
        crate::canon::MSetCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
    {
        Self {
            op_card: index.by_op.iter().map(|(&op, v)| (op, v.len())).collect(),
            atom_card: std::collections::HashMap::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Scheduler
// ---------------------------------------------------------------------------

/// A child position in the plan's index word.
///
/// The argument is a *pattern's* arity, authored in a rewrite rule, so in practice a
/// handful — but the value is compared against and used to offset into positions the
/// e-graph assigns to real nodes ([`IndexStore::build`], [`EGraph::child_at`]), whose
/// range is the child pool's. Narrowing it silently would probe or read the wrong
/// argument, so it is checked rather than cast.
///
/// [`IndexStore::build`]: crate::index::IndexStore::build
/// [`EGraph::child_at`]: crate::egraph::EGraph::child_at
fn child_pos<I: IndexLike>(pos: usize) -> I {
    I::try_from_usize(pos)
        .expect("pattern child position exceeds EGraphConfig::Index; configure a wider index word")
}

fn pv_is_bound(pv: &PatVar, bound: &[bool]) -> bool {
    match pv {
        PatVar::Local(vid) => bound[vid.idx()],
        PatVar::Global(_) => true,
    }
}

fn pv_mark_bound(pv: &PatVar, bound: &mut [bool]) {
    if let PatVar::Local(vid) = pv {
        bound[vid.idx()] = true;
    }
}

/// Base driver-scan cardinality for an atom: its per-atom override
/// (`atom_card[atom_id]`, set per semi-naive flavor) if present, else the
/// per-op bucket size (`op_card[op]`, the naive default).
fn base_card<O: Eq + Hash>(op: &O, atom_id: usize, stats: &IndexStats<O>) -> usize {
    stats
        .atom_card
        .get(&atom_id)
        .copied()
        .or_else(|| stats.op_card.get(op).copied())
        .unwrap_or(usize::MAX)
}

/// Halve `base` once per bound key, modelling each bound child/element as an
/// index intersection that narrows the driver. Mirrors the discount the join
/// actually applies: `Plain`/`AExact` intersect `by_child_pos` per bound child;
/// the variadic atoms (A*/AC*/ACI*) intersect `by_contains` per bound element
/// (see `emit_variadic_join`). Without this, a fully-bound variadic atom is
/// mis-costed as a full `by_op` scan and the scheduler may refuse to drive from
/// it even though `by_contains` makes it the cheapest atom.
fn cost_discounted<O: Eq + Hash>(
    op: &O,
    atom_id: usize,
    n_bound: usize,
    stats: &IndexStats<O>,
) -> usize {
    base_card(op, atom_id, stats) >> n_bound.min(16)
}

fn estimate_cost<O: DenseId + Hash + Copy, S, V>(
    atom: &RAtom<O, S, V>,
    atom_id: usize,
    bound: &[bool],
    stats: &IndexStats<O>,
) -> usize {
    let bound_count = |pvs: &[PatVar]| pvs.iter().filter(|p| pv_is_bound(p, bound)).count();
    match atom {
        RAtom::Plain { op, children, .. } | RAtom::AExact { op, children, .. } => {
            cost_discounted(op, atom_id, bound_count(children), stats)
        }
        // Variadic atoms narrow via `by_contains` per bound element, exactly
        // like Plain's `by_child_pos` — so apply the same per-bound discount.
        RAtom::APrefix { op, fixed, .. }
        | RAtom::ASuffix { op, fixed, .. }
        | RAtom::ABoth { op, fixed, .. } => cost_discounted(op, atom_id, bound_count(fixed), stats),
        RAtom::ACExact { op, elems, .. } | RAtom::ACSub { op, elems, .. } => {
            let nb = elems.iter().filter(|(p, _)| pv_is_bound(p, bound)).count();
            cost_discounted(op, atom_id, nb, stats)
        }
        RAtom::ACIExact { op, elems, .. } | RAtom::ACISub { op, elems, .. } => {
            cost_discounted(op, atom_id, bound_count(elems), stats)
        }
        RAtom::Lit { op, .. } | RAtom::LitBind { op, .. } => base_card(op, atom_id, stats),
        RAtom::Eq(..) | RAtom::EqGlobal(..) => 0,
    }
}

pub fn schedule<O: DenseId + Hash + Copy, S: DenseId + Copy, V: Clone, I: IndexLike>(
    rq: &ResolvedQuery<O, S, V>,
) -> QueryPlan<O, I, V> {
    schedule_with_stats(rq, &IndexStats::new())
}

pub fn schedule_with_stats<O: DenseId + Hash + Copy, S: DenseId + Copy, V: Clone, I: IndexLike>(
    rq: &ResolvedQuery<O, S, V>,
    stats: &IndexStats<O>,
) -> QueryPlan<O, I, V> {
    let mut bound = vec![false; rq.shape.num_vars()];
    let mut steps = Vec::new();
    let mut used = vec![false; rq.atoms.len()];

    loop {
        // Eager pass: Eq, Lit, already-bound nodes.
        let mut progress = true;
        while progress {
            progress = false;
            for ai in 0..rq.atoms.len() {
                if used[ai] {
                    continue;
                }
                if let Some(eager) = try_eager_lower(&rq.atoms[ai], ai, &mut bound) {
                    steps.extend(eager);
                    used[ai] = true;
                    progress = true;
                }
            }
        }

        // Pick cheapest unprocessed atom.
        let best = (0..rq.atoms.len())
            .filter(|&ai| {
                !used[ai] && !matches!(&rq.atoms[ai], RAtom::Eq(..) | RAtom::EqGlobal(..))
            })
            .min_by_key(|&ai| estimate_cost(&rq.atoms[ai], ai, &bound, stats));

        let Some(ai) = best else { break };
        emit_atom(&rq.atoms[ai], ai, &mut bound, &mut steps);
        used[ai] = true;
    }

    QueryPlan {
        steps,
        shape: rq.shape.clone(),
    }
}

fn emit_read_children<O: DenseId + Hash + Copy, S, V, I: IndexLike>(
    atom: &RAtom<O, S, V>,
    bound: &mut [bool],
    steps: &mut Vec<Step<O, I, V>>,
) {
    if let RAtom::Plain { node, children, .. } = atom {
        for (pos, &cv) in children.iter().enumerate() {
            if !pv_is_bound(&cv, bound) {
                let PatVar::Local(vid) = cv else {
                    unreachable!()
                };
                steps.push(Step::ExtractChild {
                    target: vid,
                    parent: *node,
                    pos: child_pos::<I>(pos),
                });
                pv_mark_bound(&cv, bound);
            } else {
                steps.push(Step::CheckChildEq {
                    parent: *node,
                    pos: child_pos::<I>(pos),
                    expected: cv,
                });
            }
        }
    }
}

fn emit_atom<O: DenseId + Hash + Copy, S, V: Clone, I: IndexLike>(
    atom: &RAtom<O, S, V>,
    atom_id: usize,
    bound: &mut [bool],
    steps: &mut Vec<Step<O, I, V>>,
) {
    match atom {
        RAtom::Plain { node, op, children } => {
            let mut lookups = vec![IndexLookup::ByOp { op: *op }];
            for (pos, &cv) in children.iter().enumerate() {
                if pv_is_bound(&cv, bound) {
                    lookups.push(IndexLookup::ByChildPos {
                        child: cv,
                        pos: child_pos::<I>(pos),
                    });
                }
            }
            steps.push(Step::Join {
                target: *node,
                lookups,
                atom_id,
            });
            bound[(*node).idx()] = true;
            for (pos, &cv) in children.iter().enumerate() {
                if !pv_is_bound(&cv, bound) {
                    let PatVar::Local(vid) = cv else {
                        unreachable!()
                    };
                    steps.push(Step::ExtractChild {
                        target: vid,
                        parent: *node,
                        pos: child_pos::<I>(pos),
                    });
                    pv_mark_bound(&cv, bound);
                } else {
                    steps.push(Step::CheckChildEq {
                        parent: *node,
                        pos: child_pos::<I>(pos),
                        expected: cv,
                    });
                }
            }
        }
        RAtom::Lit {
            node, op, value, ..
        } => {
            if !bound[(*node).idx()] {
                steps.push(Step::Join {
                    target: *node,
                    lookups: vec![IndexLookup::ByOp { op: *op }],
                    atom_id,
                });
                bound[(*node).idx()] = true;
            }
            steps.push(Step::CheckLit {
                node: *node,
                value: value.clone(),
            });
        }
        RAtom::LitBind { node, op, val } => {
            if !bound[(*node).idx()] {
                steps.push(Step::Join {
                    target: *node,
                    lookups: vec![IndexLookup::ByOp { op: *op }],
                    atom_id,
                });
                bound[(*node).idx()] = true;
            }
            steps.push(Step::ExtractLitVal {
                node: *node,
                val: *val,
            });
        }
        RAtom::Eq(..) | RAtom::EqGlobal(..) => {}
        RAtom::AExact { node, op, children } => {
            emit_variadic_join(node, *op, atom_id, children, bound, steps);
            steps.push(Step::ExpandA {
                node: *node,
                children: children.clone(),
                pre: None,
                suf: None,
            });
            for &cv in children {
                pv_mark_bound(&cv, bound);
            }
        }
        RAtom::APrefix {
            node,
            op,
            pre,
            fixed,
        } => {
            emit_variadic_join(node, *op, atom_id, fixed, bound, steps);
            steps.push(Step::ExpandA {
                node: *node,
                children: fixed.clone(),
                pre: Some(*pre),
                suf: None,
            });
            for &cv in fixed {
                pv_mark_bound(&cv, bound);
            }
        }
        RAtom::ASuffix {
            node,
            op,
            fixed,
            suf,
        } => {
            emit_variadic_join(node, *op, atom_id, fixed, bound, steps);
            steps.push(Step::ExpandA {
                node: *node,
                children: fixed.clone(),
                pre: None,
                suf: Some(*suf),
            });
            for &cv in fixed {
                pv_mark_bound(&cv, bound);
            }
        }
        RAtom::ABoth {
            node,
            op,
            pre,
            fixed,
            suf,
        } => {
            emit_variadic_join(node, *op, atom_id, fixed, bound, steps);
            steps.push(Step::ExpandA {
                node: *node,
                children: fixed.clone(),
                pre: Some(*pre),
                suf: Some(*suf),
            });
            for &cv in fixed {
                pv_mark_bound(&cv, bound);
            }
        }
        RAtom::ACExact { node, op, elems } => {
            let evs: Vec<PatVar> = elems.iter().map(|(ev, _)| *ev).collect();
            emit_variadic_join(node, *op, atom_id, &evs, bound, steps);
            steps.push(Step::DecomposeAC {
                node: *node,
                elems: elems.clone(),
                rest: None,
                idempotent: false,
            });
            for (ev, _) in elems {
                pv_mark_bound(ev, bound);
            }
        }
        RAtom::ACSub {
            node,
            op,
            elems,
            rest,
        } => {
            let evs: Vec<PatVar> = elems.iter().map(|(ev, _)| *ev).collect();
            emit_variadic_join(node, *op, atom_id, &evs, bound, steps);
            steps.push(Step::DecomposeAC {
                node: *node,
                elems: elems.clone(),
                rest: Some(*rest),
                idempotent: false,
            });
            for (ev, _) in elems {
                pv_mark_bound(ev, bound);
            }
        }
        RAtom::ACIExact { node, op, elems } => {
            emit_variadic_join(node, *op, atom_id, elems, bound, steps);
            steps.push(Step::DecomposeACI {
                node: *node,
                elems: elems.clone(),
                rest: None,
            });
            for &ev in elems {
                pv_mark_bound(&ev, bound);
            }
        }
        RAtom::ACISub {
            node,
            op,
            elems,
            rest,
        } => {
            emit_variadic_join(node, *op, atom_id, elems, bound, steps);
            steps.push(Step::DecomposeACI {
                node: *node,
                elems: elems.clone(),
                rest: Some(*rest),
            });
            for &ev in elems {
                pv_mark_bound(&ev, bound);
            }
        }
    }
}

/// Try to lower an atom that is *forced or free* given the current bindings —
/// the "eager pass" cases that cost nothing to resolve and only shrink the
/// problem: `Eq`/`EqGlobal` constraints between bound vars, and
/// `Lit`/`LitBind`/`Plain` whose node var is already bound (re-join within its
/// class). Returns `Some(steps)` and marks newly-bound vars if the atom is
/// eagerly resolvable now; `None` if it must wait for cost-based selection
/// (an unbound scanning atom). Single source of truth shared by the static
/// scheduler's eager pass and the runtime-adaptive matcher.
pub(crate) fn try_eager_lower<O: DenseId + Hash + Copy, S, V: Clone, I: IndexLike>(
    atom: &RAtom<O, S, V>,
    atom_id: usize,
    bound: &mut [bool],
) -> Option<Vec<Step<O, I, V>>> {
    let mut steps = Vec::new();
    match atom {
        RAtom::Eq(a, b) => {
            if bound[(*a).idx()] && bound[(*b).idx()] {
                steps.push(Step::CheckEq { a: *a, b: *b });
            } else if bound[(*a).idx()] {
                steps.push(Step::CopyBinding {
                    target: *b,
                    other: *a,
                });
                bound[(*b).idx()] = true;
            } else if bound[(*b).idx()] {
                steps.push(Step::CopyBinding {
                    target: *a,
                    other: *b,
                });
                bound[(*a).idx()] = true;
            } else {
                return None;
            }
        }
        RAtom::EqGlobal(local, global) if bound[(*local).idx()] => {
            steps.push(Step::CheckEqGlobal {
                local: *local,
                global: *global,
            });
        }
        RAtom::Lit {
            node, op, value, ..
        } if bound[(*node).idx()] => {
            steps.push(Step::Join {
                target: *node,
                lookups: vec![
                    IndexLookup::ByRepr { repr: *node },
                    IndexLookup::ByOp { op: *op },
                ],
                atom_id,
            });
            steps.push(Step::CheckLit {
                node: *node,
                value: value.clone(),
            });
        }
        RAtom::LitBind { node, op, val } if bound[(*node).idx()] => {
            steps.push(Step::Join {
                target: *node,
                lookups: vec![
                    IndexLookup::ByRepr { repr: *node },
                    IndexLookup::ByOp { op: *op },
                ],
                atom_id,
            });
            steps.push(Step::ExtractLitVal {
                node: *node,
                val: *val,
            });
        }
        RAtom::Plain { node, op, .. } if bound[(*node).idx()] => {
            steps.push(Step::Join {
                target: *node,
                lookups: vec![
                    IndexLookup::ByRepr { repr: *node },
                    IndexLookup::ByOp { op: *op },
                ],
                atom_id,
            });
            emit_read_children(atom, bound, &mut steps);
        }
        _ => return None,
    }
    Some(steps)
}

fn emit_variadic_join<O: DenseId + Hash + Copy, I: IndexLike, V>(
    node: &VarId,
    op: O,
    atom_id: usize,
    elems: &[PatVar],
    bound: &mut [bool],
    steps: &mut Vec<Step<O, I, V>>,
) {
    if !bound[(*node).idx()] {
        // Drive from `by_op[op]`, intersected with `by_contains[e]` for every
        // element `e` already bound. A matching variadic node MUST contain each
        // bound element, so `by_contains[e]` is a sound (membership-only) filter
        // — the following DecomposeAC/ExpandA/DecomposeACI does the precise
        // multiplicity/position check. This narrows the driver to the few
        // parents containing the bound element instead of scanning the whole
        // `by_op` bucket — the variadic analogue of `Plain`'s `ByChildPos`.
        let mut lookups = vec![IndexLookup::ByOp { op }];
        for &pv in elems {
            if pv_is_bound(&pv, bound) {
                lookups.push(IndexLookup::ByContains { child: pv });
            }
        }
        steps.push(Step::Join {
            target: *node,
            lookups,
            atom_id,
        });
        bound[(*node).idx()] = true;
    } else {
        // The node var is already bound — e.g. extracted as an enclosing
        // atom's child via `ExtractChild`. Re-join within its class
        // (`ByRepr ∩ ByOp`), exactly as the `Plain` bound-node path does, so
        // this atom still emits a `Step::Join` carrying `atom_id`. Without it,
        // the semi-naive variant mode (delta / full∖delta / full) — which is
        // realized *only* on `Step::Join` (see `ematch::run_join`) — would
        // never be applied to a parent-driven variadic atom, letting the
        // parent-driven variant re-discover matches the delta-driven variants
        // already own. In the naive path this re-join is a no-op intersection
        // (the node re-selects itself within its own class).
        steps.push(Step::Join {
            target: *node,
            lookups: vec![
                IndexLookup::ByRepr { repr: *node },
                IndexLookup::ByOp { op },
            ],
            atom_id,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{OpId, SortId};
    use crate::lit_model::LitModel;
    use crate::literal::{LitValStore, NiraLitVal, NiraModel};
    use crate::nodes::LitValId;
    use crate::registry::{OpRegistry, SortRegistry};
    use crate::resolve::MatchShape;
    use crate::resolve::resolve;
    use crate::sortcheck::flatten_surface as flatten;
    use crate::test_helpers::parse_pattern;

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
        let mut ops = OpRegistry::new();
        ops.register_builtins(&model, &sorts);
        ops.register("f", &[e, e], e);
        ops.register("g", &[e], e);
        ops.register("h", &[e, e], e);
        ops.register_a("concat", e, e, crate::registry::AssocDir::Right);
        ops.register_mset("add", e, e);
        ops.register_set("union", e, e);
        let ibig = sorts.id_by_name("IBig").expect("IBig builtin");
        ops.register("ILit", &[ibig], e);
        (ops, sorts, LitValStore::new())
    }

    fn do_plan(src: &str) -> (QueryPlan<OpId, u32, NiraLitVal>, MatchShape) {
        let (ops, sorts, _) = setup();
        let model = NiraModel;
        let pat = parse_pattern(src);
        let fq = flatten(&[pat], &ops).unwrap();
        let rq = resolve(
            &fq,
            &ops,
            &sorts,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        (schedule(&rq), rq.shape)
    }

    fn do_plan_multi(srcs: &[&str]) -> (QueryPlan<OpId, u32, NiraLitVal>, MatchShape) {
        let (ops, sorts, _) = setup();
        let model = NiraModel;
        let pats: Vec<_> = srcs.iter().map(|s| parse_pattern(s)).collect();
        let fq = flatten(&pats, &ops).unwrap();
        let rq = resolve(
            &fq,
            &ops,
            &sorts,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        (schedule(&rq), rq.shape)
    }

    fn do_plan_with_stats(
        srcs: &[&str],
        card: &[(&str, usize)],
    ) -> (QueryPlan<OpId, u32, NiraLitVal>, MatchShape) {
        let (ops, sorts, _) = setup();
        let model = NiraModel;
        let pats: Vec<_> = srcs.iter().map(|s| parse_pattern(s)).collect();
        let fq = flatten(&pats, &ops).unwrap();
        let rq = resolve(
            &fq,
            &ops,
            &sorts,
            &model,
            &crate::resolve::GlobalCtx::<_, ()>::new(),
        )
        .unwrap();
        let mut stats = IndexStats::new();
        for &(name, c) in card {
            let op_id = ops.id_by_name(name).unwrap();
            stats.op_card.insert(op_id, c);
        }
        (schedule_with_stats(&rq, &stats), rq.shape)
    }

    #[test]
    fn plain_flat() {
        let (qp, _) = do_plan("(f x y)");
        assert_eq!(qp.steps.len(), 3);
        assert!(matches!(&qp.steps[0], Step::Join { lookups, .. }
            if matches!(&lookups[0], IndexLookup::ByOp { .. })));
        assert!(matches!(&qp.steps[1], Step::ExtractChild { pos: 0, .. }));
        assert!(matches!(&qp.steps[2], Step::ExtractChild { pos: 1, .. }));
    }

    #[test]
    fn nested() {
        let (qp, _) = do_plan("(f x (g y))");
        let join_count = qp
            .steps
            .iter()
            .filter(|s| matches!(s, Step::Join { .. }))
            .count();
        assert_eq!(join_count, 2);
    }

    #[test]
    fn multi_atom_shared_var() {
        let (qp, vars) = do_plan_multi(&["(f x y)", "(g y)"]);
        let y = vars.find_var("y").unwrap();
        // g has 1 arg, so after f binds y, g-join should use ByChildPos(y, 0)
        let g_join = qp.steps.iter().find(|s| match s {
            Step::Join { lookups, .. } => lookups.len() > 1,
            _ => false,
        });
        assert!(g_join.is_some());
        if let Step::Join { lookups, .. } = g_join.unwrap() {
            assert!(
                lookups
                    .iter()
                    .any(|l| matches!(l, IndexLookup::ByChildPos { child, pos: 0 } if *child == PatVar::Local(y)))
            );
        }
    }

    /// A ground literal in a pattern must compile to a *satisfiable* plan: a join that
    /// actually reads an index, followed by the payload check that pins the value.
    /// Regression for the dead-literal defect — the literal atom used to emit
    /// `Join { lookups: [] }`, and an empty lookup vector makes both matcher engines
    /// abandon the query, so the whole rule was inert.
    #[test]
    fn literal_atom_joins_and_checks_payload() {
        let (qp, _) = do_plan("(f (ILit 42) x)");
        for step in &qp.steps {
            if let Step::Join { lookups, .. } = step {
                assert!(
                    !lookups.is_empty(),
                    "a join with no lookups yields no candidates: {qp:?}"
                );
            }
        }
        let checks: Vec<_> = qp
            .steps
            .iter()
            .filter(|s| matches!(s, Step::CheckLit { .. }))
            .collect();
        assert_eq!(checks.len(), 1, "expected one payload check in {qp:?}");
        assert!(
            matches!(checks[0], Step::CheckLit { value, .. } if value.to_string() == "42"),
            "payload check does not carry the pattern's literal: {qp:?}"
        );
    }

    #[test]
    fn nonlinear_check_eq() {
        let (qp, _) = do_plan("(f x x)");
        assert!(
            qp.steps
                .iter()
                .any(|s| matches!(s, Step::CheckChildEq { .. }))
        );
    }

    #[test]
    fn ac_subset() {
        let (qp, _) = do_plan("(add x:2 ..rest)");
        assert!(qp.steps.iter().any(|s| matches!(
            s,
            Step::DecomposeAC {
                rest: Some(_),
                idempotent: false,
                ..
            }
        )));
    }

    #[test]
    fn aci_subset() {
        let (qp, _) = do_plan("(union x y ..rest)");
        assert!(
            qp.steps
                .iter()
                .any(|s| matches!(s, Step::DecomposeACI { rest: Some(_), .. }))
        );
    }

    #[test]
    fn a_prefix() {
        let (qp, _) = do_plan("(concat ..pre x y)");
        assert!(qp.steps.iter().any(|s| matches!(
            s,
            Step::ExpandA {
                pre: Some(_),
                suf: None,
                ..
            }
        )));
    }

    #[test]
    fn selectivity_picks_rarest() {
        let (qp, _) = do_plan_with_stats(&["(f x (g y))"], &[("f", 10_000), ("g", 10)]);
        // First Join should be for g (rarest)
        let first_join = qp
            .steps
            .iter()
            .find(|s| matches!(s, Step::Join { .. }))
            .unwrap();
        if let Step::Join { lookups, .. } = first_join {
            let (ops, _, _) = setup();
            let g_id = ops.id_by_name("g").unwrap();
            assert!(
                lookups
                    .iter()
                    .any(|l| matches!(l, IndexLookup::ByOp { op } if *op == g_id))
            );
        }
    }

    #[test]
    fn selectivity_three_atoms() {
        let (qp, _) = do_plan_with_stats(
            &["(f x y)", "(g y)", "(h y w)"],
            &[("f", 10_000), ("g", 500), ("h", 5)],
        );
        let (ops, _, _) = setup();
        let join_ops: Vec<OpId> = qp
            .steps
            .iter()
            .filter_map(|s| match s {
                Step::Join { lookups, .. } => lookups.iter().find_map(|l| match l {
                    IndexLookup::ByOp { op } => Some(*op),
                    _ => None,
                }),
                _ => None,
            })
            .collect();
        let h = ops.id_by_name("h").unwrap();
        let g = ops.id_by_name("g").unwrap();
        let f = ops.id_by_name("f").unwrap();
        assert_eq!(join_ops, [h, g, f]);
    }

    #[test]
    fn bound_child_reduces_cost() {
        let (qp, _) = do_plan_with_stats(&["(f x y)", "(h y z)"], &[("f", 1000), ("h", 1000)]);
        let second_join = qp
            .steps
            .iter()
            .filter(|s| matches!(s, Step::Join { .. }))
            .nth(1);
        if let Some(Step::Join { lookups, .. }) = second_join {
            assert!(
                lookups
                    .iter()
                    .any(|l| matches!(l, IndexLookup::ByChildPos { .. }))
            );
        }
    }

    /// A bound element discounts a variadic atom's cost, just as a bound child
    /// discounts a `Plain` atom — so `estimate_cost` reflects the `by_contains`
    /// narrowing that `emit_variadic_join` performs. Without the discount a
    /// fully-bound variadic atom would be mis-costed as a full `by_op` scan.
    #[test]
    fn bound_element_discounts_variadic_cost() {
        let (ops, _, _) = setup();
        let add = ops.id_by_name("add").unwrap();
        let mut stats = IndexStats::<OpId>::new();
        stats.op_card.insert(add, 1000);

        // ACSub `(add x:1 ..rest)` with one element var `x` (VarId 0).
        let atom = RAtom::<OpId, SortId, NiraLitVal>::ACSub {
            node: VarId::new(1),
            op: add,
            elems: vec![(PatVar::Local(VarId::new(0)), RMult::Exact(1))],
            rest: crate::ast::MsetVarId::new(0),
        };

        // x unbound → full op cardinality. (atom_id 0; no per-atom override,
        // so it falls back to op_card.)
        let bound_none = [false, false];
        assert_eq!(estimate_cost(&atom, 0, &bound_none, &stats), 1000);

        // x bound → discounted (halved per bound element), reflecting the
        // `by_contains[x]` intersection the join will apply.
        let bound_x = [true, false];
        let cost_bound = estimate_cost(&atom, 0, &bound_x, &stats);
        assert!(
            cost_bound < 1000,
            "binding an element must discount a variadic atom's cost, got {cost_bound}"
        );
        assert_eq!(cost_bound, 500, "one bound element halves the estimate");
    }

    /// End-to-end: with a bound element, the scheduler must be willing to drive
    /// from a high-cardinality variadic atom. `(g x)` binds x cheaply; the
    /// `add` atom has 100× g's cardinality, but once x is bound its discounted
    /// cost lets `by_contains[x]` carry the join (lookups include ByContains).
    #[test]
    fn scheduler_drives_variadic_from_bound_element() {
        let (qp, vars) =
            do_plan_with_stats(&["(g x)", "(add x ..rest)"], &[("g", 10), ("add", 1000)]);
        let x = vars.find_var("x").unwrap();
        // The add-atom join must intersect by_contains on the bound element x.
        let has_by_contains = qp.steps.iter().any(|s| match s {
            Step::Join { lookups, .. } => lookups.iter().any(
                |l| matches!(l, IndexLookup::ByContains { child } if *child == PatVar::Local(x)),
            ),
            _ => false,
        });
        assert!(
            has_by_contains,
            "variadic atom with a bound element should drive via ByContains: {:?}",
            qp.steps
        );
    }
}
