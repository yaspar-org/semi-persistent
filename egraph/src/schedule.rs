// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Query scheduler: order variables and assign index constraints.
//!
//! Given a `ResolvedQuery` (OpId-based), produce a `QueryPlan` that
//! tells the execution engine which variable to bind next and how.

use crate::ast::{GlobalVarId, LitValVarId, MsetVarId, SeqVarId, SetVarId, VarId};
use crate::containers::DenseId;
use crate::resolve::{MatchShape, PatVar, RAtom, RMult, ResolvedQuery};
use std::hash::Hash;

// ---------------------------------------------------------------------------
// Index lookups — each produces a SortedVec<G> for leapfrog
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IndexLookup<O> {
    ByOp { op: O },
    ByChildPos { child: PatVar, pos: u32 },
    ByRepr { repr: VarId },
    ByContains { child: PatVar },
}

// ---------------------------------------------------------------------------
// Execution steps
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step<O> {
    Join {
        target: VarId,
        lookups: Vec<IndexLookup<O>>,
    },
    ExtractChild {
        target: VarId,
        parent: VarId,
        pos: u32,
    },
    CheckChildEq {
        parent: VarId,
        pos: u32,
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
}

#[derive(Clone, Debug)]
pub struct QueryPlan<O> {
    pub steps: Vec<Step<O>>,
    pub shape: MatchShape,
}

// ---------------------------------------------------------------------------
// Stats
// ---------------------------------------------------------------------------

pub struct IndexStats<O: Eq + Hash> {
    pub op_card: std::collections::HashMap<O, usize>,
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
        }
    }
}

impl<O: Eq + Hash + Copy> IndexStats<O> {
    pub fn from_index<Cfg>(index: &crate::index::IndexStore<Cfg>) -> Self
    where
        Cfg: crate::config::EGraphConfig<O = O>,
        crate::canon::ACCanon: crate::canon::VarCanon<Cfg::G, Cfg::C>,
    {
        Self {
            op_card: index.by_op.iter().map(|(&op, v)| (op, v.len())).collect(),
        }
    }
}

// ---------------------------------------------------------------------------
// Scheduler
// ---------------------------------------------------------------------------

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

fn estimate_cost<O: DenseId + Hash + Copy, S, V>(
    atom: &RAtom<O, S, V>,
    bound: &[bool],
    stats: &IndexStats<O>,
) -> usize {
    match atom {
        RAtom::Plain { op, children, .. } | RAtom::AExact { op, children, .. } => {
            let base = stats.op_card.get(op).copied().unwrap_or(usize::MAX);
            let bc = children.iter().filter(|c| pv_is_bound(c, bound)).count();
            base >> bc.min(16)
        }
        RAtom::APrefix { op, .. }
        | RAtom::ASuffix { op, .. }
        | RAtom::ABoth { op, .. }
        | RAtom::ACExact { op, .. }
        | RAtom::ACSub { op, .. }
        | RAtom::ACIExact { op, .. }
        | RAtom::ACISub { op, .. } => stats.op_card.get(op).copied().unwrap_or(usize::MAX),
        RAtom::Lit { .. } => 1,
        RAtom::LitBind { op, .. } => stats.op_card.get(op).copied().unwrap_or(usize::MAX),
        RAtom::Eq(..) | RAtom::EqGlobal(..) => 0,
    }
}

pub fn schedule<O: DenseId + Hash + Copy, S: DenseId + Copy, V>(
    rq: &ResolvedQuery<O, S, V>,
) -> QueryPlan<O> {
    schedule_with_stats(rq, &IndexStats::new())
}

pub fn schedule_with_stats<O: DenseId + Hash + Copy, S: DenseId + Copy, V>(
    rq: &ResolvedQuery<O, S, V>,
    stats: &IndexStats<O>,
) -> QueryPlan<O> {
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
                match &rq.atoms[ai] {
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
                            continue;
                        }
                        used[ai] = true;
                        progress = true;
                    }
                    RAtom::EqGlobal(local, global) if bound[(*local).idx()] => {
                        steps.push(Step::CheckEqGlobal {
                            local: *local,
                            global: *global,
                        });
                        used[ai] = true;
                        progress = true;
                    }
                    RAtom::Lit { node, .. } => {
                        if !bound[(*node).idx()] {
                            steps.push(Step::Join {
                                target: *node,
                                lookups: vec![],
                            });
                            bound[(*node).idx()] = true;
                        }
                        used[ai] = true;
                        progress = true;
                    }
                    RAtom::LitBind { node, op, val } if bound[(*node).idx()] => {
                        // Node is bound to a class rep — re-join to find
                        // the node with the right lit op in that class.
                        steps.push(Step::Join {
                            target: *node,
                            lookups: vec![
                                IndexLookup::ByRepr { repr: *node },
                                IndexLookup::ByOp { op: *op },
                            ],
                        });
                        steps.push(Step::ExtractLitVal {
                            node: *node,
                            val: *val,
                        });
                        used[ai] = true;
                        progress = true;
                    }
                    // Otherwise defer to cost-based selection.
                    RAtom::Plain { node, op, .. } if bound[(*node).idx()] => {
                        // The node var is bound to a class representative, but
                        // we need a node with the specific op in that class.
                        // Re-join within the class: ByRepr ∩ ByOp.
                        steps.push(Step::Join {
                            target: *node,
                            lookups: vec![
                                IndexLookup::ByRepr { repr: *node },
                                IndexLookup::ByOp { op: *op },
                            ],
                        });
                        emit_read_children(&rq.atoms[ai], &mut bound, &mut steps);
                        used[ai] = true;
                        progress = true;
                    }
                    _ => {}
                }
            }
        }

        // Pick cheapest unprocessed atom.
        let best = (0..rq.atoms.len())
            .filter(|&ai| {
                !used[ai] && !matches!(&rq.atoms[ai], RAtom::Eq(..) | RAtom::EqGlobal(..))
            })
            .min_by_key(|&ai| estimate_cost(&rq.atoms[ai], &bound, stats));

        let Some(ai) = best else { break };
        emit_atom(&rq.atoms[ai], &mut bound, &mut steps);
        used[ai] = true;
    }

    QueryPlan {
        steps,
        shape: rq.shape.clone(),
    }
}

fn emit_read_children<O: DenseId + Hash + Copy, S, V>(
    atom: &RAtom<O, S, V>,
    bound: &mut [bool],
    steps: &mut Vec<Step<O>>,
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
                    pos: pos as u32,
                });
                pv_mark_bound(&cv, bound);
            } else {
                steps.push(Step::CheckChildEq {
                    parent: *node,
                    pos: pos as u32,
                    expected: cv,
                });
            }
        }
    }
}

fn emit_atom<O: DenseId + Hash + Copy, S, V>(
    atom: &RAtom<O, S, V>,
    bound: &mut [bool],
    steps: &mut Vec<Step<O>>,
) {
    match atom {
        RAtom::Plain { node, op, children } => {
            let mut lookups = vec![IndexLookup::ByOp { op: *op }];
            for (pos, &cv) in children.iter().enumerate() {
                if pv_is_bound(&cv, bound) {
                    lookups.push(IndexLookup::ByChildPos {
                        child: cv,
                        pos: pos as u32,
                    });
                }
            }
            steps.push(Step::Join {
                target: *node,
                lookups,
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
                        pos: pos as u32,
                    });
                    pv_mark_bound(&cv, bound);
                } else {
                    steps.push(Step::CheckChildEq {
                        parent: *node,
                        pos: pos as u32,
                        expected: cv,
                    });
                }
            }
        }
        RAtom::Lit { node, .. } => {
            if !bound[(*node).idx()] {
                steps.push(Step::Join {
                    target: *node,
                    lookups: vec![],
                });
                bound[(*node).idx()] = true;
            }
        }
        RAtom::LitBind { node, op, val } => {
            if !bound[(*node).idx()] {
                steps.push(Step::Join {
                    target: *node,
                    lookups: vec![IndexLookup::ByOp { op: *op }],
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
            emit_variadic_join(node, *op, bound, steps);
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
            emit_variadic_join(node, *op, bound, steps);
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
            emit_variadic_join(node, *op, bound, steps);
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
            emit_variadic_join(node, *op, bound, steps);
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
            emit_variadic_join(node, *op, bound, steps);
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
            emit_variadic_join(node, *op, bound, steps);
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
            emit_variadic_join(node, *op, bound, steps);
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
            emit_variadic_join(node, *op, bound, steps);
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

fn emit_variadic_join<O: DenseId + Hash + Copy>(
    node: &VarId,
    op: O,
    bound: &mut [bool],
    steps: &mut Vec<Step<O>>,
) {
    if !bound[(*node).idx()] {
        steps.push(Step::Join {
            target: *node,
            lookups: vec![IndexLookup::ByOp { op }],
        });
        bound[(*node).idx()] = true;
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
        ops.register_ac("add", e, e);
        ops.register_aci("union", e, e);
        (ops, sorts, LitValStore::new())
    }

    fn do_plan(src: &str) -> (QueryPlan<OpId>, MatchShape) {
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

    fn do_plan_multi(srcs: &[&str]) -> (QueryPlan<OpId>, MatchShape) {
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

    fn do_plan_with_stats(srcs: &[&str], card: &[(&str, usize)]) -> (QueryPlan<OpId>, MatchShape) {
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
}
