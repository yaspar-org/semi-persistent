// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Pair-mode bounded relaxation over the finite class-pair graph.
//!
//! E-classes are regular tree grammars. Their product is a finite AND/OR
//! hypergraph whose states are ordered class pairs. Cycles in that graph do
//! not require recursive evaluation: round `d` below is intended to compute
//! the best finite derivation of structural depth at most `d`, starting from
//! the always available terminal generalize action at depth zero. Finite
//! oracles exercise this invariant; it is not yet a machine-checked refinement.
//!
//! The implementation relies on the following cycle-erasure argument: a
//! minimum-size derivation does not repeat a pair on one root-to-leaf path. If
//! it did, the descendant occurrence would itself be a valid result for the
//! same pair, while the surrounding structural path contributes at least one
//! ordinary term node. Removing the path is therefore strictly smaller. With
//! `N` reachable pair states, the argument gives a depth-`N` bound, which the
//! loop asserts. This argument has finite regression coverage but is not yet a
//! machine-checked theorem; see design chapter 19, section 9.6.

use std::collections::HashMap;
use std::time::{Duration, Instant};

use crate::canon::{MSetCanon, VarCanon};
use crate::config::{AuIds, EGraphConfig};
use crate::literal::LitVal;

use super::ac_repr;
use super::actions::{ActionCache, generate_actions};
use super::egraph_api::{AuSnapshot, ClassOf};
use super::estimates::lb_pair;
use super::terms::{TermOp, TermPool, build_best_term, evaluate_generalize_action};
use super::transport::{Cell, TransportProblem, TransportSolution, solve_transport};

type Quality = (u32, u32);

struct StructuralAction<O> {
    op: O,
    children: Vec<(usize, u64)>,
}

struct TransportAction<O> {
    op: O,
    row_supply: Vec<u32>,
    col_demand: Vec<u32>,
    cells: Vec<Vec<usize>>,
}

struct PairNode<Cfg: EGraphConfig> {
    left: ClassOf<Cfg>,
    right: ClassOf<Cfg>,
    structural: Vec<StructuralAction<Cfg::O>>,
    transport: Vec<TransportAction<Cfg::O>>,
}

struct PairGraph<Cfg: EGraphConfig> {
    nodes: Vec<PairNode<Cfg>>,
    by_pair: HashMap<(ClassOf<Cfg>, ClassOf<Cfg>), usize>,
}

impl<Cfg: EGraphConfig> PairGraph<Cfg> {
    fn new(left: ClassOf<Cfg>, right: ClassOf<Cfg>) -> Self {
        let mut by_pair = HashMap::new();
        by_pair.insert((left, right), 0);
        PairGraph {
            nodes: vec![PairNode {
                left,
                right,
                structural: Vec::new(),
                transport: Vec::new(),
            }],
            by_pair,
        }
    }

    fn intern(&mut self, left: ClassOf<Cfg>, right: ClassOf<Cfg>) -> usize {
        if let Some(&index) = self.by_pair.get(&(left, right)) {
            return index;
        }
        let index = self.nodes.len();
        self.nodes.push(PairNode {
            left,
            right,
            structural: Vec::new(),
            transport: Vec::new(),
        });
        self.by_pair.insert((left, right), index);
        index
    }
}

pub(crate) struct FixedExact<T> {
    pub(crate) term: T,
    pub(crate) complete: bool,
    #[allow(dead_code)]
    pub(crate) states: usize,
    #[allow(dead_code)]
    pub(crate) rounds: usize,
}

#[inline]
fn expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|limit| Instant::now() >= limit)
}

fn narrow_counts<C>(monomial: &[(C, u64)]) -> Option<Vec<u32>> {
    monomial
        .iter()
        .map(|(_, count)| u32::try_from(*count).ok())
        .collect()
}

fn build_graph<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    left: ClassOf<Cfg>,
    right: ClassOf<Cfg>,
    deadline: Option<Instant>,
) -> Option<PairGraph<Cfg>>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut graph = PairGraph::new(left, right);
    let mut cache: ActionCache<Cfg::O, Cfg::Au, Cfg::M> =
        ActionCache::without_ac_actions(usize::MAX);
    let mut cursor = 0;

    while cursor < graph.nodes.len() {
        if expired(deadline) {
            return None;
        }
        let left = graph.nodes[cursor].left;
        let right = graph.nodes[cursor].right;
        if left == right {
            cursor += 1;
            continue;
        }

        generate_actions(snap, &mut cache, left, right);
        let actions = cache
            .get(left, right)
            .expect("action generation must populate the cache")
            .to_vec();
        let mut structural = Vec::with_capacity(actions.len());
        for action in actions {
            let children = action
                .pairs
                .iter()
                .map(|pair| {
                    (
                        graph.intern(pair.left, pair.right),
                        crate::multiplicity::MultiplicityLike::to_u64(pair.count),
                    )
                })
                .collect();
            structural.push(StructuralAction {
                op: action.op,
                children,
            });
        }

        let mut transport = Vec::new();
        for op in ac_repr::common_ac_ops(snap, left, right) {
            for (left_mono, right_mono, _) in ac_repr::representation_pairs(snap, left, right, op) {
                let Some(row_supply) = narrow_counts(&left_mono) else {
                    continue;
                };
                let Some(col_demand) = narrow_counts(&right_mono) else {
                    continue;
                };
                let cells = left_mono
                    .iter()
                    .map(|(left_child, _)| {
                        right_mono
                            .iter()
                            .map(|(right_child, _)| graph.intern(*left_child, *right_child))
                            .collect()
                    })
                    .collect();
                transport.push(TransportAction {
                    op,
                    row_supply,
                    col_demand,
                    cells,
                });
            }
        }

        graph.nodes[cursor].structural = structural;
        graph.nodes[cursor].transport = transport;
        cursor += 1;
    }
    Some(graph)
}

#[inline]
fn cap_quality(size: u128, variant_mass: u128) -> Quality {
    (
        size.min(u128::from(u32::MAX)) as u32,
        variant_mass.min(u128::from(u32::MAX)) as u32,
    )
}

fn structural_quality<O>(action: &StructuralAction<O>, qualities: &[Quality]) -> Quality {
    let mut size = 1u128;
    let mut variant_mass = 0u128;
    for &(child, count) in &action.children {
        size = size.saturating_add(u128::from(qualities[child].0) * u128::from(count));
        variant_mass =
            variant_mass.saturating_add(u128::from(qualities[child].1) * u128::from(count));
    }
    cap_quality(size, variant_mass)
}

fn structural_size_bound<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    graph: &PairGraph<Cfg>,
    action: &StructuralAction<Cfg::O>,
) -> u128
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    action
        .children
        .iter()
        .fold(1u128, |bound, &(child, count)| {
            let node = &graph.nodes[child];
            bound.saturating_add(
                u128::from(lb_pair(snap, node.left, node.right).0) * u128::from(count),
            )
        })
}

fn transport_solution<O>(
    action: &TransportAction<O>,
    qualities: &[Quality],
) -> Option<TransportSolution> {
    let cost = action
        .cells
        .iter()
        .map(|row| {
            row.iter()
                .map(|&child| Cell::Cost(qualities[child].0, qualities[child].1))
                .collect()
        })
        .collect();
    solve_transport(&TransportProblem {
        row_supply: action.row_supply.clone(),
        col_demand: action.col_demand.clone(),
        cost,
    })
}

fn transport_size_bound<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    graph: &PairGraph<Cfg>,
    action: &TransportAction<Cfg::O>,
) -> Option<u128>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let cost = action
        .cells
        .iter()
        .map(|row| {
            row.iter()
                .map(|&child| {
                    let node = &graph.nodes[child];
                    Cell::Cost(lb_pair(snap, node.left, node.right).0, 0)
                })
                .collect()
        })
        .collect();
    solve_transport(&TransportProblem {
        row_supply: action.row_supply.clone(),
        col_demand: action.col_demand.clone(),
        cost,
    })
    .map(|solution| solution.total.0.saturating_add(1))
}

fn solution_quality(solution: &TransportSolution) -> Quality {
    cap_quality(solution.total.0.saturating_add(1), solution.total.1)
}

fn structural_term<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    action: &StructuralAction<Cfg::O>,
    terms: &[<Cfg::Au as AuIds>::Term],
) -> <Cfg::Au as AuIds>::Term
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let children: Vec<_> = action
        .children
        .iter()
        .map(|&(child, count)| (terms[child], count))
        .collect();
    pool.intern_action_result(
        TermOp::EGraph(action.op),
        &children,
        snap.op_is_commutative(action.op),
    )
}

fn transport_term<Cfg: EGraphConfig>(
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    action: &TransportAction<Cfg::O>,
    solution: &TransportSolution,
    terms: &[<Cfg::Au as AuIds>::Term],
) -> <Cfg::Au as AuIds>::Term {
    let mut children = Vec::new();
    for (row, flow_row) in solution.flow.iter().enumerate() {
        for (col, &count) in flow_row.iter().enumerate() {
            if count > 0 {
                children.push((terms[action.cells[row][col]], u64::from(count)));
            }
        }
    }
    pool.intern_action_result(TermOp::EGraph(action.op), &children, true)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_in<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &mut TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    left: ClassOf<Cfg>,
    right: ClassOf<Cfg>,
    deadline: Option<Duration>,
    pruning: bool,
    warm_incumbent: Option<<Cfg::Au as AuIds>::Term>,
) -> Result<FixedExact<<Cfg::Au as AuIds>::Term>, super::AuError>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    snap.validate_finite_from(left)?;
    snap.validate_finite_from(right)?;
    let deadline = deadline.map(|duration| Instant::now() + duration);

    let root_fallback = if left == right {
        build_best_term(snap, pool, left)
    } else {
        evaluate_generalize_action(snap, pool, left, right)
    };
    let root_term = warm_incumbent
        .filter(|term| pool.quality(*term) < pool.quality(root_fallback))
        .unwrap_or(root_fallback);

    let Some(graph) = build_graph(snap, left, right, deadline) else {
        return Ok(FixedExact {
            term: root_term,
            complete: false,
            states: 1,
            rounds: 0,
        });
    };

    let mut qualities = Vec::with_capacity(graph.nodes.len());
    let mut terms = Vec::with_capacity(graph.nodes.len());
    for (index, node) in graph.nodes.iter().enumerate() {
        if expired(deadline) {
            return Ok(FixedExact {
                term: root_term,
                complete: false,
                states: graph.nodes.len(),
                rounds: 0,
            });
        }
        let term = if index == 0 {
            root_term
        } else if node.left == node.right {
            build_best_term(snap, pool, node.left)
        } else {
            evaluate_generalize_action(snap, pool, node.left, node.right)
        };
        qualities.push(pool.quality(term));
        terms.push(term);
    }

    let mut completed_rounds = 0;
    for round in 0..=graph.nodes.len() {
        if expired(deadline) {
            return Ok(FixedExact {
                term: terms[0],
                complete: false,
                states: graph.nodes.len(),
                rounds: completed_rounds,
            });
        }

        let mut next_qualities = qualities.clone();
        let mut next_terms = terms.clone();
        let mut changed = false;

        for (node_index, node) in graph.nodes.iter().enumerate() {
            if expired(deadline) {
                return Ok(FixedExact {
                    term: terms[0],
                    complete: false,
                    states: graph.nodes.len(),
                    rounds: completed_rounds,
                });
            }
            if node.left == node.right {
                continue;
            }
            let mut best_quality = qualities[node_index];
            let mut best_term = terms[node_index];

            for action in &node.structural {
                if pruning
                    && structural_size_bound(snap, &graph, action) > u128::from(best_quality.0)
                {
                    continue;
                }
                let candidate_quality = structural_quality(action, &qualities);
                if candidate_quality < best_quality {
                    let candidate = structural_term(snap, pool, action, &terms);
                    debug_assert_eq!(pool.quality(candidate), candidate_quality);
                    best_quality = candidate_quality;
                    best_term = candidate;
                }
            }

            for action in &node.transport {
                if pruning {
                    let Some(bound) = transport_size_bound(snap, &graph, action) else {
                        continue;
                    };
                    if bound > u128::from(best_quality.0) {
                        continue;
                    }
                }
                let Some(solution) = transport_solution(action, &qualities) else {
                    continue;
                };
                let candidate_quality = solution_quality(&solution);
                if candidate_quality < best_quality {
                    let candidate = transport_term::<Cfg>(pool, action, &solution, &terms);
                    debug_assert_eq!(pool.quality(candidate), candidate_quality);
                    best_quality = candidate_quality;
                    best_term = candidate;
                }
            }

            if best_quality < qualities[node_index] {
                changed = true;
                next_qualities[node_index] = best_quality;
                next_terms[node_index] = best_term;
            }
        }

        if !changed {
            return Ok(FixedExact {
                term: terms[0],
                complete: true,
                states: graph.nodes.len(),
                rounds: completed_rounds,
            });
        }
        assert!(
            round < graph.nodes.len(),
            "cycle-complete AU relaxation exceeded the pair-simple depth bound"
        );
        qualities = next_qualities;
        terms = next_terms;
        completed_rounds += 1;
    }
    unreachable!("the pair-depth loop either stabilizes or asserts")
}

pub(crate) fn run<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    left: ClassOf<Cfg>,
    right: ClassOf<Cfg>,
    deadline: Option<Duration>,
    pruning: bool,
) -> Result<
    (
        FixedExact<<Cfg::Au as AuIds>::Term>,
        TermPool<Cfg::O, Cfg::V, Cfg::Au>,
    ),
    super::AuError,
>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut pool = TermPool::new();
    let result = run_in(snap, &mut pool, left, right, deadline, pruning, None)?;
    Ok((result, pool))
}
