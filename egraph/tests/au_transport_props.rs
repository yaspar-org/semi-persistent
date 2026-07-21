// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Property-based tests for the transportation solver.
//!
//! Each test checks a mathematical invariant that must hold for every valid input,
//! regardless of margins, costs, or forbidden-cell patterns.

use proptest::prelude::*;
use semi_persistent_egraph::au::transport::{
    Cell, TransportProblem, TransportSolution, solve_transport,
};

fn check_margins(p: &TransportProblem, sol: &TransportSolution) {
    let rows = p.row_supply.len();
    let cols = p.col_demand.len();
    for i in 0..rows {
        let row_sum: u32 = sol.flow[i].iter().sum();
        assert_eq!(row_sum, p.row_supply[i], "row {i} margin violated");
    }
    for j in 0..cols {
        let col_sum: u32 = sol.flow.iter().map(|r| r[j]).sum();
        assert_eq!(col_sum, p.col_demand[j], "col {j} margin violated");
    }
}

fn recompute_total(p: &TransportProblem, sol: &TransportSolution) -> (u128, u128) {
    let mut s: u128 = 0;
    let mut v: u128 = 0;
    for (i, row) in sol.flow.iter().enumerate() {
        for (j, &x) in row.iter().enumerate() {
            if x > 0 {
                match p.cost[i][j] {
                    Cell::Cost(cs, cv) => {
                        s += x as u128 * cs as u128;
                        v += x as u128 * cv as u128;
                    }
                    Cell::Forbidden => panic!("flow on forbidden cell ({i},{j})"),
                }
            }
        }
    }
    (s, v)
}

/// Generate a random transportation problem with equal total supply/demand.
fn arb_problem(max_dim: usize, max_margin: u32) -> impl Strategy<Value = TransportProblem> {
    (1..=max_dim, 1..=max_dim).prop_flat_map(move |(rows, cols)| {
        let row_supply = proptest::collection::vec(1..=max_margin, rows);
        row_supply
            .prop_flat_map(move |rs| {
                let total: u32 = rs.iter().sum();
                // Distribute total across cols (each at least 1, sum = total).
                let col_demand = if cols == 1 {
                    Just(vec![total]).boxed()
                } else {
                    proptest::collection::vec(0..=total, cols)
                        .prop_map(move |mut cd| {
                            // Normalize to sum = total with each >= 0.
                            let raw_sum: u64 = cd.iter().map(|&x| x as u64).sum::<u64>().max(1);
                            for x in &mut cd {
                                *x = (((*x as u64) * total as u64) / raw_sum) as u32;
                            }
                            let current: u32 = cd.iter().sum();
                            if current < total {
                                cd[0] += total - current;
                            } else if current > total {
                                for x in cd.iter_mut() {
                                    if *x > 0 && current - *x >= total {
                                        // skip
                                    } else {
                                        let excess = current.saturating_sub(total);
                                        let reduce = (*x).min(excess);
                                        *x -= reduce;
                                        break;
                                    }
                                }
                                let c2: u32 = cd.iter().sum();
                                if c2 != total {
                                    cd[0] = cd[0].wrapping_add(total.wrapping_sub(c2));
                                }
                            }
                            cd
                        })
                        .boxed()
                };
                (Just(rs), col_demand, Just(rows), Just(cols))
            })
            .prop_flat_map(move |(rs, cd, rows, cols)| {
                let cost = proptest::collection::vec(
                    proptest::collection::vec(
                        prop_oneof![
                            8 => (0..100u32, 0..100u32).prop_map(|(s, v)| Cell::Cost(s, v)),
                            2 => Just(Cell::Forbidden),
                        ],
                        cols,
                    ),
                    rows,
                );
                (Just(rs), Just(cd), cost)
            })
            .prop_map(|(row_supply, col_demand, cost)| TransportProblem {
                row_supply,
                col_demand,
                cost,
            })
    })
}

// Property 1: every returned solution satisfies all row and column margins exactly.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]
    #[test]
    fn prop_margins_satisfied(p in arb_problem(4, 10)) {
        if let Some(sol) = solve_transport(&p) {
            check_margins(&p, &sol);
        }
    }
}

// Property 2: no flow on forbidden cells.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]
    #[test]
    fn prop_no_flow_on_forbidden(p in arb_problem(4, 10)) {
        if let Some(sol) = solve_transport(&p) {
            for (i, row) in sol.flow.iter().enumerate() {
                for (j, &x) in row.iter().enumerate() {
                    if x > 0 {
                        prop_assert!(
                            matches!(p.cost[i][j], Cell::Cost(_, _)),
                            "flow {x} on forbidden cell ({i},{j})"
                        );
                    }
                }
            }
        }
    }
}

// Property 3: reported total equals recomputed total from the flow matrix.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(500))]
    #[test]
    fn prop_total_consistent_with_flow(p in arb_problem(4, 10)) {
        if let Some(sol) = solve_transport(&p) {
            let recomputed = recompute_total(&p, &sol);
            prop_assert_eq!(sol.total, recomputed);
        }
    }
}

// Property 4: the solution is lexicographically optimal. Compare against an
// exhaustive reference on small instances.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]
    #[test]
    fn prop_optimality_vs_exhaustive(p in arb_problem(3, 4)) {
        let flow_result = solve_transport(&p);
        let exhaustive = exhaustive_min(&p);
        match (flow_result, exhaustive) {
            (Some(sol), Some(expected)) => {
                prop_assert_eq!(
                    sol.total, expected,
                    "flow quality diverged from exhaustive minimum"
                );
            }
            (None, None) => {} // both agree infeasible
            (f, e) => {
                prop_assert!(false, "feasibility disagreement: flow={f:?} exhaustive={e:?}");
            }
        }
    }
}

// Property 5: determinism. Same input always produces the same output.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]
    #[test]
    fn prop_determinism(p in arb_problem(4, 10)) {
        let a = solve_transport(&p);
        let b = solve_transport(&p);
        prop_assert_eq!(a, b);
    }
}

// Property 6: scaling margins does not change feasibility. If a problem is
// feasible, scaling all margins by k (same factor) should also be feasible
// (the flow just scales).
proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]
    #[test]
    fn prop_scaling_preserves_feasibility(
        p in arb_problem(3, 5),
        k in 1u32..4,
    ) {
        let feasible = solve_transport(&p).is_some();
        if feasible && k > 0 {
            let scaled = TransportProblem {
                row_supply: p.row_supply.iter().map(|&m| m.saturating_mul(k)).collect(),
                col_demand: p.col_demand.iter().map(|&n| n.saturating_mul(k)).collect(),
                cost: p.cost.clone(),
            };
            // Check totals still match after saturation.
            let st: u64 = scaled.row_supply.iter().map(|&m| m as u64).sum();
            let dt: u64 = scaled.col_demand.iter().map(|&n| n as u64).sum();
            if st == dt {
                prop_assert!(
                    solve_transport(&scaled).is_some(),
                    "scaling a feasible problem must remain feasible"
                );
            }
        }
    }
}

// Property 7: lexicographic ordering. If we make one cell's size cheaper by 1
// and the optimal flow used that cell, the new total size must be at most the
// old total size (weakly, because the solver might find an even better flow).
proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]
    #[test]
    fn prop_cheaper_cell_does_not_worsen(p in arb_problem(3, 5)) {
        if let Some(sol) = solve_transport(&p) {
            // Find a cell with positive flow and positive size cost.
            let rows = p.row_supply.len();
            let cols = p.col_demand.len();
            for i in 0..rows {
                for j in 0..cols {
                    if sol.flow[i][j] > 0
                        && let Cell::Cost(s, v) = p.cost[i][j]
                        && s > 0
                    {
                        let mut cheaper = p.clone();
                        cheaper.cost[i][j] = Cell::Cost(s - 1, v);
                        if let Some(new_sol) = solve_transport(&cheaper) {
                            prop_assert!(
                                new_sol.total.0 <= sol.total.0,
                                "making a used cell cheaper must not worsen the objective"
                            );
                        }
                        return Ok(());
                    }
                }
            }
        }
    }
}

// Property 8: large margins do not overflow. Generate problems with margins
// up to u32::MAX / 4 and verify no panic.
proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]
    #[test]
    fn prop_large_margins_no_panic(
        m1 in 100_000u32..u32::MAX / 4,
        m2 in 100_000u32..u32::MAX / 4,
        s1 in 0u32..1000,
        s2 in 0u32..1000,
        v1 in 0u32..1000,
        v2 in 0u32..1000,
    ) {
        let total = m1 as u64 + m2 as u64;
        if total > u32::MAX as u64 {
            return Ok(()); // skip: can't fit in a single u32 demand
        }
        let p = TransportProblem {
            row_supply: vec![m1, m2],
            col_demand: vec![m1, m2], // diagonal feasible
            cost: vec![
                vec![Cell::Cost(s1, v1), Cell::Cost(s2, v2)],
                vec![Cell::Cost(s2, v2), Cell::Cost(s1, v1)],
            ],
        };
        let sol = solve_transport(&p);
        prop_assert!(sol.is_some());
        if let Some(sol) = sol {
            check_margins(&p, &sol);
            let recomputed = recompute_total(&p, &sol);
            prop_assert_eq!(sol.total, recomputed);
        }
    }
}

/// Exhaustive reference (same as in the lib unit tests, for the proptest oracle).
#[allow(clippy::collapsible_if, clippy::needless_range_loop)]
fn exhaustive_min(p: &TransportProblem) -> Option<(u128, u128)> {
    let rows = p.row_supply.len();
    let cols = p.col_demand.len();
    let mut best: Option<(u128, u128)> = None;
    let mut matrix = vec![vec![0u32; cols]; rows];
    let mut col_residual = p.col_demand.clone();

    fn rec(
        p: &TransportProblem,
        matrix: &mut Vec<Vec<u32>>,
        col_residual: &mut Vec<u32>,
        row: usize,
        best: &mut Option<(u128, u128)>,
    ) {
        let rows = p.row_supply.len();
        let cols = p.col_demand.len();
        if row == rows {
            if col_residual.iter().any(|&c| c != 0) {
                return;
            }
            let mut s: u128 = 0;
            let mut v: u128 = 0;
            for i in 0..rows {
                for j in 0..cols {
                    let x = matrix[i][j];
                    if x > 0 {
                        match p.cost[i][j] {
                            Cell::Cost(cs, cv) => {
                                s += x as u128 * cs as u128;
                                v += x as u128 * cv as u128;
                            }
                            Cell::Forbidden => return,
                        }
                    }
                }
            }
            let q = (s, v);
            if best.is_none() || q < best.unwrap() {
                *best = Some(q);
            }
            return;
        }
        fn dist(
            p: &TransportProblem,
            matrix: &mut Vec<Vec<u32>>,
            col_residual: &mut Vec<u32>,
            row: usize,
            col: usize,
            remaining: u32,
            best: &mut Option<(u128, u128)>,
        ) {
            let cols = p.col_demand.len();
            if col == cols {
                if remaining == 0 {
                    rec(p, matrix, col_residual, row + 1, best);
                }
                return;
            }
            let max = remaining.min(col_residual[col]);
            for x in 0..=max {
                if x > 0 && matches!(p.cost[row][col], Cell::Forbidden) {
                    break;
                }
                matrix[row][col] = x;
                col_residual[col] -= x;
                dist(p, matrix, col_residual, row, col + 1, remaining - x, best);
                col_residual[col] += x;
                matrix[row][col] = 0;
            }
        }
        dist(p, matrix, col_residual, row, 0, p.row_supply[row], best);
    }

    rec(p, &mut matrix, &mut col_residual, 0, &mut best);
    best
}
