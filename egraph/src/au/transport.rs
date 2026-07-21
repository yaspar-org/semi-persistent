// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Lexicographic min-cost transportation solver for AC/ACI matching (§3.4.4).
//!
//! Problem: rows with supplies `m_i`, columns with demands `n_j` (equal totals),
//! per-cell lexicographic cost `(size, variant_mass)` or a forbidden marker.
//! Find an integral flow meeting every margin that minimizes
//! `(Σ x_ij·s_ij, Σ x_ij·v_ij)` lexicographically, or report infeasibility.
//!
//! The lexicographic objective is scalarized: `cost = s·W + v` with
//! `W = F·v_max + 1` where `F` is the total transported multiplicity and
//! `v_max` the maximum cell variant mass. Total variant mass never exceeds
//! `F·v_max`, so a one-unit size improvement always outweighs any possible
//! variant-mass difference. All arithmetic is checked `u128`; with `u32`
//! inputs the worst-case total cost is far below `u128::MAX` for any
//! realistic multiplicity, and overflow panics with a diagnostic rather
//! than wrapping.
//!
//! Algorithm: successive shortest augmenting paths (Bellman-Ford/SPFA, which
//! tolerates the negative residual reverse edges without potentials), with
//! bottleneck augmentation so large multiplicities move in one step instead
//! of unit-at-a-time. Determinism: nodes and edges are relaxed in fixed index
//! order with strict-less updates, so equal-cost ties resolve to the first
//! (lowest-index) candidate; the returned matrix is a deterministic function
//! of the input.

/// One cell of the transportation cost matrix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cell {
    /// Allowed pairing with lexicographic cost (size, variant_mass).
    Cost(u32, u32),
    /// Forbidden pairing (cycle-blocked).
    Forbidden,
}

/// A transportation problem instance.
#[derive(Clone, Debug)]
pub struct TransportProblem {
    pub row_supply: Vec<u32>,
    pub col_demand: Vec<u32>,
    /// `cost[i][j]` for row i, column j. Dimensions rows x cols.
    pub cost: Vec<Vec<Cell>>,
}

/// An optimal solution: the matching-count matrix and its total quality.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransportSolution {
    /// `flow[i][j]` = number of copies pairing row i with column j.
    pub flow: Vec<Vec<u32>>,
    /// Total (Σ x·s, Σ x·v) as u128 to handle large multiplicities without
    /// overflow. The caller adds the +1 operator cost.
    pub total: (u128, u128),
}

struct Edge {
    to: usize,
    cap: i64,
    cost: i128,
    /// Signed net flow: augmenting the forward edge by d does
    /// `flow[e] += d; flow[e^1] -= d`, so a reverse edge with cap 0 gains
    /// residual capacity exactly equal to the cancellable forward flow.
    flow: i64,
}

struct Network {
    edges: Vec<Edge>,
    /// adjacency: per node, indices into `edges` (each edge is paired with its
    /// reverse at index ^ 1).
    adj: Vec<Vec<usize>>,
}

impl Network {
    fn new(nodes: usize) -> Self {
        Network {
            edges: Vec::new(),
            adj: vec![Vec::new(); nodes],
        }
    }

    fn add_edge(&mut self, from: usize, to: usize, cap: u32, cost: i128) {
        let idx = self.edges.len();
        self.edges.push(Edge {
            to,
            cap: cap as i64,
            cost,
            flow: 0,
        });
        self.edges.push(Edge {
            to: from,
            cap: 0,
            cost: -cost,
            flow: 0,
        });
        self.adj[from].push(idx);
        self.adj[to].push(idx + 1);
    }

    fn residual(&self, e: usize) -> i64 {
        self.edges[e].cap - self.edges[e].flow
    }
}

/// A float-cost transportation problem (for MCGS Q estimates). Costs must be
/// finite; non-finite cells must be passed as `None` (Forbidden).
#[derive(Clone, Debug)]
pub struct TransportProblemF64 {
    pub row_supply: Vec<u32>,
    pub col_demand: Vec<u32>,
    /// `cost[i][j]`: `Some(finite f64)` = allowed, `None` = forbidden.
    pub cost: Vec<Vec<Option<f64>>>,
}

/// Solution of a float-cost transport: flow matrix and total cost.
#[derive(Clone, Debug, PartialEq)]
pub struct TransportSolutionF64 {
    pub flow: Vec<Vec<u32>>,
    pub total: f64,
}

/// Solve a float-cost transportation problem with the same SPFA successive
/// shortest augmenting path algorithm, using native f64 cost arithmetic.
/// Finite costs only (asserted unconditionally: NaN would silently corrupt
/// the relaxation); ties resolve deterministically to the first
/// (lowest-index) candidate. No scalarization or rounding: the exact argmin
/// over the represented f64 values is preserved.
pub fn solve_transport_f64(p: &TransportProblemF64) -> Option<TransportSolutionF64> {
    // Validate ALL costs before any early return: a non-finite cost is a
    // caller bug and must panic in every build and on every input shape
    // (zero-flow and mismatched-margin instances included), never be
    // conflated with infeasibility (None) or absorbed by a trivial solution.
    for row in &p.cost {
        for c in row.iter().flatten() {
            assert!(c.is_finite(), "transport f64 cost must be finite");
        }
    }

    let rows = p.row_supply.len();
    let cols = p.col_demand.len();
    if rows == 0 || cols == 0 {
        return None;
    }
    let total_supply: u64 = p.row_supply.iter().map(|&m| m as u64).sum();
    let total_demand: u64 = p.col_demand.iter().map(|&n| n as u64).sum();
    if total_supply != total_demand {
        return None;
    }
    if total_supply == 0 {
        return Some(TransportSolutionF64 {
            flow: vec![vec![0; cols]; rows],
            total: 0.0,
        });
    }

    let source = 0usize;
    let sink = rows + cols + 1;
    let mut net = NetworkF64::new(rows + cols + 2);
    for (i, &m) in p.row_supply.iter().enumerate() {
        net.add_edge(source, 1 + i, m, 0.0);
    }
    for (j, &n) in p.col_demand.iter().enumerate() {
        net.add_edge(1 + rows + j, sink, n, 0.0);
    }
    let mut cell_edge: Vec<Vec<Option<usize>>> = vec![vec![None; cols]; rows];
    for i in 0..rows {
        for j in 0..cols {
            if let Some(c) = p.cost[i][j] {
                let cap = p.row_supply[i].min(p.col_demand[j]);
                if cap > 0 {
                    cell_edge[i][j] = Some(net.edges.len());
                    net.add_edge(1 + i, 1 + rows + j, cap, c);
                }
            }
        }
    }

    let n_nodes = rows + cols + 2;
    let mut pushed_total: u64 = 0;
    loop {
        let mut dist: Vec<Option<f64>> = vec![None; n_nodes];
        let mut parent_edge: Vec<Option<usize>> = vec![None; n_nodes];
        let mut in_queue = vec![false; n_nodes];
        let mut queue = std::collections::VecDeque::new();
        dist[source] = Some(0.0);
        queue.push_back(source);
        in_queue[source] = true;

        while let Some(u) = queue.pop_front() {
            in_queue[u] = false;
            let du = dist[u].unwrap();
            for &e in &net.adj[u] {
                if net.residual(e) == 0 {
                    continue;
                }
                let v = net.edges[e].to;
                let nd = du + net.edges[e].cost;
                if dist[v].is_none() || nd < dist[v].unwrap() {
                    dist[v] = Some(nd);
                    parent_edge[v] = Some(e);
                    if !in_queue[v] {
                        queue.push_back(v);
                        in_queue[v] = true;
                    }
                }
            }
        }

        if dist[sink].is_none() {
            break;
        }
        let mut bottleneck = i64::MAX;
        let mut node = sink;
        while node != source {
            let e = parent_edge[node].unwrap();
            bottleneck = bottleneck.min(net.residual(e));
            node = net.edges[e ^ 1].to;
        }
        debug_assert!(bottleneck > 0);
        let mut node = sink;
        while node != source {
            let e = parent_edge[node].unwrap();
            net.edges[e].flow += bottleneck;
            net.edges[e ^ 1].flow -= bottleneck;
            node = net.edges[e ^ 1].to;
        }
        pushed_total += bottleneck as u64;
        if pushed_total == total_supply {
            break;
        }
    }

    if pushed_total != total_supply {
        return None;
    }

    let mut flow = vec![vec![0u32; cols]; rows];
    let mut total = 0.0f64;
    for i in 0..rows {
        for j in 0..cols {
            if let Some(e) = cell_edge[i][j] {
                let x = net.edges[e].flow;
                debug_assert!(x >= 0);
                if x > 0 {
                    let x = u32::try_from(x).expect("cell flow exceeds u32");
                    flow[i][j] = x;
                    if let Some(c) = p.cost[i][j] {
                        total += x as f64 * c;
                    }
                }
            }
        }
    }
    Some(TransportSolutionF64 { flow, total })
}

struct EdgeF64 {
    to: usize,
    cap: i64,
    cost: f64,
    flow: i64,
}

struct NetworkF64 {
    edges: Vec<EdgeF64>,
    adj: Vec<Vec<usize>>,
}

impl NetworkF64 {
    fn new(nodes: usize) -> Self {
        NetworkF64 {
            edges: Vec::new(),
            adj: vec![Vec::new(); nodes],
        }
    }

    fn add_edge(&mut self, from: usize, to: usize, cap: u32, cost: f64) {
        let idx = self.edges.len();
        self.edges.push(EdgeF64 {
            to,
            cap: cap as i64,
            cost,
            flow: 0,
        });
        self.edges.push(EdgeF64 {
            to: from,
            cap: 0,
            cost: -cost,
            flow: 0,
        });
        self.adj[from].push(idx);
        self.adj[to].push(idx + 1);
    }

    fn residual(&self, e: usize) -> i64 {
        self.edges[e].cap - self.edges[e].flow
    }
}

/// Solve the transportation problem. Returns `None` if infeasible (the margins
/// cannot be met using only allowed cells) and panics on arithmetic overflow
/// (unreachable for realistic u32 inputs).
pub fn solve_transport(p: &TransportProblem) -> Option<TransportSolution> {
    let rows = p.row_supply.len();
    let cols = p.col_demand.len();
    if rows == 0 || cols == 0 {
        return None;
    }
    let total_supply: u64 = p.row_supply.iter().map(|&m| m as u64).sum();
    let total_demand: u64 = p.col_demand.iter().map(|&n| n as u64).sum();
    if total_supply != total_demand {
        return None;
    }
    if total_supply == 0 {
        return Some(TransportSolution {
            flow: vec![vec![0; cols]; rows],
            total: (0, 0),
        });
    }

    // Scalarization constants (checked).
    let f: u128 = total_supply as u128;
    let v_max: u128 = p
        .cost
        .iter()
        .flatten()
        .filter_map(|c| match c {
            Cell::Cost(_, v) => Some(*v as u128),
            Cell::Forbidden => None,
        })
        .max()
        .unwrap_or(0);
    let w: u128 = f
        .checked_mul(v_max)
        .and_then(|x| x.checked_add(1))
        .expect("transport scalarization overflow (W)");

    // Nodes: source=0, rows 1..=rows, cols rows+1..=rows+cols, sink=rows+cols+1.
    let source = 0usize;
    let sink = rows + cols + 1;
    let mut net = Network::new(rows + cols + 2);

    for (i, &m) in p.row_supply.iter().enumerate() {
        net.add_edge(source, 1 + i, m, 0);
    }
    for (j, &n) in p.col_demand.iter().enumerate() {
        net.add_edge(1 + rows + j, sink, n, 0);
    }
    // Remember the edge index of each (i,j) cell for flow extraction.
    let mut cell_edge: Vec<Vec<Option<usize>>> = vec![vec![None; cols]; rows];
    for i in 0..rows {
        for j in 0..cols {
            if let Cell::Cost(s, v) = p.cost[i][j] {
                let scalar: u128 = (s as u128)
                    .checked_mul(w)
                    .and_then(|x| x.checked_add(v as u128))
                    .expect("transport scalarization overflow (cell)");
                let cap = p.row_supply[i].min(p.col_demand[j]);
                if cap > 0 {
                    cell_edge[i][j] = Some(net.edges.len());
                    let cost_i128 =
                        i128::try_from(scalar).expect("transport scalar cost exceeds i128");
                    net.add_edge(1 + i, 1 + rows + j, cap, cost_i128);
                }
            }
        }
    }

    // Successive shortest augmenting paths with SPFA and bottleneck augmentation.
    let n_nodes = rows + cols + 2;
    let mut pushed_total: u64 = 0;
    loop {
        // SPFA from source: dist, parent edge.
        let mut dist: Vec<Option<i128>> = vec![None; n_nodes];
        let mut parent_edge: Vec<Option<usize>> = vec![None; n_nodes];
        let mut in_queue = vec![false; n_nodes];
        let mut queue = std::collections::VecDeque::new();
        dist[source] = Some(0);
        queue.push_back(source);
        in_queue[source] = true;

        while let Some(u) = queue.pop_front() {
            in_queue[u] = false;
            let du = dist[u].unwrap();
            for &e in &net.adj[u] {
                if net.residual(e) == 0 {
                    continue;
                }
                let v = net.edges[e].to;
                let nd = du
                    .checked_add(net.edges[e].cost)
                    .expect("transport distance overflow");
                // Strict-less relaxation: deterministic first-found ties.
                if dist[v].is_none() || nd < dist[v].unwrap() {
                    dist[v] = Some(nd);
                    parent_edge[v] = Some(e);
                    if !in_queue[v] {
                        queue.push_back(v);
                        in_queue[v] = true;
                    }
                }
            }
        }

        if dist[sink].is_none() {
            break; // no augmenting path
        }

        // Bottleneck along the path.
        let mut bottleneck = i64::MAX;
        let mut node = sink;
        while node != source {
            let e = parent_edge[node].unwrap();
            bottleneck = bottleneck.min(net.residual(e));
            // The edge e enters `node`; its reverse (e^1) points back.
            node = net.edges[e ^ 1].to;
        }
        debug_assert!(bottleneck > 0);

        // Apply: standard signed-flow update. Pushing d along e cancels d units
        // of any flow on the reverse edge (flow[e^1] -= d), which is what makes
        // residual(e^1) = cap - flow correct for both directions.
        let mut node = sink;
        while node != source {
            let e = parent_edge[node].unwrap();
            net.edges[e].flow += bottleneck;
            net.edges[e ^ 1].flow -= bottleneck;
            node = net.edges[e ^ 1].to;
        }
        pushed_total += bottleneck as u64;
        if pushed_total == total_supply {
            break;
        }
    }

    if pushed_total != total_supply {
        return None; // infeasible: margins cannot be met with allowed cells
    }

    // Extract the flow matrix and total quality.
    let mut flow = vec![vec![0u32; cols]; rows];
    let mut total_s: u128 = 0;
    let mut total_v: u128 = 0;
    for i in 0..rows {
        for j in 0..cols {
            if let Some(e) = cell_edge[i][j] {
                let x = net.edges[e].flow;
                debug_assert!(x >= 0, "forward cell edge cannot end with negative flow");
                if x > 0 {
                    let x = u32::try_from(x).expect("cell flow exceeds u32");
                    flow[i][j] = x;
                    if let Cell::Cost(s, v) = p.cost[i][j] {
                        total_s += x as u128 * s as u128;
                        total_v += x as u128 * v as u128;
                    }
                }
            }
        }
    }

    Some(TransportSolution {
        flow,
        total: (total_s, total_v),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Non-finite f64 costs are a caller bug and must panic in ALL builds
    /// (a NaN would silently corrupt the SPFA relaxation), never be
    /// conflated with transport infeasibility (which returns None).
    #[test]
    #[should_panic(expected = "transport f64 cost must be finite")]
    fn f64_nan_cost_panics() {
        let p = TransportProblemF64 {
            row_supply: vec![1],
            col_demand: vec![1],
            cost: vec![vec![Some(f64::NAN)]],
        };
        let _ = solve_transport_f64(&p);
    }

    #[test]
    #[should_panic(expected = "transport f64 cost must be finite")]
    fn f64_infinite_cost_panics() {
        let p = TransportProblemF64 {
            row_supply: vec![1],
            col_demand: vec![1],
            cost: vec![vec![Some(f64::INFINITY)]],
        };
        let _ = solve_transport_f64(&p);
    }

    /// The finiteness contract holds on every input shape: a zero-flow
    /// instance must not absorb a NaN into a trivial solution.
    #[test]
    #[should_panic(expected = "transport f64 cost must be finite")]
    fn f64_nan_cost_panics_on_zero_flow() {
        let p = TransportProblemF64 {
            row_supply: vec![0],
            col_demand: vec![0],
            cost: vec![vec![Some(f64::NAN)]],
        };
        let _ = solve_transport_f64(&p);
    }

    /// ... and a mismatched-margin instance must not conflate the NaN with
    /// infeasibility (None).
    #[test]
    #[should_panic(expected = "transport f64 cost must be finite")]
    fn f64_infinite_cost_panics_on_mismatched_margins() {
        let p = TransportProblemF64 {
            row_supply: vec![2],
            col_demand: vec![1],
            cost: vec![vec![Some(f64::INFINITY)]],
        };
        let _ = solve_transport_f64(&p);
    }

    /// Exhaustive reference: enumerate every feasible integer matrix, return
    /// the lexicographic minimum total quality (or None if infeasible).
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
                                Cell::Forbidden => return, // invalid matrix
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
            // Distribute row `row` across columns.
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

    fn check_margins(p: &TransportProblem, sol: &TransportSolution) {
        for (i, &m) in p.row_supply.iter().enumerate() {
            let row_sum: u32 = sol.flow[i].iter().sum();
            assert_eq!(row_sum, m, "row {i} margin violated");
        }
        for (j, &n) in p.col_demand.iter().enumerate() {
            let col_sum: u32 = sol.flow.iter().map(|r| r[j]).sum();
            assert_eq!(col_sum, n, "col {j} margin violated");
        }
        for (i, row) in sol.flow.iter().enumerate() {
            for (j, &x) in row.iter().enumerate() {
                if x > 0 {
                    assert!(
                        matches!(p.cost[i][j], Cell::Cost(_, _)),
                        "flow on forbidden cell ({i},{j})"
                    );
                }
            }
        }
    }

    #[test]
    fn trivial_1x1() {
        let p = TransportProblem {
            row_supply: vec![3],
            col_demand: vec![3],
            cost: vec![vec![Cell::Cost(2, 1)]],
        };
        let sol = solve_transport(&p).unwrap();
        assert_eq!(sol.flow, vec![vec![3]]);
        assert_eq!(sol.total, (6, 3));
    }

    #[test]
    fn intersection_counterexample_costs() {
        // The [2,1] x [2,1] instance with the cross vertex optimal:
        // costs: (0,0)=3 self-pair X-X; (0,1)=4 X-Z; (1,0)=4 Y-X; (1,1)=6 Y-Z.
        // Diagonal matrix [[2,0],[0,1]] costs 2*3 + 6 = 12? No: X appears twice
        // in acop{X,X,Y}? Use the actual margins from the counterexample:
        // left {X^2, Y}, right {X^2, Z}... simplified to [2,1] margins:
        let p = TransportProblem {
            row_supply: vec![2, 1],
            col_demand: vec![2, 1],
            cost: vec![
                vec![Cell::Cost(3, 0), Cell::Cost(4, 2)],
                vec![Cell::Cost(4, 2), Cell::Cost(6, 6)],
            ],
        };
        let sol = solve_transport(&p).unwrap();
        check_margins(&p, &sol);
        // Diagonal: 2*3 + 1*6 = 12. Cross: 1*3 + 1*4 + 1*4 = 11.
        assert_eq!(sol.total.0, 11, "the cross matching must win");
        assert_eq!(sol.flow, vec![vec![1, 1], vec![1, 0]]);
    }

    #[test]
    fn forbidden_cell_forces_detour() {
        let p = TransportProblem {
            row_supply: vec![1, 1],
            col_demand: vec![1, 1],
            cost: vec![
                vec![Cell::Cost(1, 0), Cell::Cost(10, 0)],
                vec![Cell::Forbidden, Cell::Cost(1, 0)],
            ],
        };
        // Row 1 can only go to col 1, so row 0 must take col 0: total 2.
        let sol = solve_transport(&p).unwrap();
        check_margins(&p, &sol);
        assert_eq!(sol.total, (2, 0));
    }

    #[test]
    fn infeasible_when_column_unreachable() {
        let p = TransportProblem {
            row_supply: vec![1, 1],
            col_demand: vec![1, 1],
            cost: vec![
                vec![Cell::Cost(1, 0), Cell::Forbidden],
                vec![Cell::Cost(1, 0), Cell::Forbidden],
            ],
        };
        assert!(solve_transport(&p).is_none());
    }

    #[test]
    fn hall_style_infeasibility() {
        // Every row and column has an edge, but capacity constraints fail:
        // rows 0,1 (supply 2 each) can only reach col 0 (demand 1).
        let p = TransportProblem {
            row_supply: vec![2, 2],
            col_demand: vec![1, 3],
            cost: vec![
                vec![Cell::Cost(1, 0), Cell::Forbidden],
                vec![Cell::Cost(1, 0), Cell::Cost(1, 0)],
            ],
        };
        // Row 0 needs 2 units into col 0 (demand 1): infeasible.
        assert!(solve_transport(&p).is_none());
    }

    #[test]
    fn lexicographic_vmass_tiebreak() {
        // Two flows with equal size totals; vmass must decide.
        let p = TransportProblem {
            row_supply: vec![1, 1],
            col_demand: vec![1, 1],
            cost: vec![
                // diagonal: sizes 5+5=10, vmass 3+3=6
                // crossed:  sizes 5+5=10, vmass 1+1=2
                vec![Cell::Cost(5, 3), Cell::Cost(5, 1)],
                vec![Cell::Cost(5, 1), Cell::Cost(5, 3)],
            ],
        };
        let sol = solve_transport(&p).unwrap();
        check_margins(&p, &sol);
        assert_eq!(sol.total, (10, 2), "vmass must break the size tie");
    }

    #[test]
    fn zero_cost_cells() {
        let p = TransportProblem {
            row_supply: vec![2],
            col_demand: vec![1, 1],
            cost: vec![vec![Cell::Cost(0, 0), Cell::Cost(0, 0)]],
        };
        let sol = solve_transport(&p).unwrap();
        check_margins(&p, &sol);
        assert_eq!(sol.total, (0, 0));
    }

    #[test]
    fn large_multiplicities_bottleneck() {
        // Bottleneck augmentation must handle this without 2M iterations.
        let m = 1_000_000u32;
        let p = TransportProblem {
            row_supply: vec![m, m],
            col_demand: vec![m, m],
            cost: vec![
                vec![Cell::Cost(1, 0), Cell::Cost(2, 0)],
                vec![Cell::Cost(2, 0), Cell::Cost(1, 0)],
            ],
        };
        let sol = solve_transport(&p).unwrap();
        check_margins(&p, &sol);
        assert_eq!(sol.total.0, 2 * m as u128);
    }

    #[test]
    fn u32_max_multiplicities_no_overflow() {
        let m = u32::MAX;
        let p = TransportProblem {
            row_supply: vec![m, m],
            col_demand: vec![m, m],
            cost: vec![
                vec![Cell::Cost(m, m), Cell::Forbidden],
                vec![Cell::Forbidden, Cell::Cost(m, m)],
            ],
        };
        let sol = solve_transport(&p).unwrap();
        check_margins(&p, &sol);
        let expected = 2u128 * m as u128 * m as u128;
        assert_eq!(sol.total, (expected, expected));
    }

    #[test]
    fn differential_random_small() {
        // Deterministic pseudo-random exploration of small instances.
        let mut seed: u64 = 0x9E3779B97F4A7C15;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _case in 0..200 {
            let rows = 1 + (next() % 3) as usize;
            let cols = 1 + (next() % 3) as usize;
            // Random margins with equal totals: generate row supplies, then
            // distribute the same total across columns.
            let row_supply: Vec<u32> = (0..rows).map(|_| 1 + (next() % 3) as u32).collect();
            let total: u32 = row_supply.iter().sum();
            let mut col_demand = vec![0u32; cols];
            let mut rem = total;
            for j in 0..cols - 1 {
                let d = next() as u32 % (rem + 1);
                col_demand[j] = d;
                rem -= d;
            }
            col_demand[cols - 1] = rem;

            let cost: Vec<Vec<Cell>> = (0..rows)
                .map(|_| {
                    (0..cols)
                        .map(|_| {
                            if next() % 5 == 0 {
                                Cell::Forbidden
                            } else {
                                Cell::Cost((next() % 10) as u32, (next() % 10) as u32)
                            }
                        })
                        .collect()
                })
                .collect();

            let p = TransportProblem {
                row_supply,
                col_demand,
                cost,
            };
            let flow = solve_transport(&p);
            let reference = exhaustive_min(&p);
            match (flow, reference) {
                (Some(sol), Some(expected)) => {
                    check_margins(&p, &sol);
                    assert_eq!(
                        sol.total, expected,
                        "flow quality diverged from exhaustive minimum on {p:?}"
                    );
                }
                (None, None) => {}
                (flow, reference) => {
                    panic!("feasibility disagreement on {p:?}: flow={flow:?} ref={reference:?}");
                }
            }
        }
    }

    #[test]
    fn determinism() {
        let p = TransportProblem {
            row_supply: vec![2, 2],
            col_demand: vec![2, 2],
            cost: vec![
                vec![Cell::Cost(1, 1), Cell::Cost(1, 1)],
                vec![Cell::Cost(1, 1), Cell::Cost(1, 1)],
            ],
        };
        let a = solve_transport(&p).unwrap();
        let b = solve_transport(&p).unwrap();
        assert_eq!(a.flow, b.flow, "equal-cost ties must resolve identically");
    }
}
