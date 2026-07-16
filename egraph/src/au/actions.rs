// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Action generation per node kind (§3.4).
//!
//! For a class pair `(l, r)`, actions are the ways to factor both classes through a
//! common operator. Dispatch is on the operator's `OpKind`. Results are cached by
//! `(l, r)` and shared across contexts; cycle filtering happens at the OR node level.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::id::ENodeKind;
use crate::literal::LitVal;

use super::AuClassId;
use super::egraph_api::AuSnapshot;

/// One action: an operator plus its paired children with multiplicities.
#[derive(Debug, Clone)]
pub struct Action<O: DenseId> {
    pub op: O,
    pub pairs: Vec<ActionPair>,
}

/// A single child-pair in an action. `count` is the multiplicity (>1 for AC repeated children).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ActionPair {
    pub left: AuClassId,
    pub right: AuClassId,
    pub count: u32,
}

/// Default maximum number of AC matrices to materialize before using lazy chain states.
pub const DEFAULT_A_MAX: usize = 32;

/// The action cache: maps class pair `(l, r)` to a list of actions.
/// Semi-persistent by length-based truncation: mark saves the entry count,
/// restore clears entries added after the mark. Since actions are deterministic
/// and derived from the class pair's members (which are part of the immutable
/// snapshot), re-deriving them after restore produces the same result; the cache
/// is purely a performance optimization.
#[derive(Debug)]
pub struct ActionCache<O: DenseId> {
    keys: Vec<(AuClassId, AuClassId)>,
    values: Vec<Vec<Action<O>>>,
    index: hashbrown::HashMap<(AuClassId, AuClassId), usize>,
    a_max: usize,
}

/// Token for restoring an `ActionCache`.
#[derive(Clone, Copy, Debug)]
pub struct ActionCacheToken {
    len: usize,
}

impl<O: DenseId> ActionCache<O> {
    pub fn new(a_max: usize) -> Self {
        ActionCache {
            keys: Vec::new(),
            values: Vec::new(),
            index: hashbrown::HashMap::new(),
            a_max,
        }
    }

    pub fn get(&self, l: AuClassId, r: AuClassId) -> Option<&[Action<O>]> {
        self.index
            .get(&(l, r))
            .map(|&idx| self.values[idx].as_slice())
    }

    pub fn insert(&mut self, l: AuClassId, r: AuClassId, actions: Vec<Action<O>>) {
        let idx = self.keys.len();
        self.keys.push((l, r));
        self.values.push(actions);
        self.index.insert((l, r), idx);
    }

    pub fn a_max(&self) -> usize {
        self.a_max
    }

    pub fn mark(&self) -> ActionCacheToken {
        ActionCacheToken {
            len: self.keys.len(),
        }
    }

    pub fn restore(&mut self, token: ActionCacheToken) {
        self.keys.truncate(token.len);
        self.values.truncate(token.len);
        self.index.clear();
        for (i, key) in self.keys.iter().enumerate() {
            self.index.insert(*key, i);
        }
    }
}

impl<O: DenseId> Default for ActionCache<O> {
    fn default() -> Self {
        Self::new(DEFAULT_A_MAX)
    }
}

/// Generate all actions for a class pair `(l, r)` by scanning their common operators.
/// Actions are NOT cycle-filtered here; that is done at the OR-node level.
pub fn generate_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    cache: &mut ActionCache<Cfg::O>,
    l: AuClassId,
    r: AuClassId,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if cache.get(l, r).is_some() {
        return;
    }

    let eg = snap.egraph();
    let members_l = snap.members(l);
    let members_r = snap.members(r);
    let a_max = cache.a_max();

    let mut actions: Vec<Action<Cfg::O>> = Vec::new();

    // Group members by op (they are already sorted by op).
    let mut il = 0;
    let mut ir = 0;

    while il < members_l.len() && ir < members_r.len() {
        let (op_l, _) = members_l[il];
        let (op_r, _) = members_r[ir];

        match op_l.to_usize().cmp(&op_r.to_usize()) {
            std::cmp::Ordering::Less => {
                // Advance l past this op.
                while il < members_l.len() && members_l[il].0 == op_l {
                    il += 1;
                }
            }
            std::cmp::Ordering::Greater => {
                // Advance r past this op.
                while ir < members_r.len() && members_r[ir].0 == op_r {
                    ir += 1;
                }
            }
            std::cmp::Ordering::Equal => {
                // Common operator: collect all l-members and r-members with this op.
                let il_start = il;
                while il < members_l.len() && members_l[il].0 == op_l {
                    il += 1;
                }
                let ir_start = ir;
                while ir < members_r.len() && members_r[ir].0 == op_r {
                    ir += 1;
                }

                let l_nodes = &members_l[il_start..il];
                let r_nodes = &members_r[ir_start..ir];

                let kind = eg.ops().info(op_l).canon_class();
                match kind {
                    ENodeKind::Plain0 => {
                        // Nullary: one action with no children (the op itself matches).
                        actions.push(Action {
                            op: op_l,
                            pairs: Vec::new(),
                        });
                    }
                    ENodeKind::Plain1
                    | ENodeKind::Plain2
                    | ENodeKind::Plain3
                    | ENodeKind::PlainN => {
                        generate_ordered_actions(snap, eg, op_l, l_nodes, r_nodes, &mut actions);
                    }
                    ENodeKind::Seq => {
                        generate_seq_actions(snap, eg, op_l, l_nodes, r_nodes, &mut actions);
                    }
                    ENodeKind::SPair => {
                        generate_spair_actions(snap, eg, op_l, l_nodes, r_nodes, &mut actions);
                    }
                    ENodeKind::MSet => {
                        generate_mset_actions(
                            snap,
                            eg,
                            op_l,
                            l_nodes,
                            r_nodes,
                            a_max,
                            &mut actions,
                        );
                    }
                    ENodeKind::Set => {
                        generate_set_actions(snap, eg, op_l, l_nodes, r_nodes, a_max, &mut actions);
                    }
                    ENodeKind::Lit => {
                        generate_lit_actions(eg, op_l, l_nodes, r_nodes, &mut actions);
                    }
                }
            }
        }
    }

    cache.insert(l, r, actions);
}

/// Ordered operators (fixed arity): positional zip of same-arity member pairs (§3.4.1).
fn generate_ordered_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    actions: &mut Vec<Action<Cfg::O>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    for &(_, l_id) in l_nodes {
        let l_arity = eg.for_each_child(l_id, |_, _| {});
        for &(_, r_id) in r_nodes {
            let r_arity = eg.for_each_child(r_id, |_, _| {});
            if l_arity != r_arity {
                continue;
            }
            // Positional zip.
            let mut pairs = Vec::with_capacity(l_arity);
            let mut l_children = Vec::with_capacity(l_arity);
            let mut r_children = Vec::with_capacity(r_arity);
            eg.for_each_child(l_id, |child, _| l_children.push(child));
            eg.for_each_child(r_id, |child, _| r_children.push(child));

            for i in 0..l_arity {
                let lc = snap.class_of(l_children[i]).unwrap();
                let rc = snap.class_of(r_children[i]).unwrap();
                pairs.push(ActionPair {
                    left: lc,
                    right: rc,
                    count: 1,
                });
            }
            actions.push(Action { op, pairs });
        }
    }
}

/// Associative operators (sequences): milestone = one positional action when lengths
/// are equal, none otherwise (§3.4.3).
fn generate_seq_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    actions: &mut Vec<Action<Cfg::O>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    // Same logic as ordered: positional zip only when lengths match.
    generate_ordered_actions(snap, eg, op, l_nodes, r_nodes, actions);
}

/// Commutative binary operators (sorted pairs): two orientations per member pair (§3.4.2).
fn generate_spair_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    actions: &mut Vec<Action<Cfg::O>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    for &(_, l_id) in l_nodes {
        let mut l_children = [AuClassId::default(); 2];
        let mut li = 0;
        eg.for_each_child(l_id, |child, _| {
            if li < 2 {
                l_children[li] = snap.class_of(child).unwrap();
                li += 1;
            }
        });

        for &(_, r_id) in r_nodes {
            let mut r_children = [AuClassId::default(); 2];
            let mut ri = 0;
            eg.for_each_child(r_id, |child, _| {
                if ri < 2 {
                    r_children[ri] = snap.class_of(child).unwrap();
                    ri += 1;
                }
            });

            // Orientation 1: positional (a,c), (b,d).
            let pairs1 = vec![
                ActionPair {
                    left: l_children[0],
                    right: r_children[0],
                    count: 1,
                },
                ActionPair {
                    left: l_children[1],
                    right: r_children[1],
                    count: 1,
                },
            ];
            actions.push(Action { op, pairs: pairs1 });

            // Orientation 2: crossed (a,d), (b,c) — skip if same as orientation 1.
            if !(l_children[0] == l_children[1] || r_children[0] == r_children[1]) {
                let pairs2 = vec![
                    ActionPair {
                        left: l_children[0],
                        right: r_children[1],
                        count: 1,
                    },
                    ActionPair {
                        left: l_children[1],
                        right: r_children[0],
                        count: 1,
                    },
                ];
                actions.push(Action { op, pairs: pairs2 });
            }
        }
    }
}

/// AC operators (multisets): matching-count matrix enumeration (§3.4.4).
fn generate_mset_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    a_max: usize,
    actions: &mut Vec<Action<Cfg::O>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut l_mset_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();
    let mut r_mset_buf: Vec<(Cfg::G, Cfg::M)> = Vec::new();

    for &(_, l_id) in l_nodes {
        eg.mset_children(l_id, &mut l_mset_buf);
        let l_total: u32 = l_mset_buf.iter().map(|(_, m)| Into::<u32>::into(*m)).sum();

        for &(_, r_id) in r_nodes {
            eg.mset_children(r_id, &mut r_mset_buf);
            let r_total: u32 = r_mset_buf.iter().map(|(_, m)| Into::<u32>::into(*m)).sum();

            // Milestone: equal total only (§3.4.4).
            if l_total != r_total {
                continue;
            }

            // Convert to (AuClassId, u32) for matrix enumeration.
            let l_classes: Vec<(AuClassId, u32)> = l_mset_buf
                .iter()
                .map(|(g, m)| (snap.class_of(*g).unwrap(), (*m).into()))
                .collect();
            let r_classes: Vec<(AuClassId, u32)> = r_mset_buf
                .iter()
                .map(|(g, m)| (snap.class_of(*g).unwrap(), (*m).into()))
                .collect();

            enumerate_matrices(op, &l_classes, &r_classes, a_max, actions);
        }
    }
}

/// ACI operators (sets): bijection enumeration for equal-cardinality sets (§3.4.5).
fn generate_set_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    a_max: usize,
    actions: &mut Vec<Action<Cfg::O>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    for &(_, l_id) in l_nodes {
        let mut l_children: Vec<AuClassId> = Vec::new();
        eg.for_each_child(l_id, |child, _| {
            l_children.push(snap.class_of(child).unwrap());
        });

        for &(_, r_id) in r_nodes {
            let mut r_children: Vec<AuClassId> = Vec::new();
            eg.for_each_child(r_id, |child, _| {
                r_children.push(snap.class_of(child).unwrap());
            });

            if l_children.len() != r_children.len() {
                continue;
            }

            // All multiplicities are 1: use mset matrix enumeration.
            let l_classes: Vec<(AuClassId, u32)> = l_children.iter().map(|&c| (c, 1)).collect();
            let r_classes: Vec<(AuClassId, u32)> = r_children.iter().map(|&c| (c, 1)).collect();

            enumerate_matrices(op, &l_classes, &r_classes, a_max, actions);
        }
    }
}

/// Literals: same-value pairing only (§3.4.6).
fn generate_lit_actions<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    eg: &EGraph<Cfg, L, T, P>,
    op: Cfg::O,
    l_nodes: &[(Cfg::O, Cfg::G)],
    r_nodes: &[(Cfg::O, Cfg::G)],
    actions: &mut Vec<Action<Cfg::O>>,
) where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    for &(_, l_id) in l_nodes {
        let l_val = eg.get_lit_val_id(l_id);
        for &(_, r_id) in r_nodes {
            let r_val = eg.get_lit_val_id(r_id);
            if l_val == r_val {
                // Terminal action with no children.
                actions.push(Action {
                    op,
                    pairs: Vec::new(),
                });
            }
        }
    }
}

// ---------------------------------------------------------------------------
// AC matrix enumeration
// ---------------------------------------------------------------------------

/// Enumerate all valid matching-count matrices for multisets `M` and `N` with equal
/// total multiplicity. A matrix X has `x[i][j]` copies of pair `(l_i, r_j)`;
/// row i sums to `m_i`, column j sums to `n_j`.
///
/// If the number of matrices exceeds `a_max`, only `a_max` are emitted (greedy-first).
/// The full lazy chain-state extension is deferred to a future milestone.
fn enumerate_matrices<O: DenseId>(
    op: O,
    l_classes: &[(AuClassId, u32)],
    r_classes: &[(AuClassId, u32)],
    a_max: usize,
    actions: &mut Vec<Action<O>>,
) {
    let rows = l_classes.len();
    let cols = r_classes.len();

    if rows == 0 || cols == 0 {
        return;
    }

    let row_sums: Vec<u32> = l_classes.iter().map(|(_, m)| *m).collect();
    let col_sums: Vec<u32> = r_classes.iter().map(|(_, m)| *m).collect();

    // Enumerate via backtracking: fill row by row, left to right.
    let mut matrix: Vec<Vec<u32>> = vec![vec![0; cols]; rows];
    let mut count = 0;

    enumerate_row(
        op,
        l_classes,
        r_classes,
        &row_sums,
        &col_sums,
        &mut matrix,
        0,
        &mut col_sums.clone(),
        a_max,
        &mut count,
        actions,
    );
}

fn enumerate_row<O: DenseId>(
    op: O,
    l_classes: &[(AuClassId, u32)],
    r_classes: &[(AuClassId, u32)],
    row_sums: &[u32],
    _col_sums: &[u32],
    matrix: &mut [Vec<u32>],
    row: usize,
    remaining_col: &mut Vec<u32>,
    a_max: usize,
    count: &mut usize,
    actions: &mut Vec<Action<O>>,
) {
    if *count >= a_max {
        return;
    }

    let rows = l_classes.len();
    let cols = r_classes.len();

    if row == rows {
        // Complete matrix: emit an action.
        let mut pairs: Vec<ActionPair> = Vec::new();
        for i in 0..rows {
            for j in 0..cols {
                if matrix[i][j] > 0 {
                    pairs.push(ActionPair {
                        left: l_classes[i].0,
                        right: r_classes[j].0,
                        count: matrix[i][j],
                    });
                }
            }
        }
        actions.push(Action { op, pairs });
        *count += 1;
        return;
    }

    // Fill row `row`: distribute row_sums[row] among columns, respecting remaining_col.
    distribute_row(
        op,
        l_classes,
        r_classes,
        row_sums,
        _col_sums,
        matrix,
        row,
        0,
        row_sums[row],
        remaining_col,
        a_max,
        count,
        actions,
    );
}

#[allow(clippy::too_many_arguments)]
fn distribute_row<O: DenseId>(
    op: O,
    l_classes: &[(AuClassId, u32)],
    r_classes: &[(AuClassId, u32)],
    row_sums: &[u32],
    col_sums: &[u32],
    matrix: &mut [Vec<u32>],
    row: usize,
    col: usize,
    remaining: u32,
    remaining_col: &mut Vec<u32>,
    a_max: usize,
    count: &mut usize,
    actions: &mut Vec<Action<O>>,
) {
    if *count >= a_max {
        return;
    }

    let cols = r_classes.len();

    if col == cols - 1 {
        // Last column gets whatever remains (if it fits).
        if remaining <= remaining_col[col] {
            matrix[row][col] = remaining;
            remaining_col[col] -= remaining;
            enumerate_row(
                op,
                l_classes,
                r_classes,
                row_sums,
                col_sums,
                matrix,
                row + 1,
                remaining_col,
                a_max,
                count,
                actions,
            );
            remaining_col[col] += remaining;
            matrix[row][col] = 0;
        }
        return;
    }

    // Try greedy-first: assign diagonal value first when l_classes[row] == r_classes[col].
    // For general ordering: try from min(remaining, remaining_col[col]) down to 0.
    let max_assign = remaining.min(remaining_col[col]);
    // Greedy-first: start with the diagonal match if classes are the same.
    let greedy_val = if l_classes[row].0 == r_classes[col].0 {
        max_assign
    } else {
        0
    };

    // Emit greedy value first, then the rest.
    let mut tried_greedy = false;
    for val in (0..=max_assign).rev() {
        if val == greedy_val && !tried_greedy {
            tried_greedy = true;
        } else if val == greedy_val {
            continue;
        } else if !tried_greedy {
            // Emit greedy first.
            tried_greedy = true;
            matrix[row][col] = greedy_val;
            remaining_col[col] -= greedy_val;
            distribute_row(
                op,
                l_classes,
                r_classes,
                row_sums,
                col_sums,
                matrix,
                row,
                col + 1,
                remaining - greedy_val,
                remaining_col,
                a_max,
                count,
                actions,
            );
            remaining_col[col] += greedy_val;
            matrix[row][col] = 0;
            if *count >= a_max {
                return;
            }
            if val == greedy_val {
                continue;
            }
        }

        matrix[row][col] = val;
        remaining_col[col] -= val;
        distribute_row(
            op,
            l_classes,
            r_classes,
            row_sums,
            col_sums,
            matrix,
            row,
            col + 1,
            remaining - val,
            remaining_col,
            a_max,
            count,
            actions,
        );
        remaining_col[col] += val;
        matrix[row][col] = 0;
        if *count >= a_max {
            return;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

    /// Appendix B worked example: AU(and{a,b,c}, and{b,c,d}) produces exactly 6 actions.
    #[test]
    fn appendix_b_six_actions() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let and_op = eg.register_set("and", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let and_abc = eg.add(and_op, &[a, b, c]);
        let and_bcd = eg.add(and_op, &[b, c, d]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(and_abc).unwrap();
        let r = snap.class_of(and_bcd).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, l, r);

        let acts = cache.get(l, r).unwrap();
        // 3 distinct children on each side, all mult 1 -> 3! = 6 bijections.
        assert_eq!(acts.len(), 6, "expected 6 actions, got {}", acts.len());

        // Each action should have 3 pairs with count 1.
        for action in acts {
            assert_eq!(action.pairs.len(), 3);
            for pair in &action.pairs {
                assert_eq!(pair.count, 1);
            }
        }
    }

    /// AC with repeated children: AU(plus{a,a}, plus{a,b}) -> matrices with margin (2) and (1,1).
    #[test]
    fn ac_repeated_children() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let plus_op = eg.register_mset("plus", int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let plus_aa = eg.add(plus_op, &[a, a]);
        let plus_ab = eg.add(plus_op, &[a, b]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(plus_aa).unwrap();
        let r = snap.class_of(plus_ab).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, l, r);

        let acts = cache.get(l, r).unwrap();
        // L = {a^2}, R = {a^1, b^1}. Row margin = [2], col margins = [1, 1].
        // Only one matrix: x[0][0]=1, x[0][1]=1 (the row of 2 is split across 2 cols).
        assert_eq!(acts.len(), 1, "expected 1 action, got {}", acts.len());
        assert_eq!(acts[0].pairs.len(), 2);
    }

    /// Ordered: f(a,b) and f(c,d) produce one positional action with 2 pairs.
    #[test]
    fn ordered_positional_zip() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let f_op = eg.register_op2("f", int, int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let fab = eg.add(f_op, &[a, b]);
        let fcd = eg.add(f_op, &[c, d]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(fab).unwrap();
        let r = snap.class_of(fcd).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, l, r);

        let acts = cache.get(l, r).unwrap();
        assert_eq!(acts.len(), 1);
        assert_eq!(acts[0].pairs.len(), 2);
        assert_eq!(acts[0].pairs[0].count, 1);
        assert_eq!(acts[0].pairs[1].count, 1);
    }

    /// SPair: eq(a,b) vs eq(c,d) produces 2 orientations.
    #[test]
    fn spair_two_orientations() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let eq_op = eg.register_c("eq", [int, int], int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let eq_ab = eg.add(eq_op, &[a, b]);
        let eq_cd = eg.add(eq_op, &[c, d]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(eq_ab).unwrap();
        let r = snap.class_of(eq_cd).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, l, r);

        let acts = cache.get(l, r).unwrap();
        assert_eq!(acts.len(), 2, "expected 2 orientations");
    }

    /// SPair dedup when a == b: eq(a,a) vs eq(c,d) produces only 1 orientation.
    #[test]
    fn spair_dedup_same_children() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let c_op = eg.register_op0("c", int);
        let d_op = eg.register_op0("d", int);
        let eq_op = eg.register_c("eq", [int, int], int);

        let a = eg.add(a_op, &[]);
        let c = eg.add(c_op, &[]);
        let d = eg.add(d_op, &[]);
        let eq_aa = eg.add(eq_op, &[a, a]);
        let eq_cd = eg.add(eq_op, &[c, d]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let l = snap.class_of(eq_aa).unwrap();
        let r = snap.class_of(eq_cd).unwrap();

        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, l, r);

        let acts = cache.get(l, r).unwrap();
        assert_eq!(
            acts.len(),
            1,
            "dedup: only 1 orientation when l children are same"
        );
    }

    /// Literal: same value matches, different values don't.
    #[test]
    fn literal_same_value() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let lit_op = eg.register_lit("intlit", int);

        let val1 = eg.intern_lit(crate::literal::NiraLitVal::Int(42.into()));
        let val2 = eg.intern_lit(crate::literal::NiraLitVal::Int(99.into()));

        let l = eg.add_lit(lit_op, val1);
        let r1 = eg.add_lit(lit_op, val1);
        let r2 = eg.add_lit(lit_op, val2);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(l).unwrap();
        let r1c = snap.class_of(r1).unwrap();
        let r2c = snap.class_of(r2).unwrap();

        // Same value -> 1 action.
        let mut cache = ActionCache::new(100);
        generate_actions(&snap, &mut cache, lc, r1c);
        let acts = cache.get(lc, r1c).unwrap();
        assert_eq!(acts.len(), 1);

        // Different value -> 0 actions.
        generate_actions(&snap, &mut cache, lc, r2c);
        let acts = cache.get(lc, r2c).unwrap();
        assert_eq!(acts.len(), 0);
    }
}
