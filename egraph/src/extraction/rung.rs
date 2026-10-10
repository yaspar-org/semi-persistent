// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The ladder of encodings.
//!
//! | rung | exposes | trees of a flat node |
//! | --- | --- | --- |
//! | [`Selection`] | a selector per e-class and per e-node | the flat node as written |
//! | [`Levels`] | plus a depth per operand of each flat node | chains of flat blocks |
//! | [`Splits`] | plus split labels per level | every unordered tree, or every binary one |
//! | [`Orders`] | plus a position per operand in its block | every ordered tree |
//!
//! Each rung contains the one below and gives its variables the same meaning.
//! Constraints differ by rung: the chain family's constraints are not the split
//! family's, so each rung emits its own over the shared variables.
//!
//! A flat node's operands are its distinct child classes: a class occurring several
//! times is one operand (maximum-partition semantics).
//!
//! # Tree variables
//!
//! Per operand `i` of a flat node with `k` operands and depth bound `L = k - 1`:
//! a depth `D(i)` in `1..=L`, the depth of the node `i` is a direct operand of; for
//! each depth `d < D(i)` a label in `0..B`, which sub-block of its depth-`d` block `i`
//! continues into; and under [`Orders`] a position per depth. Two operands are in the
//! same block at depth `d` when they agree on every label above `d`. Labels are a
//! restricted growth string within each block, so each unordered tree has exactly one
//! assignment; positions order the operands of each block.

use crate::extraction::Lit;
use crate::extraction::cost::Cost;
use crate::extraction::graph::{ClassId, Graph, Node, NodeId, Term, Tree};
use crate::extraction::oint::{Build, Exact, OInt, Over, RecDef, Under};
use std::collections::BTreeMap;
use std::sync::Arc;

/// The largest arity whose tree is a decision; above it the node stays flat.
pub const MAX_ARITY: usize = 16;
/// The largest arity whose operand order is a decision under [`Orders`].
pub const MAX_ORDERED_ARITY: usize = 8;

/// An internal node a flat node's tree may contain.
#[derive(Clone, Debug)]
pub struct Inner {
    /// True exactly when the flat node is selected and its tree contains this node.
    pub exists: Lit,
    /// Operands under this node, each under its gates.
    pub members: Vec<(Vec<Lit>, ClassId)>,
    /// Operands that are its siblings, each under its gates. A sibling sub-block is
    /// represented by its members.
    pub siblings: Vec<(Vec<Lit>, ClassId)>,
}

/// What every rung offers a cost function.
pub trait Rung: Send + Sync {
    fn selection(&self) -> &Selection;
    fn graph(&self) -> &Graph {
        &self.selection().graph
    }
    /// The siblings of class `c` under parent `n`, each under the literals that make
    /// it one. The node's own selection is among the gates.
    fn siblings(&self, n: NodeId, c: ClassId) -> Vec<(Vec<Lit>, ClassId)>;
    /// The internal nodes of `n`'s tree. Empty below [`Levels`].
    fn inner_nodes(&self, n: NodeId) -> &[Inner];
    /// The term a model denotes.
    fn decode(&self, model: &dyn Fn(u32) -> bool) -> Term;
    /// The value of every rung literal under `term`, exactly as the term determines
    /// it, whatever the model that produced the term.
    fn canonical(&self, term: &Term) -> BTreeMap<u32, bool>;
    /// Literals of the model that fix its term, for excluding exactly that term.
    fn term_literals(&self, model: &dyn Fn(u32) -> bool, term: &Term) -> Vec<Lit>;
    fn name(&self) -> &'static str;
    /// This rung's depths, if it exposes them.
    fn nesting(&self) -> Option<&dyn Nesting> {
        None
    }
    /// This rung's operand positions, if it exposes them.
    fn ordering(&self) -> Option<&dyn Ordering> {
        None
    }
}

/// Rungs that expose depths.
pub trait Nesting: Rung {
    /// The depth of operand `c` of flat node `n`, when its tree is a decision.
    fn depth(&self, b: &mut Build, n: NodeId, c: ClassId) -> Option<OInt<Exact>>;
}

/// Rungs that expose operand order.
pub trait Ordering: Nesting {
    /// The position of operand `c` of `n` within its block at depth `d`, for `d` from 1
    /// (the node itself) to the tree's depth. `None` for any other `d`: no constraint
    /// decides a position there, so a value would come from the model, not the term.
    fn position(&self, b: &mut Build, n: NodeId, c: ClassId, d: usize) -> Option<OInt<Exact>>;
}

// --- selection -------------------------------------------------------------------

/// Rung 0: a selector per e-class and per e-node, with the validity constraints.
pub struct Selection {
    pub graph: Arc<Graph>,
    pub reachable: Vec<ClassId>,
    sel_class: Vec<Option<Lit>>,
    sel_node: Vec<Option<Lit>>,
    /// The fixed bracketing of every candidate fold of three or more operands.
    folds: Vec<Option<crate::extraction::seq::SeqVars>>,
    parents: Vec<Vec<NodeId>>,
}

impl Selection {
    /// Allocate selectors and emit: the root is selected; a selected class selects
    /// exactly one candidate; a selected node selects its class and its children.
    pub fn build(graph: Arc<Graph>, b: &mut Build) -> Selection {
        let reachable = graph.reachable();
        let mut sel_class = vec![None; graph.classes.len()];
        let mut sel_node = vec![None; graph.nodes.len()];
        for &c in &reachable {
            sel_class[c] = Some(b.target().fresh());
            for n in graph.candidates(c) {
                sel_node[n] = Some(b.target().fresh());
            }
        }
        let t = b.target();
        t.clause(&[sel_class[graph.root].expect("root reachable")]);
        let mut parents = vec![Vec::new(); graph.classes.len()];
        for &c in &reachable {
            let ac = sel_class[c].unwrap();
            let members: Vec<NodeId> = graph.candidates(c).collect();
            let mut any = vec![ac.not()];
            for &n in &members {
                let an = sel_node[n].unwrap();
                any.push(an);
                t.clause(&[an.not(), ac]);
                for k in graph.operands(n) {
                    t.clause(&[an.not(), sel_class[k].unwrap()]);
                    parents[k].push(n);
                }
            }
            t.clause(&any);
            // At most one member, sequentially: 3m - 4 clauses rather than m²/2.
            let mut prev: Option<Lit> = None;
            for (i, &n) in members.iter().enumerate() {
                let an = sel_node[n].unwrap();
                if let Some(p) = prev {
                    t.clause(&[an.not(), p.not()]);
                }
                if i + 1 < members.len() {
                    let s = t.fresh();
                    t.clause(&[an.not(), s]);
                    if let Some(p) = prev {
                        t.clause(&[p.not(), s]);
                    }
                    prev = Some(s);
                }
            }
        }
        let mut folds: Vec<Option<crate::extraction::seq::SeqVars>> =
            (0..graph.nodes.len()).map(|_| None).collect();
        for &c in &reachable {
            for n in graph.candidates(c) {
                if let Some(dir) = graph.nodes[n].kind.fold()
                    && graph.nodes[n].children.len() >= 3
                {
                    let sel = sel_node[n].unwrap();
                    folds[n] = Some(crate::extraction::seq::SeqVars::fold(
                        b,
                        sel,
                        graph.nodes[n].children.clone(),
                        dir == crate::extraction::graph::Assoc::Left,
                    ));
                }
            }
        }
        Selection {
            graph,
            reachable,
            sel_class,
            sel_node,
            parents,
            folds,
        }
    }

    /// True exactly when class `c` is selected.
    pub fn class(&self, c: ClassId) -> Lit {
        self.sel_class[c].unwrap_or(Lit::False)
    }

    /// True exactly when node `n` is the selected member of its class.
    pub fn node(&self, n: NodeId) -> Lit {
        self.sel_node[n].unwrap_or(Lit::False)
    }

    /// Nodes that have `c` as an operand, once each.
    pub fn parents(&self, c: ClassId) -> &[NodeId] {
        &self.parents[c]
    }

    fn decode_selection(&self, model: &dyn Fn(u32) -> bool) -> Vec<Option<NodeId>> {
        let mut sel = vec![None; self.graph.classes.len()];
        for (n, l) in self.sel_node.iter().enumerate() {
            if let Some(Lit::Var { var, .. }) = l {
                let c = self.graph.nodes[n].class;
                if model(*var) && sel[c].is_none() {
                    sel[c] = Some(n);
                }
            }
        }
        // Keep only the classes the root reaches: a model may select classes the
        // term does not contain, and those are not part of the term.
        let term = Term {
            selection: sel.clone(),
            trees: BTreeMap::new(),
        };
        let mut keep = vec![false; sel.len()];
        let mut stack = vec![self.graph.root];
        let mut seen = vec![false; sel.len()];
        while let Some(c) = stack.pop() {
            if std::mem::replace(&mut seen[c], true) {
                continue;
            }
            keep[c] = true;
            if let Some(n) = term.selection[c] {
                stack.extend(self.graph.nodes[n].children.iter().copied());
            }
        }
        sel.iter()
            .enumerate()
            .map(|(c, &n)| if keep[c] { n } else { None })
            .collect()
    }

    fn canonical_selection(&self, term: &Term, out: &mut BTreeMap<u32, bool>) {
        for (c, l) in self.sel_class.iter().enumerate() {
            if let Some(Lit::Var { var, .. }) = l {
                out.insert(*var, term.selection[c].is_some());
            }
        }
        for (n, l) in self.sel_node.iter().enumerate() {
            if let Some(Lit::Var { var, .. }) = l {
                let c = self.graph.nodes[n].class;
                out.insert(*var, term.selection[c] == Some(n));
            }
        }
    }

    fn selection_literals(&self, term: &Term) -> Vec<Lit> {
        term.selection
            .iter()
            .filter_map(|n| n.and_then(|n| self.sel_node[n]))
            .collect()
    }

    /// The siblings of `c` under `n` with no tree decided: a fold's by its fixed
    /// bracketing, any other node's all its other operands.
    fn node_siblings(&self, n: NodeId, c: ClassId) -> Vec<(Vec<Lit>, ClassId)> {
        match &self.folds[n] {
            Some(f) => f.sibling_parts(self.node(n), c),
            None => self.flat_siblings(n, c),
        }
    }

    fn fold_inner(&self, n: NodeId) -> &[Inner] {
        self.folds[n]
            .as_ref()
            .map(|f| f.inner.as_slice())
            .unwrap_or(&[])
    }

    fn flat_siblings(&self, n: NodeId, c: ClassId) -> Vec<(Vec<Lit>, ClassId)> {
        let sel = self.node(n);
        self.graph
            .operands(n)
            .into_iter()
            .filter(|&s| s != c)
            .map(|s| (vec![sel], s))
            .collect()
    }
}

impl Rung for Selection {
    fn selection(&self) -> &Selection {
        self
    }
    fn siblings(&self, n: NodeId, c: ClassId) -> Vec<(Vec<Lit>, ClassId)> {
        self.node_siblings(n, c)
    }
    fn inner_nodes(&self, n: NodeId) -> &[Inner] {
        self.fold_inner(n)
    }
    fn decode(&self, model: &dyn Fn(u32) -> bool) -> Term {
        Term {
            selection: self.decode_selection(model),
            trees: BTreeMap::new(),
        }
    }
    fn canonical(&self, term: &Term) -> BTreeMap<u32, bool> {
        let mut out = BTreeMap::new();
        self.canonical_selection(term, &mut out);
        out
    }
    fn term_literals(&self, _model: &dyn Fn(u32) -> bool, term: &Term) -> Vec<Lit> {
        self.selection_literals(term)
    }
    fn name(&self) -> &'static str {
        "selection"
    }
}

// --- tree variables --------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Family {
    Chains,
    Splits { binary: bool },
    Ordered,
}

/// Tree variables of one flat node.
struct TreeVars {
    kids: Vec<ClassId>,
    depth: usize,
    labels: usize,
    dep: Vec<Vec<Lit>>,
    lab: Vec<Vec<Vec<Lit>>>,
    same: Vec<Vec<Lit>>,
    /// `pos[i][d][p]`: `[position(i, d) >= p]`, when order is a decision.
    pos: Option<Vec<Vec<Vec<Lit>>>>,
    reps: Vec<(usize, usize, Lit)>,
    inner: Vec<Inner>,
}

fn pair(i: usize, s: usize, k: usize) -> usize {
    let (a, b) = if i < s { (i, s) } else { (s, i) };
    a * k + b
}

fn var_of(l: Lit) -> Option<u32> {
    if let Lit::Var { var, .. } = l {
        Some(var)
    } else {
        None
    }
}

impl TreeVars {
    fn new(b: &mut Build, sel: Lit, node: NodeId, kids: Vec<ClassId>, family: Family) -> TreeVars {
        let k = kids.len();
        let depth = k - 1;
        let labels = match family {
            Family::Chains => 1,
            Family::Splits { binary: true } => 2,
            _ => (k / 2).max(1),
        };
        let t = b.target();
        let mut dep = vec![vec![Lit::True; depth + 2]; k];
        for row in dep.iter_mut() {
            for d in 2..=depth {
                row[d] = t.fresh();
            }
            row[depth + 1] = Lit::False;
        }
        let mut lab = vec![vec![vec![Lit::True; labels + 1]; depth + 1]; k];
        for row in lab.iter_mut() {
            for d in 1..depth {
                for l in 1..labels {
                    row[d][l] = t.fresh();
                }
                row[d][labels] = Lit::False;
            }
        }
        let mut same = vec![Vec::new(); k * k];
        for i in 0..k {
            for s in (i + 1)..k {
                let mut v = vec![Lit::True; depth + 1];
                for d in 2..=depth {
                    v[d] = t.fresh();
                }
                same[pair(i, s, k)] = v;
            }
        }
        let pos = (family == Family::Ordered).then(|| {
            (0..k)
                .map(|_| {
                    (0..=depth)
                        .map(|_| {
                            let mut th = vec![Lit::True];
                            for _ in 1..k {
                                th.push(t.fresh());
                            }
                            th.push(Lit::False);
                            th
                        })
                        .collect()
                })
                .collect()
        });
        let _ = node;
        let mut tv = TreeVars {
            kids,
            depth,
            labels,
            dep,
            lab,
            same,
            pos,
            reps: Vec::new(),
            inner: Vec::new(),
        };
        tv.emit(b, sel, family);
        tv
    }

    fn same_at(&self, i: usize, s: usize, d: usize) -> Lit {
        if d <= 1 {
            Lit::True
        } else {
            self.same[pair(i, s, self.kids.len())][d]
        }
    }

    fn leaf_at(&self, i: usize, d: usize) -> [Lit; 2] {
        [self.dep[i][d], self.dep[i][d + 1].not()]
    }

    fn emit(&mut self, b: &mut Build, sel: Lit, family: Family) {
        let (k, depth, labels) = (self.kids.len(), self.depth, self.labels);
        {
            let t = b.target();
            for i in 0..k {
                for d in 2..=depth {
                    t.clause(&[self.dep[i][d].not(), self.dep[i][d - 1]]);
                }
                for d in 1..depth {
                    for l in 2..labels {
                        t.clause(&[self.lab[i][d][l].not(), self.lab[i][d][l - 1]]);
                    }
                    if labels > 1 {
                        t.clause(&[self.dep[i][d + 1], self.lab[i][d][1].not()]);
                    }
                }
            }
            for i in 0..k {
                for s in (i + 1)..k {
                    for d in 2..=depth {
                        let here = self.same_at(i, s, d);
                        t.clause(&[here.not(), self.same_at(i, s, d - 1)]);
                        t.clause(&[here.not(), self.dep[i][d]]);
                        t.clause(&[here.not(), self.dep[s][d]]);
                        for l in 1..labels {
                            let (x, y) = (self.lab[i][d - 1][l], self.lab[s][d - 1][l]);
                            t.clause(&[here.not(), x.not(), y]);
                            t.clause(&[here.not(), x, y.not()]);
                        }
                        for v in 0..labels {
                            t.clause(&[
                                self.same_at(i, s, d - 1).not(),
                                self.dep[i][d].not(),
                                self.dep[s][d].not(),
                                self.lab[i][d - 1][v].not(),
                                self.lab[i][d - 1][v + 1],
                                self.lab[s][d - 1][v].not(),
                                self.lab[s][d - 1][v + 1],
                                here,
                            ]);
                        }
                    }
                }
            }
            // Restricted growth: label `l` needs an earlier continuing block-mate
            // with label at least `l - 1`.
            for d in 1..depth {
                for i in 0..k {
                    for l in 1..labels {
                        let mut cl = vec![self.lab[i][d][l].not()];
                        for e in 0..i {
                            let x = t.fresh();
                            t.clause(&[x.not(), self.same_at(e, i, d)]);
                            t.clause(&[x.not(), self.dep[e][d + 1]]);
                            t.clause(&[x.not(), self.lab[e][d][l - 1]]);
                            cl.push(x);
                        }
                        t.clause(&cl);
                    }
                }
            }
            // A sub-block has at least two members.
            for d in 2..=depth {
                for i in 0..k {
                    let mut cl = vec![self.dep[i][d].not()];
                    for s in 0..k {
                        if s != i {
                            cl.push(self.same_at(i, s, d));
                        }
                    }
                    t.clause(&cl);
                }
            }
            // A block with a continuing member has a second operand.
            for d in 1..depth {
                for i in 0..k {
                    let mut cl = vec![self.dep[i][d + 1].not()];
                    for s in 0..k {
                        if s == i {
                            continue;
                        }
                        let leaf = t.fresh();
                        t.clause(&[leaf.not(), self.same_at(i, s, d)]);
                        t.clause(&[leaf.not(), self.dep[s][d + 1].not()]);
                        cl.push(leaf);
                        for l in 1..labels {
                            let diff = t.fresh();
                            let (x, y) = (self.lab[i][d][l], self.lab[s][d][l]);
                            t.clause(&[diff.not(), self.same_at(i, s, d)]);
                            t.clause(&[diff.not(), self.dep[s][d + 1]]);
                            t.clause(&[diff.not(), x, y]);
                            t.clause(&[diff.not(), x.not(), y.not()]);
                            cl.push(diff);
                        }
                    }
                    t.clause(&cl);
                }
            }
            if family == (Family::Splits { binary: true }) {
                for d in 1..=depth {
                    for i in 0..k {
                        let [li, ni] = self.leaf_at(i, d);
                        for s in 0..k {
                            if s == i || d == depth {
                                continue;
                            }
                            t.clause(&[
                                li.not(),
                                ni.not(),
                                self.same_at(i, s, d).not(),
                                self.dep[s][d + 1].not(),
                                self.lab[s][d][1].not(),
                            ]);
                        }
                        for j in (i + 1)..k {
                            let [lj, nj] = self.leaf_at(j, d);
                            let ij = self.same_at(i, j, d);
                            for s in 0..k {
                                if s == i || s == j {
                                    continue;
                                }
                                if d < depth {
                                    t.clause(&[
                                        li.not(),
                                        ni.not(),
                                        lj.not(),
                                        nj.not(),
                                        ij.not(),
                                        self.same_at(i, s, d).not(),
                                        self.dep[s][d + 1].not(),
                                    ]);
                                }
                                if s > j {
                                    let [ls, ns] = self.leaf_at(s, d);
                                    t.clause(&[
                                        li.not(),
                                        ni.not(),
                                        lj.not(),
                                        nj.not(),
                                        ls.not(),
                                        ns.not(),
                                        ij.not(),
                                        self.same_at(i, s, d).not(),
                                    ]);
                                }
                            }
                        }
                    }
                }
            }
            if let Some(pos) = &self.pos {
                let at = |i: usize, d: usize, p: usize| pos[i][d][p];
                for i in 0..k {
                    for d in 1..=depth {
                        for p in 2..k {
                            t.clause(&[at(i, d, p).not(), at(i, d, p - 1)]);
                        }
                        // Outside its block at depth `d`, a position is 0.
                        if k > 1 {
                            t.clause(&[self.dep[i][d], at(i, d, 1).not()]);
                        }
                    }
                }
                for d in 1..=depth {
                    for i in 0..k {
                        for s in (i + 1)..k {
                            let here = self.same_at(i, s, d);
                            let below = if d < depth {
                                self.same_at(i, s, d + 1)
                            } else {
                                Lit::False
                            };
                            // One sub-block, one position.
                            for p in 1..k {
                                t.clause(&[below.not(), at(i, d, p).not(), at(s, d, p)]);
                                t.clause(&[below.not(), at(i, d, p), at(s, d, p).not()]);
                            }
                            // Distinct operands of one block, distinct positions.
                            for p in 0..k {
                                t.clause(&[
                                    here.not(),
                                    below,
                                    at(i, d, p).not(),
                                    at(i, d, p + 1),
                                    at(s, d, p).not(),
                                    at(s, d, p + 1),
                                ]);
                            }
                        }
                        // Positions are contiguous from 0.
                        for p in 1..k {
                            let mut cl = vec![at(i, d, p).not()];
                            for s in 0..k {
                                if s == i {
                                    continue;
                                }
                                let y = t.fresh();
                                t.clause(&[y.not(), self.same_at(i, s, d)]);
                                t.clause(&[y.not(), at(s, d, p - 1)]);
                                t.clause(&[y.not(), at(s, d, p).not()]);
                                cl.push(y);
                            }
                            t.clause(&cl);
                        }
                    }
                }
            }
        }
        // Internal nodes, named by their smallest member.
        for d in 2..=depth {
            for r in 0..k {
                let rep = b.target().fresh();
                let mut cl = vec![self.dep[r][d].not(), rep];
                for e in 0..r {
                    cl.push(self.same_at(e, r, d));
                }
                b.target().clause(&cl);
                let exists = b.and(sel, rep);
                self.reps.push((r, d, rep));
                let mut members = vec![(Vec::new(), self.kids[r])];
                let mut siblings = Vec::new();
                for s in 0..k {
                    if s == r {
                        continue;
                    }
                    let g1 = self.same_at(r, s, d);
                    members.push((
                        if matches!(g1, Lit::True) {
                            vec![]
                        } else {
                            vec![g1]
                        },
                        self.kids[s],
                    ));
                    let mut g = vec![self.same_at(r, s, d - 1), self.same_at(r, s, d).not()];
                    g.retain(|l| !matches!(l, Lit::True));
                    siblings.push((g, self.kids[s]));
                }
                self.inner.push(Inner {
                    exists,
                    members,
                    siblings,
                });
            }
        }
    }

    fn sibling_parts(&self, sel: Lit, c: ClassId) -> Vec<(Vec<Lit>, ClassId)> {
        let Some(i) = self.kids.iter().position(|&x| x == c) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for d in 1..=self.depth {
            let [a, bb] = self.leaf_at(i, d);
            for s in 0..self.kids.len() {
                if s != i {
                    let mut g = vec![sel, a, bb, self.same_at(i, s, d)];
                    g.retain(|l| !matches!(l, Lit::True));
                    out.push((g, self.kids[s]));
                }
            }
        }
        out
    }

    fn decode(&self, model: &dyn Fn(u32) -> bool) -> Tree {
        let val = |l: Lit| match l {
            Lit::True => true,
            Lit::False => false,
            Lit::Var { var, sign } => model(var) == sign,
        };
        let depth_of = |i: usize| {
            (1..=self.depth)
                .rev()
                .find(|&d| val(self.dep[i][d]))
                .unwrap_or(1)
        };
        let label_of = |i: usize, d: usize| {
            (0..self.labels)
                .rev()
                .find(|&l| val(self.lab[i][d][l]))
                .unwrap_or(0)
        };
        let pos_of = |i: usize, d: usize| match &self.pos {
            Some(p) => (0..self.kids.len())
                .rev()
                .find(|&q| val(p[i][d][q]))
                .unwrap_or(0),
            None => i,
        };
        fn build(
            members: &[usize],
            d: usize,
            depth_of: &dyn Fn(usize) -> usize,
            label_of: &dyn Fn(usize, usize) -> usize,
            pos_of: &dyn Fn(usize, usize) -> usize,
        ) -> Tree {
            let mut ops: Vec<(usize, Tree)> = Vec::new();
            let mut groups: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
            for &i in members {
                if depth_of(i) == d {
                    ops.push((pos_of(i, d), Tree::Leaf(i)));
                } else {
                    groups.entry(label_of(i, d)).or_default().push(i);
                }
            }
            for g in groups.values() {
                let t = if g.len() == 1 {
                    Tree::Leaf(g[0])
                } else {
                    build(g, d + 1, depth_of, label_of, pos_of)
                };
                ops.push((pos_of(g[0], d), t));
            }
            ops.sort_by_key(|(p, _)| *p);
            Tree::Node(ops.into_iter().map(|(_, t)| t).collect())
        }
        let all: Vec<usize> = (0..self.kids.len()).collect();
        build(&all, 1, &depth_of, &label_of, &pos_of)
    }

    /// Rung literals under a tree: depths, labels, same-block, positions, and the
    /// internal-node names, exactly as the tree determines them.
    fn canonical(&self, tree: &Tree, out: &mut BTreeMap<u32, bool>) {
        let k = self.kids.len();
        let mut d_of = vec![1usize; k];
        let mut lab_of = vec![vec![0usize; self.depth + 1]; k];
        let mut pos_of = vec![vec![0usize; self.depth + 1]; k];
        let mut reps: Vec<(usize, usize)> = Vec::new();
        fn leaves(t: &Tree, out: &mut Vec<usize>) {
            match t {
                Tree::Leaf(i) => out.push(*i),
                Tree::Node(o) => o.iter().for_each(|x| leaves(x, out)),
            }
        }
        fn walk(
            t: &Tree,
            d: usize,
            d_of: &mut [usize],
            lab_of: &mut [Vec<usize>],
            pos_of: &mut [Vec<usize>],
            reps: &mut Vec<(usize, usize)>,
        ) {
            let Tree::Node(ops) = t else { return };
            if d >= 2 {
                let mut m = Vec::new();
                leaves(t, &mut m);
                reps.push((*m.iter().min().unwrap(), d));
            }
            // Sub-blocks are labelled in order of their smallest member.
            let mut subs: Vec<(usize, usize)> = ops
                .iter()
                .enumerate()
                .filter(|(_, o)| matches!(o, Tree::Node(_)))
                .map(|(j, o)| {
                    let mut m = Vec::new();
                    leaves(o, &mut m);
                    (*m.iter().min().unwrap(), j)
                })
                .collect();
            subs.sort();
            for (p, o) in ops.iter().enumerate() {
                match o {
                    Tree::Leaf(i) => {
                        d_of[*i] = d;
                        pos_of[*i][d] = p;
                    }
                    Tree::Node(_) => {
                        let label = subs.iter().position(|&(_, j)| j == p).unwrap();
                        let mut m = Vec::new();
                        leaves(o, &mut m);
                        for &i in &m {
                            lab_of[i][d] = label;
                            pos_of[i][d] = p;
                        }
                        walk(o, d + 1, d_of, lab_of, pos_of, reps);
                    }
                }
            }
        }
        walk(tree, 1, &mut d_of, &mut lab_of, &mut pos_of, &mut reps);
        let mut set = |l: Lit, v: bool| {
            if let Some(var) = var_of(l)
                && let Lit::Var { sign, .. } = l
            {
                out.insert(var, v == sign);
            }
        };
        for i in 0..k {
            for d in 2..=self.depth {
                set(self.dep[i][d], d_of[i] >= d);
            }
            for d in 1..self.depth {
                for l in 1..self.labels {
                    set(self.lab[i][d][l], d_of[i] > d && lab_of[i][d] >= l);
                }
            }
            if let Some(pos) = &self.pos {
                for d in 1..=self.depth {
                    for p in 1..k {
                        set(pos[i][d][p], d_of[i] >= d && pos_of[i][d] >= p);
                    }
                }
            }
        }
        for i in 0..k {
            for s in (i + 1)..k {
                for d in 2..=self.depth {
                    let same = d_of[i] >= d
                        && d_of[s] >= d
                        && (1..d).all(|e| lab_of[i][e] == lab_of[s][e]);
                    set(self.same_at(i, s, d), same);
                }
            }
        }
        for &(r, d, lit) in &self.reps {
            set(lit, reps.contains(&(r, d)));
        }
    }

    fn primary(&self, model: &dyn Fn(u32) -> bool) -> Vec<Lit> {
        let mut out = Vec::new();
        let mut push = |l: Lit| {
            if let Some(var) = var_of(l) {
                out.push(if model(var) {
                    Lit::pos(var)
                } else {
                    Lit::neg(var)
                });
            }
        };
        for i in 0..self.kids.len() {
            for d in 2..=self.depth {
                push(self.dep[i][d]);
            }
            for d in 1..self.depth {
                for l in 1..self.labels {
                    push(self.lab[i][d][l]);
                }
            }
            if let Some(pos) = &self.pos {
                for d in 1..=self.depth {
                    for p in 1..self.kids.len() {
                        push(pos[i][d][p]);
                    }
                }
            }
        }
        out
    }
}

// --- the tree rungs --------------------------------------------------------------

/// Tree variables for every candidate flat node and associative sequence, over one
/// selection.
struct Trees {
    selection: Selection,
    trees: Vec<Option<TreeVars>>,
    seqs: Vec<Option<crate::extraction::seq::SeqVars>>,
}

impl Trees {
    fn build(selection: Selection, b: &mut Build, family: Family) -> Trees {
        let g = selection.graph.clone();
        let cap = if family == Family::Ordered {
            MAX_ORDERED_ARITY
        } else {
            MAX_ARITY
        };
        let mut trees: Vec<Option<TreeVars>> = (0..g.nodes.len()).map(|_| None).collect();
        let mut seqs: Vec<Option<crate::extraction::seq::SeqVars>> =
            (0..g.nodes.len()).map(|_| None).collect();
        // A sequence's order is fixed, so the orders rung brackets it as splits does.
        let seq_family = match family {
            Family::Chains => crate::extraction::seq::SeqFamily::Chains,
            Family::Splits { binary: true } => crate::extraction::seq::SeqFamily::Binary,
            _ => crate::extraction::seq::SeqFamily::Trees,
        };
        for &c in &selection.reachable {
            for n in g.candidates(c) {
                if g.nodes[n].flat() {
                    let kids = g.operands(n);
                    if kids.len() >= 3 && kids.len() <= cap {
                        trees[n] = Some(TreeVars::new(b, selection.node(n), n, kids, family));
                    }
                } else if g.nodes[n].kind
                    == crate::extraction::graph::Kind::Seq(crate::extraction::graph::Assoc::Both)
                {
                    let kids = g.nodes[n].children.clone();
                    if kids.len() >= 3 && kids.len() <= MAX_ARITY {
                        seqs[n] = Some(crate::extraction::seq::SeqVars::free(
                            b,
                            selection.node(n),
                            kids,
                            seq_family,
                        ));
                    }
                }
            }
        }
        Trees {
            selection,
            trees,
            seqs,
        }
    }

    fn siblings(&self, n: NodeId, c: ClassId) -> Vec<(Vec<Lit>, ClassId)> {
        match (&self.trees[n], &self.seqs[n]) {
            (Some(t), _) => t.sibling_parts(self.selection.node(n), c),
            (_, Some(q)) => q.sibling_parts(self.selection.node(n), c),
            _ => self.selection.node_siblings(n, c),
        }
    }

    fn inner_nodes(&self, n: NodeId) -> &[Inner] {
        match (&self.trees[n], &self.seqs[n]) {
            (Some(t), _) => t.inner.as_slice(),
            (_, Some(q)) => q.inner.as_slice(),
            _ => self.selection.fold_inner(n),
        }
    }

    fn decode(&self, model: &dyn Fn(u32) -> bool) -> Term {
        let selection = self.selection.decode_selection(model);
        let mut trees = BTreeMap::new();
        for n in selection.iter().flatten() {
            if let Some(t) = &self.trees[*n] {
                trees.insert(*n, t.decode(model));
            }
            if let Some(q) = &self.seqs[*n] {
                trees.insert(*n, q.decode(model));
            }
        }
        Term { selection, trees }
    }

    fn canonical(&self, term: &Term) -> BTreeMap<u32, bool> {
        let mut out = BTreeMap::new();
        self.selection.canonical_selection(term, &mut out);
        for (n, t) in self.trees.iter().enumerate() {
            let Some(t) = t else { continue };
            let selected = term.selection[self.selection.graph.nodes[n].class] == Some(n);
            let flat = Tree::Node((0..t.kids.len()).map(Tree::Leaf).collect());
            let tree = if selected {
                term.trees.get(&n).unwrap_or(&flat)
            } else {
                &flat
            };
            t.canonical(tree, &mut out);
        }
        for (n, q) in self.seqs.iter().enumerate() {
            let Some(q) = q else { continue };
            let selected = term.selection[self.selection.graph.nodes[n].class] == Some(n);
            let flat = Tree::Node(
                (0..self.selection.graph.nodes[n].children.len())
                    .map(Tree::Leaf)
                    .collect(),
            );
            let tree = if selected {
                term.trees.get(&n).unwrap_or(&flat)
            } else {
                &flat
            };
            q.canonical(tree, &mut out);
        }
        out
    }

    fn term_literals(&self, model: &dyn Fn(u32) -> bool, term: &Term) -> Vec<Lit> {
        let mut out = self.selection.selection_literals(term);
        for n in term.selection.iter().flatten() {
            if let Some(t) = &self.trees[*n] {
                out.extend(t.primary(model));
            }
            if let Some(q) = &self.seqs[*n] {
                out.extend(q.primary(model));
            }
        }
        out
    }

    fn depth(&self, b: &mut Build, n: NodeId, c: ClassId) -> Option<OInt<Exact>> {
        if let Some(q) = &self.seqs[n] {
            return q.depth(b, c);
        }
        let t = self.trees[n].as_ref()?;
        let i = t.kids.iter().position(|&x| x == c)?;
        let values: Vec<i64> = (1..=t.depth as i64).collect();
        let ge: Vec<Lit> = (1..=t.depth).map(|d| t.dep[i][d]).collect();
        Some(b.from_thresholds(values, ge))
    }

    fn position(&self, b: &mut Build, n: NodeId, c: ClassId, d: usize) -> Option<OInt<Exact>> {
        let t = self.trees[n].as_ref()?;
        let pos = t.pos.as_ref()?;
        if d == 0 || d > t.depth {
            return None;
        }
        let i = t.kids.iter().position(|&x| x == c)?;
        let k = t.kids.len();
        Some(b.from_thresholds((0..k as i64).collect(), pos[i][d][..k].to_vec()))
    }
}

macro_rules! tree_rung {
    ($name:ident, $label:expr, $doc:expr) => {
        #[doc = $doc]
        pub struct $name {
            inner: Trees,
        }

        impl std::ops::Deref for $name {
            type Target = Selection;
            fn deref(&self) -> &Selection {
                &self.inner.selection
            }
        }

        impl Rung for $name {
            fn selection(&self) -> &Selection {
                &self.inner.selection
            }
            fn siblings(&self, n: NodeId, c: ClassId) -> Vec<(Vec<Lit>, ClassId)> {
                self.inner.siblings(n, c)
            }
            fn inner_nodes(&self, n: NodeId) -> &[Inner] {
                self.inner.inner_nodes(n)
            }
            fn decode(&self, model: &dyn Fn(u32) -> bool) -> Term {
                self.inner.decode(model)
            }
            fn canonical(&self, term: &Term) -> BTreeMap<u32, bool> {
                self.inner.canonical(term)
            }
            fn term_literals(&self, model: &dyn Fn(u32) -> bool, term: &Term) -> Vec<Lit> {
                self.inner.term_literals(model, term)
            }
            fn name(&self) -> &'static str {
                $label
            }
            fn nesting(&self) -> Option<&dyn Nesting> {
                Some(self)
            }
            fn ordering(&self) -> Option<&dyn Ordering> {
                AsOrdering::as_ordering(self)
            }
        }

        impl Nesting for $name {
            fn depth(&self, b: &mut Build, n: NodeId, c: ClassId) -> Option<OInt<Exact>> {
                self.inner.depth(b, n, c)
            }
        }
    };
}

tree_rung!(
    Levels,
    "levels",
    "Rung 1: plus a depth per operand; chains of flat blocks."
);
tree_rung!(
    Splits,
    "splits",
    "Rung 2: plus split labels; every unordered tree, or every binary one."
);
tree_rung!(
    Orders,
    "orders",
    "Rung 3: plus operand positions; every ordered tree."
);

impl Levels {
    pub fn build(selection: Selection, b: &mut Build) -> Levels {
        Levels {
            inner: Trees::build(selection, b, Family::Chains),
        }
    }
}

impl Splits {
    /// Every unordered tree when `binary` is false; every binary one when true.
    pub fn build(selection: Selection, b: &mut Build, binary: bool) -> Splits {
        Splits {
            inner: Trees::build(selection, b, Family::Splits { binary }),
        }
    }
}

impl Orders {
    pub fn build(selection: Selection, b: &mut Build) -> Orders {
        Orders {
            inner: Trees::build(selection, b, Family::Ordered),
        }
    }
}

/// Which tree rungs expose positions.
trait AsOrdering {
    fn as_ordering(&self) -> Option<&dyn Ordering>;
}
impl AsOrdering for Levels {
    fn as_ordering(&self) -> Option<&dyn Ordering> {
        None
    }
}
impl AsOrdering for Splits {
    fn as_ordering(&self) -> Option<&dyn Ordering> {
        None
    }
}
impl AsOrdering for Orders {
    fn as_ordering(&self) -> Option<&dyn Ordering> {
        Some(self)
    }
}

impl Ordering for Orders {
    fn position(&self, b: &mut Build, n: NodeId, c: ClassId, d: usize) -> Option<OInt<Exact>> {
        self.inner.position(b, n, c, d)
    }
}

// --- recursive attributes --------------------------------------------------------

/// The id of a node given by reference into `g.nodes`.
fn node_id(g: &Graph, n: &Node) -> NodeId {
    let i = (n as *const Node as usize - g.nodes.as_ptr() as usize) / std::mem::size_of::<Node>();
    debug_assert!(std::ptr::eq(&g.nodes[i], n), "a node of this graph");
    i
}

/// Per-class values the fixpoint may produce, exactly (a sum of offsets past u64 is
/// held, and the build's width then decides whether it is an error). `Err` names the
/// first class whose set would exceed `cap`, when one is set: no value is dropped.
///
/// A node's values are its offset plus the values its operands' maximum (minimum)
/// can take: those of the operands' values at least the largest operand minimum (at
/// most the smallest operand maximum). Taking every operand value instead is sound
/// but not tight: on a tree whose classes have one node each, the domains grow to
/// the number of distinct path lengths below each class (237 values where the
/// attribute has one, on Herbie's `colonnade`), and the objective with them. An
/// operand with no values yet, or only through a cycle, is left out of the bound.
fn domains(
    g: &Graph,
    reachable: &[ClassId],
    max: bool,
    offset: &dyn Fn(&Node) -> Cost,
    cap: Option<usize>,
) -> Result<Vec<Vec<Cost>>, String> {
    use std::ops::Bound::{Included, Unbounded};
    let mut sets: Vec<std::collections::BTreeSet<Cost>> = vec![Default::default(); g.classes.len()];
    for _ in 0..(g.classes.len() + 2) {
        let mut changed = false;
        for &c in reachable {
            for n in g.candidates(c) {
                let off = offset(&g.nodes[n]);
                let kids = g.operands(n);
                let incoming: Vec<Cost> = if kids.is_empty() {
                    vec![off]
                } else {
                    let known = kids.iter().filter(|&&k| !sets[k].is_empty());
                    // No bound on the side the recursion does not cut.
                    let (lo, hi) = if max {
                        (
                            Included(
                                known
                                    .map(|&k| *sets[k].first().unwrap())
                                    .max()
                                    .unwrap_or(Cost::ZERO),
                            ),
                            Unbounded,
                        )
                    } else {
                        (
                            Included(Cost::ZERO),
                            known
                                .map(|&k| *sets[k].last().unwrap())
                                .min()
                                .map_or(Unbounded, Included),
                        )
                    };
                    kids.iter()
                        .flat_map(|&k| sets[k].range((lo, hi)).map(move |&v| v + off))
                        .collect()
                };
                for v in incoming {
                    if cap.is_some_and(|cap| sets[c].len() >= cap) && !sets[c].contains(&v) {
                        return Err(format!(
                            "attribute: class {c} has more than {} values, the cap set on the build",
                            cap.unwrap_or(0)
                        ));
                    }
                    changed |= sets[c].insert(v);
                }
            }
        }
        if !changed {
            break;
        }
    }
    Ok(sets.into_iter().map(|s| s.into_iter().collect()).collect())
}

impl<'t> Build<'t> {
    /// A per-class attribute: the maximum over the selected node's operands plus the
    /// node's offset, a leaf taking its offset. Over-estimated, forced upward.
    pub fn rec_max<R: Rung + ?Sized, O: Into<Cost>>(
        &mut self,
        rung: &R,
        offset: &dyn Fn(&Node) -> O,
    ) -> Vec<Option<OInt<Over>>> {
        self.rec(rung, &|n: &Node| offset(n).into(), true, true)
    }

    /// The max-recursive attribute of [`Self::rec_max`], forced downward: an
    /// under-estimate, for where the attribute is subtracted.
    pub fn rec_max_down<R: Rung + ?Sized, O: Into<Cost>>(
        &mut self,
        rung: &R,
        offset: &dyn Fn(&Node) -> O,
    ) -> Vec<Option<OInt<Under>>> {
        self.rec(rung, &|n: &Node| offset(n).into(), true, false)
    }

    /// The min-recursive attribute of [`Self::rec_min`], forced upward: an
    /// over-estimate.
    pub fn rec_min_up<R: Rung + ?Sized, O: Into<Cost>>(
        &mut self,
        rung: &R,
        offset: &dyn Fn(&Node) -> O,
    ) -> Vec<Option<OInt<Over>>> {
        self.rec(rung, &|n: &Node| offset(n).into(), false, true)
    }

    /// As [`Self::rec_max`], with the offset given by node id.
    pub fn rec_max_by_id<R: Rung + ?Sized, O: Into<Cost>>(
        &mut self,
        rung: &R,
        offset: &dyn Fn(NodeId) -> O,
    ) -> Vec<Option<OInt<Over>>> {
        let g = rung.selection().graph.clone();
        let by_node = |n: &Node| offset(node_id(&g, n)).into();
        self.rec(rung, &by_node, true, true)
    }

    /// As [`Self::rec_max_down`], with the offset given by node id.
    pub fn rec_max_down_by_id<R: Rung + ?Sized, O: Into<Cost>>(
        &mut self,
        rung: &R,
        offset: &dyn Fn(NodeId) -> O,
    ) -> Vec<Option<OInt<Under>>> {
        let g = rung.selection().graph.clone();
        let by_node = |n: &Node| offset(node_id(&g, n)).into();
        self.rec(rung, &by_node, true, false)
    }

    /// As [`Self::rec_min_up`], with the offset given by node id.
    pub fn rec_min_up_by_id<R: Rung + ?Sized, O: Into<Cost>>(
        &mut self,
        rung: &R,
        offset: &dyn Fn(NodeId) -> O,
    ) -> Vec<Option<OInt<Over>>> {
        let g = rung.selection().graph.clone();
        let by_node = |n: &Node| offset(node_id(&g, n)).into();
        self.rec(rung, &by_node, false, true)
    }

    /// As [`Self::rec_min`], with the offset given by node id.
    pub fn rec_min_by_id<R: Rung + ?Sized, O: Into<Cost>>(
        &mut self,
        rung: &R,
        offset: &dyn Fn(NodeId) -> O,
    ) -> Vec<Option<OInt<Under>>> {
        let g = rung.selection().graph.clone();
        let by_node = |n: &Node| offset(node_id(&g, n)).into();
        self.rec(rung, &by_node, false, false)
    }

    /// As [`Self::rec_max`] with the minimum. Under-estimated, forced downward.
    pub fn rec_min<R: Rung + ?Sized, O: Into<Cost>>(
        &mut self,
        rung: &R,
        offset: &dyn Fn(&Node) -> O,
    ) -> Vec<Option<OInt<Under>>> {
        self.rec(rung, &|n: &Node| offset(n).into(), false, false)
    }

    /// `max` chooses the recursion, `up` the direction it is forced in: a max
    /// forced up and a min forced down are the natural over- and under-estimates;
    /// the other two are their duals.
    fn rec<P: crate::extraction::oint::Polarity, R: Rung + ?Sized>(
        &mut self,
        rung: &R,
        offset: &dyn Fn(&Node) -> Cost,
        max: bool,
        up: bool,
    ) -> Vec<Option<OInt<P>>> {
        let sel = rung.selection();
        let g = sel.graph.clone();
        let doms = match domains(&g, &sel.reachable, max, offset, self.attribute_cap) {
            Ok(d) => d,
            Err(e) => {
                self.fail(e);
                // The build has failed; an attribute of one value per class keeps the
                // rest of it well-formed.
                vec![vec![Cost::ZERO]; g.classes.len()]
            }
        };
        let mut def = RecDef {
            max,
            offset: g.nodes.iter().map(offset).collect(),
            slot: vec![None; g.classes.len()],
        };
        let mut out: Vec<Option<OInt<P>>> = (0..g.classes.len()).map(|_| None).collect();
        for &c in &sel.reachable {
            let values: Vec<Cost> = doms[c].clone();
            let mut ge = vec![Lit::True];
            for _ in 1..values.len() {
                ge.push(self.target.fresh());
            }
            for j in 2..ge.len() {
                self.target.clause(&[ge[j].not(), ge[j - 1]]);
            }
            let slot = self.rec.slots;
            self.rec.slots += 1;
            def.slot[c] = Some(slot);
            out[c] = Some(self.external(values, ge, slot));
        }
        // A value below the domain is the constant true threshold, which the least value
        // implies. A value above it arises only through a cycle, when the fixpoint's
        // rounds end before the values do: forced to the top threshold. Every acyclic
        // term's values are in the domains, so the clause on its own values is exact,
        // and a weaker one on larger values does not let a model understate it.
        let at = |x: &OInt<P>, v: Cost| -> Lit {
            let j = x.values().partition_point(|&y| y < v);
            if j < x.values().len() {
                x.at_least(v)
            } else {
                x.at_least(*x.values().last().unwrap())
            }
        };
        for &c in &sel.reachable {
            let me = out[c].clone().unwrap();
            for n in g.candidates(c) {
                let an = sel.node(n);
                let off = offset(&g.nodes[n]);
                let kids = g.operands(n);
                if max && !up {
                    // At least `pv` only through a child at least `pv - off`.
                    for (pv, pl) in me.thresholds() {
                        if pv <= off {
                            continue;
                        }
                        let mut cl = vec![an.not(), pl.not()];
                        cl.extend(
                            kids.iter()
                                .map(|&k| out[k].clone().unwrap().at_least(pv - off)),
                        );
                        self.target.clause(&cl);
                    }
                } else if !max && up {
                    // Every child at least `v - off` forces at least `v`.
                    for &v in me.values().iter().skip(1) {
                        let mut cl = vec![an.not(), at(&me, v)];
                        if v > off {
                            if kids.is_empty() {
                                continue;
                            }
                            cl.extend(
                                kids.iter()
                                    .map(|&k| out[k].clone().unwrap().at_least(v - off).not()),
                            );
                        }
                        self.target.clause(&cl);
                    }
                } else if max {
                    if kids.is_empty() {
                        self.target.clause(&[an.not(), at(&me, off)]);
                    }
                    for &k in &kids {
                        let child = out[k].clone().unwrap();
                        for (v, l) in child.thresholds() {
                            self.target.clause(&[an.not(), l.not(), at(&me, v + off)]);
                        }
                    }
                } else {
                    for (pv, pl) in me.thresholds() {
                        if pv <= off {
                            continue;
                        }
                        if kids.is_empty() {
                            self.target.clause(&[an.not(), pl.not()]);
                        }
                        for &k in &kids {
                            let child = out[k].clone().unwrap();
                            self.target
                                .clause(&[an.not(), pl.not(), child.at_least(pv - off)]);
                        }
                    }
                }
            }
        }
        self.rec.recs.push(def);
        out
    }
}

impl crate::extraction::oint::Detached {
    /// Values of every recursive attribute on a term, by slot.
    pub(crate) fn rec_values(&self, g: &Graph, term: &Term) -> Vec<Cost> {
        let mut values = vec![Cost::ZERO; self.slots];
        let order = match term.order(g) {
            Ok(o) => o,
            Err(_) => return values,
        };
        for def in &self.recs {
            let mut v = vec![Cost::ZERO; g.classes.len()];
            for &c in &order {
                let n = term.selection[c].expect("ordered class is selected");
                let kids = g.operands(n);
                let base = if kids.is_empty() {
                    Cost::ZERO
                } else if def.max {
                    kids.iter().map(|&k| v[k]).max().unwrap()
                } else {
                    kids.iter().map(|&k| v[k]).min().unwrap()
                };
                v[c] = base + def.offset[n];
                if let Some(s) = def.slot[c] {
                    values[s] = v[c];
                }
            }
        }
        values
    }
}

// --- choosing a rung at run time -------------------------------------------------

/// A rung, chosen at run time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RungKind {
    Selection,
    Levels,
    Splits,
    Binary,
    Orders,
}

impl RungKind {
    pub fn parse(s: &str) -> Option<RungKind> {
        Some(match s {
            "selection" => RungKind::Selection,
            "levels" => RungKind::Levels,
            "splits" => RungKind::Splits,
            "binary" => RungKind::Binary,
            "orders" => RungKind::Orders,
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            RungKind::Selection => "selection",
            RungKind::Levels => "levels",
            RungKind::Splits => "splits",
            RungKind::Binary => "binary",
            RungKind::Orders => "orders",
        }
    }

    /// Clauses the tree variables and a cost charging every internal node would
    /// need on `g`, estimated before anything is allocated. Tree variables are
    /// built for every candidate flat node, so a saturated e-graph can need far
    /// more than the selection itself: the estimate is what keeps a large instance
    /// from exhausting memory. The charges assume value sets of 64, which is a
    /// proxy and not a bound.
    pub fn estimate(self, g: &Graph) -> u64 {
        if self == RungKind::Selection {
            return 0;
        }
        let mut total: u64 = 0;
        for c in g.reachable() {
            for n in g.candidates(c) {
                if g.nodes[n].kind
                    == crate::extraction::graph::Kind::Seq(crate::extraction::graph::Assoc::Both)
                {
                    // A sequence's intervals: one literal each, a clause per crossing
                    // pair, and a cost's charges per interval.
                    let k = g.nodes[n].children.len() as u64;
                    if (3..=MAX_ARITY as u64).contains(&k) {
                        let iv = k * (k - 1) / 2;
                        total = total.saturating_add(iv * iv / 2 + iv * (k * 128 + 64 * 64));
                    }
                    continue;
                }
                if !g.nodes[n].flat() {
                    continue;
                }
                let k = g.operands(n).len() as u64;
                let cap = if self == RungKind::Orders {
                    MAX_ORDERED_ARITY
                } else {
                    MAX_ARITY
                } as u64;
                if k < 3 || k > cap {
                    continue;
                }
                let depth = k - 1;
                let labels = match self {
                    RungKind::Levels => 1,
                    RungKind::Binary => 2,
                    _ => (k / 2).max(1),
                };
                let mut structure = 8 * k * k * depth * labels;
                if self == RungKind::Binary {
                    structure += k * k * k * depth;
                }
                if self == RungKind::Orders {
                    structure += 4 * k * k * k * depth;
                }
                let charges = k * depth * (k * 128 + 64 * 64);
                total = total.saturating_add(structure + charges);
            }
        }
        total
    }

    /// The highest rung at or below this one whose estimate on `g` fits `budget`:
    /// orders, splits, levels, selection; binary steps to selection.
    pub fn within(self, g: &Graph, budget: u64) -> RungKind {
        let ladder: &[RungKind] = match self {
            RungKind::Orders => &[
                RungKind::Orders,
                RungKind::Splits,
                RungKind::Levels,
                RungKind::Selection,
            ],
            RungKind::Splits => &[RungKind::Splits, RungKind::Levels, RungKind::Selection],
            RungKind::Binary => &[RungKind::Binary, RungKind::Selection],
            RungKind::Levels => &[RungKind::Levels, RungKind::Selection],
            RungKind::Selection => &[RungKind::Selection],
        };
        ladder
            .iter()
            .copied()
            .find(|&r| r == RungKind::Selection || r.estimate(g) <= budget)
            .unwrap_or(RungKind::Selection)
    }
}
