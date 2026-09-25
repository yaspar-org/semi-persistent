// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Ramp-up kata 1: union-find + a bare e-graph that shows why rebuild exists.
//!
//! Self-contained on purpose — this file does not use the production
//! `UnionFind` or `EGraph`. The interaction to learn is:
//!
//! 1. hash-consing keys a node by `(op, find(child), find(child), …)`;
//! 2. `union` changes those `find` results;
//! 3. without `rebuild`, the table still holds the old keys, so two nodes
//!    that have become structurally identical stay in different classes.

use proptest::prelude::*;
use std::collections::{HashMap, HashSet};

type Id = usize;

// ---------------------------------------------------------------------------
// Part 1 — Union-find with path compression and union by rank
// ---------------------------------------------------------------------------

/// A forest of trees. Each tree is one equivalence class; the root is the
/// representative that `find` returns.
struct UnionFind {
    /// `parent[x]` is the next node toward the root. A root stores `parent[x] = x`.
    parent: Vec<Id>,
    /// `rank[x]` is used only at roots: an upper bound on that tree's height.
    rank: Vec<u8>,
}

impl UnionFind {
    fn new() -> Self {
        Self {
            parent: Vec::new(),
            rank: Vec::new(),
        }
    }

    /// Allocate a fresh singleton class `{id}` and return `id`.
    fn make(&mut self) -> Id {
        let id = self.parent.len();
        self.parent.push(id);
        self.rank.push(0);
        id
    }

    /// Walk to the root, then flatten the path so every hop points at the root.
    fn find(&mut self, x: Id) -> Id {
        let p = self.parent[x];
        if p != x {
            let root = self.find(p);
            self.parent[x] = root;
            root
        } else {
            x
        }
    }

    /// Merge the classes of `a` and `b`. The shorter tree hangs under the taller
    /// one. Returns `Some((survivor, absorbed))`, or `None` if already together.
    fn union(&mut self, a: Id, b: Id) -> Option<(Id, Id)> {
        let mut ra = self.find(a);
        let mut rb = self.find(b);
        if ra == rb {
            return None;
        }
        if self.rank[ra] < self.rank[rb] {
            std::mem::swap(&mut ra, &mut rb);
        }
        self.parent[rb] = ra;
        if self.rank[ra] == self.rank[rb] {
            self.rank[ra] += 1;
        }
        Some((ra, rb))
    }
}

// ---------------------------------------------------------------------------
// Part 2 — Naive set-of-sets oracle (obviously correct, not fast)
// ---------------------------------------------------------------------------

/// Each element remembers which set it belongs to. `union` really does merge
/// two `HashSet`s. This is the spec the union-find must match.
struct NaiveSets {
    set_of: Vec<Id>,
    members: Vec<HashSet<Id>>,
}

impl NaiveSets {
    fn with_size(n: usize) -> Self {
        Self {
            set_of: (0..n).collect(),
            members: (0..n).map(|i| HashSet::from([i])).collect(),
        }
    }

    fn same(&self, a: Id, b: Id) -> bool {
        self.set_of[a] == self.set_of[b]
    }

    fn union(&mut self, a: Id, b: Id) {
        let (sa, sb) = (self.set_of[a], self.set_of[b]);
        if sa == sb {
            return;
        }
        let (keep, drop) = if self.members[sa].len() >= self.members[sb].len() {
            (sa, sb)
        } else {
            (sb, sa)
        };
        let moving: Vec<Id> = self.members[drop].drain().collect();
        for x in moving {
            self.set_of[x] = keep;
            self.members[keep].insert(x);
        }
    }
}

#[derive(Clone, Debug)]
enum UfOp {
    Union(Id, Id),
    Same(Id, Id),
}

fn uf_ops() -> impl Strategy<Value = (usize, Vec<UfOp>)> {
    (1usize..20).prop_flat_map(|n| {
        let op = prop_oneof![
            (0..n, 0..n).prop_map(|(a, b)| UfOp::Union(a, b)),
            (0..n, 0..n).prop_map(|(a, b)| UfOp::Same(a, b)),
        ];
        proptest::collection::vec(op, 0..64).prop_map(move |ops| (n, ops))
    })
}

fn run_uf_against_naive(n: usize, ops: &[UfOp]) {
    let mut uf = UnionFind::new();
    for _ in 0..n {
        uf.make();
    }
    let mut naive = NaiveSets::with_size(n);
    for op in ops {
        match *op {
            UfOp::Union(a, b) => {
                uf.union(a, b);
                naive.union(a, b);
            }
            UfOp::Same(a, b) => {
                assert_eq!(
                    uf.find(a) == uf.find(b),
                    naive.same(a, b),
                    "find disagrees with the set-of-sets model on ({a}, {b})"
                );
            }
        }
    }
    for a in 0..n {
        for b in 0..n {
            assert_eq!(
                uf.find(a) == uf.find(b),
                naive.same(a, b),
                "final partition disagrees on ({a}, {b})"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Part 3 — Bare e-graph: add / find / union / rebuild, with hash-consing
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Op {
    /// Nullary constant. `Const(0)` is `a`, `Const(1)` is `b`, and so on.
    Const(u8),
    /// Binary `f`.
    F,
}

struct Node {
    op: Op,
    /// Child *class* ids, last written at insert or recanonize time.
    children: Vec<Id>,
}

struct EGraph {
    uf: UnionFind,
    nodes: Vec<Node>,
    /// `(op, canonical children)` → the node that currently owns that key.
    hashcons: HashMap<(Op, Vec<Id>), Id>,
    /// `uses[class]` = parent nodes that have `class` as a child.
    uses: Vec<Vec<Id>>,
    /// Parents that may still store a pre-merge child id in their key.
    pending: Vec<Id>,
}

impl EGraph {
    fn new() -> Self {
        Self {
            uf: UnionFind::new(),
            nodes: Vec::new(),
            hashcons: HashMap::new(),
            uses: Vec::new(),
            pending: Vec::new(),
        }
    }

    fn node_count(&self) -> usize {
        self.nodes.len()
    }

    fn find(&mut self, x: Id) -> Id {
        self.uf.find(x)
    }

    /// Insert `op(children…)`. Reuses the existing node when the canonical
    /// key is already in the table — that is hash-consing.
    fn add(&mut self, op: Op, children: &[Id]) -> Id {
        let kids: Vec<Id> = children.iter().map(|&c| self.uf.find(c)).collect();
        let key = (op, kids.clone());
        if let Some(&existing) = self.hashcons.get(&key) {
            return existing;
        }
        let id = self.uf.make();
        debug_assert_eq!(id, self.nodes.len());
        self.nodes.push(Node {
            op,
            children: kids.clone(),
        });
        self.uses.push(Vec::new());
        self.hashcons.insert(key, id);
        for &c in &kids {
            self.uses[c].push(id);
        }
        id
    }

    /// Merge two classes. Only the union-find and the use-lists change here.
    /// Parent keys stay stale until `rebuild`.
    fn union(&mut self, a: Id, b: Id) -> Option<(Id, Id)> {
        let (survivor, absorbed) = self.uf.union(a, b)?;
        let parents = std::mem::take(&mut self.uses[absorbed]);
        self.pending.extend(parents.iter().copied());
        self.uses[survivor].extend(parents);
        Some((survivor, absorbed))
    }

    /// Rehash every stale parent. A collision is congruence: the two nodes
    /// denote the same application, so their classes merge.
    fn rebuild(&mut self) {
        while let Some(n) = self.pending.pop() {
            self.recanonize(n);
        }
    }

    fn recanonize(&mut self, n: Id) {
        let op = self.nodes[n].op;
        let old_children = self.nodes[n].children.clone();
        let new_children: Vec<Id> = old_children
            .iter()
            .copied()
            .map(|c| self.uf.find(c))
            .collect();
        if old_children == new_children {
            return;
        }
        let old_key = (op, old_children);
        if self.hashcons.get(&old_key) == Some(&n) {
            self.hashcons.remove(&old_key);
        }
        self.nodes[n].children = new_children.clone();
        let new_key = (op, new_children);
        if let Some(other) = self.hashcons.get(&new_key).copied() {
            if self.uf.find(other) != self.uf.find(n) {
                self.union(n, other);
            }
            let root = self.uf.find(n);
            self.hashcons.insert(new_key, root);
        } else {
            self.hashcons.insert(new_key, n);
        }
    }
}

/// After rebuild, equal child classes must put `f`-parents in one class.
fn assert_congruence_closed(g: &mut EGraph) {
    let f_nodes: Vec<Id> = (0..g.nodes.len())
        .filter(|&i| g.nodes[i].op == Op::F)
        .collect();
    for &i in &f_nodes {
        for &j in &f_nodes {
            let ci: Vec<Id> = g.nodes[i].children.iter().map(|&c| g.uf.find(c)).collect();
            let cj: Vec<Id> = g.nodes[j].children.iter().map(|&c| g.uf.find(c)).collect();
            if ci == cj {
                assert_eq!(
                    g.find(i),
                    g.find(j),
                    "congruence missed: f-nodes {i} and {j} have the same children {ci:?}"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tests — these stay in the suite (the kata is not throwaway)
// ---------------------------------------------------------------------------

#[test]
fn path_compression_flattens_to_the_root() {
    let mut uf = UnionFind::new();
    let a = uf.make();
    let b = uf.make();
    let c = uf.make();
    uf.union(a, b);
    uf.union(b, c);
    let root = uf.find(c);
    assert_eq!(uf.parent[c], root);
    assert_eq!(uf.parent[b], root);
    assert_eq!(uf.find(a), root);
}

#[test]
fn union_by_rank_hangs_the_shorter_tree() {
    let mut uf = UnionFind::new();
    let a = uf.make();
    let b = uf.make();
    let c = uf.make();
    uf.union(a, b);
    let (survivor, absorbed) = uf.union(a, c).expect("c was a singleton");
    assert_eq!(survivor, uf.find(a));
    assert_eq!(absorbed, c);
    assert_eq!(uf.parent[c], survivor);
}

#[test]
fn hashcons_reuses_the_same_node() {
    let mut g = EGraph::new();
    let a = g.add(Op::Const(0), &[]);
    let b = g.add(Op::Const(1), &[]);
    let first = g.add(Op::F, &[a, b]);
    let again = g.add(Op::F, &[a, b]);
    assert_eq!(first, again);
    assert_eq!(g.node_count(), 3);
    let a2 = g.add(Op::Const(0), &[]);
    assert_eq!(a, a2);
    assert_eq!(g.node_count(), 3);
}

#[test]
fn without_rebuild_congruence_is_lost() {
    let mut g = EGraph::new();
    let a = g.add(Op::Const(0), &[]);
    let b = g.add(Op::Const(1), &[]);
    let c = g.add(Op::Const(2), &[]);
    let d = g.add(Op::Const(3), &[]);
    let left = g.add(Op::F, &[a, b]);
    let right = g.add(Op::F, &[c, d]);
    assert_eq!(g.node_count(), 6);

    g.union(a, c);
    g.union(b, d);

    // The bug the kata asks us to demonstrate: mathematically
    // f(a,b) = f(c,d), but the table still has two keys.
    assert_ne!(
        g.find(left),
        g.find(right),
        "expected the stale-key bug before rebuild"
    );
}

#[test]
fn rebuild_restores_congruence() {
    let mut g = EGraph::new();
    let a = g.add(Op::Const(0), &[]);
    let b = g.add(Op::Const(1), &[]);
    let c = g.add(Op::Const(2), &[]);
    let d = g.add(Op::Const(3), &[]);
    let left = g.add(Op::F, &[a, b]);
    let right = g.add(Op::F, &[c, d]);

    g.union(a, c);
    g.union(b, d);
    g.rebuild();

    assert_eq!(g.find(left), g.find(right));
    assert_eq!(
        g.node_count(),
        6,
        "rebuild merges classes, not arena entries"
    );
    assert_congruence_closed(&mut g);
}

#[test]
fn book_example_union_a_b_merges_the_parents() {
    // The chapter-6 story: f(a,b) and f(b,b) become equal after union(a,b).
    let mut g = EGraph::new();
    let a = g.add(Op::Const(0), &[]);
    let b = g.add(Op::Const(1), &[]);
    let left = g.add(Op::F, &[a, b]);
    let right = g.add(Op::F, &[b, b]);
    assert_ne!(g.find(left), g.find(right));
    g.union(a, b);
    g.rebuild();
    assert_eq!(g.find(left), g.find(right));
}

#[derive(Clone, Debug)]
enum EgOp {
    Leaf(u8),
    F(usize, usize),
    Union(usize, usize),
}

fn eg_ops() -> impl Strategy<Value = Vec<EgOp>> {
    let leaf = (0u8..6).prop_map(EgOp::Leaf);
    let f = (any::<usize>(), any::<usize>()).prop_map(|(a, b)| EgOp::F(a, b));
    let union = (any::<usize>(), any::<usize>()).prop_map(|(a, b)| EgOp::Union(a, b));
    proptest::collection::vec(prop_oneof![leaf, f, union], 1..40)
}

fn run_egraph_ops(ops: &[EgOp]) {
    let mut g = EGraph::new();
    let mut ids: Vec<Id> = Vec::new();
    for op in ops {
        match *op {
            EgOp::Leaf(tag) => ids.push(g.add(Op::Const(tag), &[])),
            EgOp::F(i, j) => {
                if ids.len() < 2 {
                    continue;
                }
                let x = ids[i % ids.len()];
                let y = ids[j % ids.len()];
                ids.push(g.add(Op::F, &[x, y]));
            }
            EgOp::Union(i, j) => {
                if ids.len() < 2 {
                    continue;
                }
                g.union(ids[i % ids.len()], ids[j % ids.len()]);
            }
        }
    }
    g.rebuild();
    assert_congruence_closed(&mut g);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn union_find_matches_naive_sets((n, ops) in uf_ops()) {
        run_uf_against_naive(n, &ops);
    }

    #[test]
    fn rebuild_closes_congruence_on_random_programs(ops in eg_ops()) {
        run_egraph_ops(&ops);
    }
}
