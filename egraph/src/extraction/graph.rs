// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The e-graph the library extracts from, and the term it extracts.

use crate::extraction::cost::Cost;
use std::collections::BTreeMap;

pub type ClassId = usize;
pub type NodeId = usize;

/// An e-node.
#[derive(Clone, Debug)]
pub struct Node {
    pub op: String,
    /// Integer payload, such as the bounds of an interval: exact, so an e-graph literal
    /// past `i64` is the number it is.
    pub ints: Vec<Cost>,
    /// String payload, such as the name of an atom.
    pub strings: Vec<String>,
    /// Child classes, positionally; for a flat node, its distinct operands, each once.
    pub children: Vec<ClassId>,
    /// For a multiset node, the multiplicity of each operand, parallel to `children`, or
    /// empty when every operand counts once; empty for every other node, whose children
    /// each count once. A count is never expanded into repeated children (see
    /// [`Graph::coalesce`]).
    pub mults: Vec<u64>,
    pub class: ClassId,
    /// The operator's algebraic kind. A multiset or set node is flat: its children
    /// are unordered and its rendering as a tree is free to choose.
    pub kind: Kind,
    /// Excluded from extraction, as a subsuming rewrite marks its input.
    pub subsumed: bool,
}

/// The algebraic kind of an operator, as the e-graph stores its nodes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Kind {
    /// Positional children.
    #[default]
    Plain,
    /// Two children, unordered.
    Comm,
    /// Associative only: an ordered sequence of operands, bracketed as `Assoc` says.
    Seq(Assoc),
    /// Associative and commutative: a multiset of operands.
    MSet,
    /// Associative, commutative, and idempotent: a set of operands.
    Set,
}

/// The bracketing an associative operator admits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Assoc {
    Both,
    Left,
    Right,
}

impl Kind {
    /// A multiset or set node: its operands are unordered, and its rendering as a
    /// tree is a decision of the rung.
    pub fn flat(self) -> bool {
        matches!(self, Kind::MSet | Kind::Set)
    }

    /// A node whose bracketing is a decision of the rung: a multiset or set node, or
    /// an associative sequence (`Assoc::Both`). A fold (`Assoc::Left`, `Assoc::Right`)
    /// has one bracketing.
    pub fn bracketed(self) -> bool {
        self.flat() || self == Kind::Seq(Assoc::Both)
    }

    /// A fold: one bracketing, fixed by its direction.
    pub fn fold(self) -> Option<Assoc> {
        match self {
            Kind::Seq(a @ (Assoc::Left | Assoc::Right)) => Some(a),
            _ => None,
        }
    }
}

impl Node {
    pub fn flat(&self) -> bool {
        self.kind.flat()
    }
}

/// An e-graph: nodes, the members of each class, and the root class.
#[derive(Clone, Debug, Default)]
pub struct Graph {
    pub nodes: Vec<Node>,
    pub classes: Vec<Vec<NodeId>>,
    pub root: ClassId,
}

impl Graph {
    /// Members eligible for extraction.
    pub fn candidates(&self, c: ClassId) -> impl Iterator<Item = NodeId> + '_ {
        self.classes[c]
            .iter()
            .copied()
            .filter(move |&n| !self.nodes[n].subsumed)
    }

    /// Classes the root reaches through candidates, ascending.
    pub fn reachable(&self) -> Vec<ClassId> {
        let mut seen = vec![false; self.classes.len()];
        let mut stack = vec![self.root];
        while let Some(c) = stack.pop() {
            if std::mem::replace(&mut seen[c], true) {
                continue;
            }
            for n in self.candidates(c) {
                stack.extend(self.nodes[n].children.iter().copied());
            }
        }
        (0..self.classes.len()).filter(|&c| seen[c]).collect()
    }

    /// The multiplicity of operand `i` of `n` (an index into [`Self::operands`]): its
    /// stored count under an AC operator, 1 otherwise.
    pub fn multiplicity(&self, n: NodeId, i: usize) -> u64 {
        self.nodes[n].mults.get(i).copied().unwrap_or(1)
    }

    /// Bring every flat node to its stored form: a multiset node's repeated children
    /// become one operand with the sum of their counts, and a set node's are deduplicated,
    /// in first-occurrence order. A graph built by hand may list a class twice; the
    /// encodings read the stored form only. `Err` when a summed count exceeds u64.
    pub fn coalesce(&mut self) -> Result<(), String> {
        for node in &mut self.nodes {
            if !node.flat() {
                continue;
            }
            let multiset = node.kind == Kind::MSet;
            let mut kids: Vec<ClassId> = Vec::new();
            let mut counts: Vec<u64> = Vec::new();
            for (i, &k) in node.children.iter().enumerate() {
                let m = node.mults.get(i).copied().unwrap_or(1);
                match kids.iter().position(|&x| x == k) {
                    Some(j) => {
                        counts[j] = counts[j].checked_add(m).ok_or_else(|| {
                            format!(
                                "the multiplicities of class {k} under node {} sum past u64",
                                node.op
                            )
                        })?;
                    }
                    None => {
                        kids.push(k);
                        counts.push(m);
                    }
                }
            }
            node.children = kids;
            node.mults = if multiset { counts } else { Vec::new() };
        }
        Ok(())
    }

    /// The leaves of `n`'s tree, which a [`Tree::Leaf`] indexes: the distinct operands
    /// of a multiset or set node, the children in order of any other node (a
    /// sequence's leaves are positions, and a class may occupy several).
    pub fn leaves(&self, n: NodeId) -> Vec<ClassId> {
        if self.nodes[n].flat() {
            self.operands(n)
        } else {
            self.nodes[n].children.clone()
        }
    }

    /// The multiplicity of leaf `i` of `n`: its stored count for a multiset node, 1 for a
    /// set node or a position of a sequence.
    pub fn leaf_multiplicity(&self, n: NodeId, i: usize) -> u64 {
        if self.nodes[n].flat() {
            self.multiplicity(n, i)
        } else {
            1
        }
    }

    /// Distinct children in first-occurrence order: the operands of a flat node
    /// under maximum-partition semantics (its stored children).
    pub fn operands(&self, n: NodeId) -> Vec<ClassId> {
        let node = &self.nodes[n];
        if node.flat() {
            debug_assert!(
                node.children
                    .iter()
                    .enumerate()
                    .all(|(i, k)| !node.children[..i].contains(k))
                    && (node.mults.is_empty() || node.mults.len() == node.children.len()),
                "flat node {n} is not in stored form (distinct children, a count each or none): call Graph::coalesce"
            );
            return node.children.clone();
        }
        let mut out = Vec::new();
        for &k in &self.nodes[n].children {
            if !out.contains(&k) {
                out.push(k);
            }
        }
        out
    }
}

/// The rendering of a flat node: leaves index its operands.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Tree {
    Leaf(usize),
    Node(Vec<Tree>),
}

impl Tree {
    /// A canonical string, the same for every ordering of operands.
    pub fn canon(&self) -> String {
        match self {
            Tree::Leaf(i) => i.to_string(),
            Tree::Node(ops) => {
                let mut p: Vec<String> = ops.iter().map(Tree::canon).collect();
                p.sort();
                format!("({})", p.join(" "))
            }
        }
    }

    /// A string that respects the order of operands.
    pub fn ordered(&self) -> String {
        match self {
            Tree::Leaf(i) => i.to_string(),
            Tree::Node(ops) => format!(
                "({})",
                ops.iter().map(Tree::ordered).collect::<Vec<_>>().join(" ")
            ),
        }
    }

    pub fn is_flat(&self) -> bool {
        matches!(self, Tree::Node(o) if o.iter().all(|x| matches!(x, Tree::Leaf(_))))
    }
}

/// An extracted term: the selected member of each class it contains, and the
/// rendering of each flat node whose tree was a decision. Classes not in the term
/// are `None`.
#[derive(Clone, Debug, Default)]
pub struct Term {
    pub selection: Vec<Option<NodeId>>,
    pub trees: BTreeMap<NodeId, Tree>,
}

impl Term {
    /// The classes of the term, children before parents, or the classes of a cycle.
    pub fn order(&self, g: &Graph) -> Result<Vec<ClassId>, Vec<ClassId>> {
        const WHITE: u8 = 0;
        const GRAY: u8 = 1;
        const BLACK: u8 = 2;
        let mut colour = vec![WHITE; g.classes.len()];
        let mut order = Vec::new();
        let mut path = vec![g.root];
        let mut stack: Vec<(ClassId, usize)> = vec![(g.root, 0)];
        colour[g.root] = GRAY;
        while let Some(&mut (c, ref mut i)) = stack.last_mut() {
            let kids: &[ClassId] = match self.selection[c] {
                Some(n) => &g.nodes[n].children,
                None => &[],
            };
            if *i < kids.len() {
                let k = kids[*i];
                *i += 1;
                match colour[k] {
                    WHITE => {
                        colour[k] = GRAY;
                        path.push(k);
                        stack.push((k, 0));
                    }
                    GRAY => {
                        let j = path.iter().position(|&x| x == k).unwrap();
                        return Err(path[j..].to_vec());
                    }
                    _ => {}
                }
            } else {
                colour[c] = BLACK;
                order.push(c);
                path.pop();
                stack.pop();
            }
        }
        Ok(order)
    }

    /// The term as JSON: `{"root": ref, "nodes": {ref: {"op", "children", "ints",
    /// "strings"}}}`, each class once, so a shared subterm
    /// stays shared. A flat node whose tree was a decision is written as that tree,
    /// its internal nodes carrying the node's operator. A multiset node, and each
    /// internal node of its tree, also carries `"mults"`, the count of each child,
    /// parallel to `"children"`: a child of multiplicity k is listed once.
    pub fn to_json(&self, g: &Graph) -> Result<String, Vec<ClassId>> {
        let order = self.order(g)?;
        let mut nodes = serde_json::Map::new();
        let class_ref = |c: ClassId| format!("c{c}");
        for &c in &order {
            let n = self.selection[c].expect("an ordered class is in the term");
            let node = &g.nodes[n];
            let multiset = node.kind == Kind::MSet;
            let entry = |children: Vec<(String, u64)>| {
                let (refs, mults): (Vec<String>, Vec<u64>) = children.into_iter().unzip();
                // An integer in `i64` is a JSON number; a wider one is its decimal string, since
                // JSON readers commonly hold numbers as doubles.
                let ints: Vec<serde_json::Value> = node
                    .ints
                    .iter()
                    .map(|v| {
                        v.to_i64().map_or_else(
                            || serde_json::json!(v.to_string()),
                            |x| serde_json::json!(x),
                        )
                    })
                    .collect();
                let mut e = serde_json::json!({ "op": node.op, "children": refs, "ints": ints, "strings": node.strings });
                if multiset {
                    e["mults"] = serde_json::json!(mults);
                }
                e
            };
            match self.trees.get(&n) {
                Some(tree) => {
                    let ops = g.leaves(n);
                    let mut next = 0usize;
                    // A leaf is one operand with its whole multiplicity: the copies
                    // stay together, so the leaf's parent lists it once with its count.
                    let mult: Vec<u64> =
                        (0..ops.len()).map(|i| g.leaf_multiplicity(n, i)).collect();
                    #[allow(clippy::type_complexity)]
                    fn write(
                        t: &Tree,
                        top: bool,
                        c: ClassId,
                        ops: &[ClassId],
                        mult: &[u64],
                        next: &mut usize,
                        out: &mut Vec<(String, Vec<(String, u64)>)>,
                    ) -> String {
                        match t {
                            Tree::Leaf(i) => format!("c{}", ops[*i]),
                            Tree::Node(kids) => {
                                let mut refs: Vec<(String, u64)> = Vec::new();
                                for k in kids {
                                    let r = write(k, false, c, ops, mult, next, out);
                                    let times = if let Tree::Leaf(i) = k { mult[*i] } else { 1 };
                                    refs.push((r, times));
                                }
                                let me = if top {
                                    format!("c{c}")
                                } else {
                                    *next += 1;
                                    format!("c{c}.{}", *next)
                                };
                                out.push((me.clone(), refs));
                                me
                            }
                        }
                    }
                    let mut out = Vec::new();
                    write(tree, true, c, &ops, &mult, &mut next, &mut out);
                    for (r, kids) in out {
                        nodes.insert(r, entry(kids));
                    }
                }
                None => {
                    nodes.insert(
                        class_ref(c),
                        entry(
                            node.children
                                .iter()
                                .enumerate()
                                .map(|(i, &k)| (class_ref(k), g.leaf_multiplicity(n, i)))
                                .collect(),
                        ),
                    );
                }
            }
        }
        let v = serde_json::json!({ "root": class_ref(g.root), "nodes": nodes });
        Ok(serde_json::to_string_pretty(&v).expect("serializable"))
    }
}
