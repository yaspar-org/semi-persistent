// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The e-graph and a rung as a MiniZinc model, for criteria written in MiniZinc.
//!
//! [`dump`] writes the reachable e-graph as data and the rung as variables and
//! constraints; the user's criteria (their own variables, constraints, and one
//! `solve minimize` item) are appended, and a MiniZinc solver solves the whole.
//! Integers stay integer variables: nothing is order-encoded before the solver sees
//! it. [`extract`] decodes the solution into a [`Term`] and reports the objective on
//! that term by solving again with the term fixed.
//!
//! # Names
//!
//! Classes are `1..C` and nodes `1..N`, over the reachable classes and their
//! candidates; `class_id[c]` and `node_id[n]` give the e-graph's ids.
//!
//! | name | meaning |
//! | --- | --- |
//! | `ROOT`, `cls[n]`, `op[n]` | the root class; node `n`'s class and operator (a string) |
//! | `kind[n]` | `PLAIN`, `COMM`, `SEQ`, `SEQ_LEFT`, `SEQ_RIGHT`, `MSET`, or `SET` |
//! | `kids[n]`, `nkid[n]`, `kid[n, i]` | distinct operand classes; the children in order (0-padded); a flat node's children are its distinct operands |
//! | `kmult[n, i]`, `mult(n, k)` | child `i`'s multiplicity (its stored count under an AC operator, 1 otherwise); the multiplicity of class `k` among `n`'s children |
//! | `nint[n]`, `ints[n, j]` | integer payload |
//! | `first[c]` | class `c`'s first candidate |
//! | `nleaf[n]`, `leaf[n, p]` | the leaves of `n`'s tree: distinct operands of an AC node, positions of a sequence, distinct operands otherwise |
//! | `used[c]`, `pick[n]` | the class is in the term; the node is its class's choice |
//! | `rank[c]` | the term's height at `c` (0 when unused): the chosen term is acyclic |
//! | `B`, `bnode[b]` | blocks `1..B` (internal nodes a tree may have) and their node |
//! | `inner[b]`, `bmem[b, p]` | the block exists; leaf `p` lies under it |
//! | `parent_leaf[n, p]`, `parent_blk[b]` | the innermost block around a leaf or a block (0 is the root) |
//! | `depth[n, p]` | leaf `p`'s depth, 1 directly under the root |
//! | `pos_leaf[n, p]`, `pos_blk[b]` | at the orders rung, a child's position in its block (AC only) |

use crate::extraction::graph::{Assoc, ClassId, Graph, Kind, NodeId, Term, Tree};
use crate::extraction::rung::{MAX_ARITY, MAX_ORDERED_ARITY, RungKind};
use crate::extraction::solve::{OpbCommand, Status};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

fn quote(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

fn leaves(g: &Graph, n: NodeId) -> Vec<ClassId> {
    match g.nodes[n].kind {
        Kind::Seq(_) => g.nodes[n].children.clone(),
        _ => g.operands(n),
    }
}

fn free_tree(g: &Graph, n: NodeId, rung: RungKind) -> bool {
    if rung == RungKind::Selection {
        return false;
    }
    let k = leaves(g, n).len();
    match g.nodes[n].kind {
        Kind::MSet | Kind::Set => {
            k >= 3
                && k <= if rung == RungKind::Orders {
                    MAX_ORDERED_ARITY
                } else {
                    MAX_ARITY
                }
        }
        Kind::Seq(Assoc::Both) => (3..=MAX_ARITY).contains(&k),
        _ => false,
    }
}

/// The numbering a dump uses, to decode solutions.
pub struct Index {
    pub classes: Vec<ClassId>,
    pub nodes: Vec<NodeId>,
    /// Per block: its node, and its interval (a sequence or fold) or least leaf and size (AC), 0-based.
    blocks: Vec<(NodeId, bool, usize, usize)>,
}

fn index(g: &Graph, rung: RungKind) -> Index {
    let classes = g.reachable();
    let nodes: Vec<NodeId> = classes
        .iter()
        .flat_map(|&c| g.candidates(c).collect::<Vec<_>>())
        .collect();
    let mut blocks = Vec::new();
    for &n in &nodes {
        let k = leaves(g, n).len();
        if free_tree(g, n, rung) {
            if g.nodes[n].kind == Kind::Seq(Assoc::Both) {
                for i in 0..k {
                    for j in (i + 1)..k {
                        if (i, j) != (0, k - 1) {
                            blocks.push((n, true, i, j));
                        }
                    }
                }
            } else {
                for r in 0..k {
                    for s in 2..k {
                        if r + s <= k {
                            blocks.push((n, false, r, s));
                        }
                    }
                }
            }
        } else if let Some(dir) = g.nodes[n].kind.fold() {
            for len in 2..k {
                let (i, j) = if dir == Assoc::Left {
                    (0, len - 1)
                } else {
                    (k - len, k - 1)
                };
                blocks.push((n, true, i, j));
            }
        }
    }
    Index {
        classes,
        nodes,
        blocks,
    }
}

/// The reachable e-graph as data, and the rung as variables and constraints.
pub fn dump(g: &Graph, rung: RungKind) -> String {
    let ix = index(g, rung);
    let cpos: BTreeMap<ClassId, usize> = ix
        .classes
        .iter()
        .enumerate()
        .map(|(i, &c)| (c, i + 1))
        .collect();
    let npos: BTreeMap<NodeId, usize> = ix
        .nodes
        .iter()
        .enumerate()
        .map(|(i, &n)| (n, i + 1))
        .collect();
    let (c_n, n_n, b_n) = (ix.classes.len(), ix.nodes.len(), ix.blocks.len());
    let maxk = ix
        .nodes
        .iter()
        .map(|&n| g.nodes[n].children.len())
        .max()
        .unwrap_or(0)
        .max(1);
    let maxl = ix
        .nodes
        .iter()
        .map(|&n| leaves(g, n).len())
        .max()
        .unwrap_or(0)
        .max(1);
    let maxj = ix
        .nodes
        .iter()
        .map(|&n| g.nodes[n].ints.len())
        .max()
        .unwrap_or(0)
        .max(1);
    let mut o = String::new();
    let list = |xs: Vec<String>| format!("[{}]", xs.join(", "));
    let grid = |rows: Vec<Vec<String>>, w: usize, pad: &str| {
        let body: Vec<String> = rows
            .into_iter()
            .map(|r| {
                let mut r = r;
                r.resize(w, pad.to_string());
                r.join(", ")
            })
            .collect();
        format!("[| {} |]", body.join(" | "))
    };
    let _ = writeln!(o, "% The e-graph.");
    let _ = writeln!(
        o,
        "int: C = {c_n};\nint: N = {n_n};\nint: B = {b_n};\nint: MAXK = {maxk};\nint: MAXL = {maxl};\nint: MAXJ = {maxj};"
    );
    let _ = writeln!(o, "int: ROOT = {};", cpos[&g.root]);
    let _ = writeln!(
        o,
        "int: PLAIN = 0; int: COMM = 1; int: SEQ = 2; int: SEQ_LEFT = 3; int: SEQ_RIGHT = 4; int: MSET = 5; int: SET = 6;"
    );
    let _ = writeln!(
        o,
        "array[1..C] of int: class_id = {};",
        list(ix.classes.iter().map(|c| c.to_string()).collect())
    );
    let _ = writeln!(
        o,
        "array[1..N] of int: node_id = {};",
        list(ix.nodes.iter().map(|n| n.to_string()).collect())
    );
    let _ = writeln!(
        o,
        "array[1..N] of 1..C: cls = {};",
        list(
            ix.nodes
                .iter()
                .map(|&n| cpos[&g.nodes[n].class].to_string())
                .collect()
        )
    );
    let _ = writeln!(
        o,
        "array[1..N] of string: op = {};",
        list(ix.nodes.iter().map(|&n| quote(&g.nodes[n].op)).collect())
    );
    let kind = |k: Kind| match k {
        Kind::Plain => 0,
        Kind::Comm => 1,
        Kind::Seq(Assoc::Both) => 2,
        Kind::Seq(Assoc::Left) => 3,
        Kind::Seq(Assoc::Right) => 4,
        Kind::MSet => 5,
        Kind::Set => 6,
    };
    let _ = writeln!(
        o,
        "array[1..N] of int: kind = {};",
        list(
            ix.nodes
                .iter()
                .map(|&n| kind(g.nodes[n].kind).to_string())
                .collect()
        )
    );
    let _ = writeln!(
        o,
        "array[1..N] of set of 1..C: kids = {};",
        list(
            ix.nodes
                .iter()
                .map(|&n| format!(
                    "{{{}}}",
                    g.operands(n)
                        .iter()
                        .map(|k| cpos[k].to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ))
                .collect()
        )
    );
    let _ = writeln!(
        o,
        "array[1..N] of int: nkid = {};",
        list(
            ix.nodes
                .iter()
                .map(|&n| g.nodes[n].children.len().to_string())
                .collect()
        )
    );
    let _ = writeln!(
        o,
        "array[1..N, 1..MAXK] of 0..C: kid = {};",
        grid(
            ix.nodes
                .iter()
                .map(|&n| g.nodes[n]
                    .children
                    .iter()
                    .map(|k| cpos[k].to_string())
                    .collect())
                .collect(),
            maxk,
            "0"
        )
    );
    let _ = writeln!(
        o,
        "array[1..N, 1..MAXK] of int: kmult = {};",
        grid(
            ix.nodes
                .iter()
                .map(|&n| (0..g.nodes[n].children.len())
                    .map(|i| g.leaf_multiplicity(n, i).to_string())
                    .collect())
                .collect(),
            maxk,
            "0"
        )
    );
    let _ = writeln!(
        o,
        "function int: mult(int: n, int: k) = sum(i in 1..nkid[n])(if kid[n, i] = k then kmult[n, i] else 0 endif);"
    );
    let _ = writeln!(
        o,
        "array[1..N] of int: nint = {};",
        list(
            ix.nodes
                .iter()
                .map(|&n| g.nodes[n].ints.len().to_string())
                .collect()
        )
    );
    let _ = writeln!(
        o,
        "array[1..N, 1..MAXJ] of int: ints = {};",
        grid(
            ix.nodes
                .iter()
                .map(|&n| g.nodes[n].ints.iter().map(|v| v.to_string()).collect())
                .collect(),
            maxj,
            "0"
        )
    );
    let _ = writeln!(
        o,
        "array[1..C] of 1..N: first = {};",
        list(
            ix.classes
                .iter()
                .map(|&c| npos[&g.candidates(c).next().unwrap()].to_string())
                .collect()
        )
    );
    let _ = writeln!(
        o,
        "array[1..N] of int: nleaf = {};",
        list(
            ix.nodes
                .iter()
                .map(|&n| leaves(g, n).len().to_string())
                .collect()
        )
    );
    let _ = writeln!(
        o,
        "array[1..N, 1..MAXL] of 0..C: leaf = {};",
        grid(
            ix.nodes
                .iter()
                .map(|&n| leaves(g, n).iter().map(|k| cpos[k].to_string()).collect())
                .collect(),
            maxl,
            "0"
        )
    );
    // Tree data: per node its rung family; per block its node, style, and bounds (1-based).
    let fam = |n: NodeId| -> &str {
        if free_tree(g, n, rung) {
            match rung {
                RungKind::Levels => "1",
                RungKind::Binary => "3",
                RungKind::Orders if g.nodes[n].kind != Kind::Seq(Assoc::Both) => "4",
                _ => "2",
            }
        } else if g.nodes[n].kind.fold().is_some() && leaves(g, n).len() >= 3 {
            "5"
        } else {
            "0"
        }
    };
    let _ = writeln!(
        o,
        "% 0 no tree, 1 chains, 2 trees, 3 binary trees, 4 ordered trees, 5 a fold."
    );
    let _ = writeln!(
        o,
        "array[1..N] of int: family = {};",
        list(ix.nodes.iter().map(|&n| fam(n).to_string()).collect())
    );
    let _ = writeln!(
        o,
        "array[1..B] of 1..N: bnode = {};",
        list(ix.blocks.iter().map(|b| npos[&b.0].to_string()).collect())
    );
    let _ = writeln!(
        o,
        "array[1..B] of bool: interval = {};",
        list(ix.blocks.iter().map(|b| b.1.to_string()).collect())
    );
    let _ = writeln!(
        o,
        "array[1..B] of int: blo = {};",
        list(ix.blocks.iter().map(|b| (b.2 + 1).to_string()).collect())
    );
    let _ = writeln!(
        o,
        "array[1..B] of int: bhi = {};",
        list(
            ix.blocks
                .iter()
                .map(|b| if b.1 { b.3 + 1 } else { b.3 }.to_string())
                .collect()
        )
    );
    o.push_str(RULES);
    o
}

/// The selection and tree constraints, over the data [`dump`] writes.
const RULES: &str = r#"
% Selection: the root is used; a class is used exactly when it is the root or an
% operand of a picked node; a used class picks one candidate; the term's height is
% its rank, so the chosen term is acyclic and the rank is determined.
array[1..C] of var bool: used;
array[1..N] of var bool: pick;
array[1..C] of var 0..C: rank;
constraint used[ROOT];
constraint forall(c in 1..C)(used[c] <-> (c = ROOT \/ exists(n in 1..N where c in kids[n])(pick[n])));
constraint forall(c in 1..C)(sum(n in 1..N where cls[n] = c)(bool2int(pick[n])) = bool2int(used[c]));
constraint forall(c in 1..C)(not used[c] -> rank[c] = 0);
constraint forall(n in 1..N)(pick[n] -> rank[cls[n]] = 1 + max([0] ++ [rank[k] | k in kids[n]]));

% Blocks: free at the tree rungs, fixed for a fold, only under a picked node.
array[1..B] of var bool: inner;
array[1..B, 1..MAXL] of var bool: bmem;
constraint forall(b in 1..B)(inner[b] -> pick[bnode[b]]);
constraint forall(b in 1..B where family[bnode[b]] = 5)(inner[b] = pick[bnode[b]]);
constraint forall(b in 1..B, p in 1..MAXL where interval[b])(bmem[b, p] = (inner[b] /\ blo[b] <= p /\ p <= bhi[b]));
constraint forall(b in 1..B where not interval[b])(
    bmem[b, blo[b]] = inner[b]
    /\ forall(p in 1..MAXL where p < blo[b] \/ p > nleaf[bnode[b]])(not bmem[b, p])
    /\ forall(p in 1..MAXL)(bmem[b, p] -> inner[b])
    /\ sum(p in 1..MAXL)(bool2int(bmem[b, p])) = bhi[b] * bool2int(inner[b]));
predicate meet(int: b1, int: b2) = exists(p in 1..MAXL)(bmem[b1, p] /\ bmem[b2, p]);
predicate within(int: b1, int: b2) = inner[b1] /\ inner[b2] /\ forall(p in 1..MAXL)(bmem[b1, p] -> bmem[b2, p]);
constraint forall(b1, b2 in 1..B where b1 < b2 /\ bnode[b1] = bnode[b2])(
    (inner[b1] /\ inner[b2] /\ meet(b1, b2)) -> (within(b1, b2) \/ within(b2, b1)));
constraint forall(b1, b2 in 1..B where b1 < b2 /\ bnode[b1] = bnode[b2] /\ family[bnode[b1]] = 1)(
    (inner[b1] /\ inner[b2]) -> meet(b1, b2));
constraint forall(n in 1..N where family[n] = 3)(
    pick[n] -> sum(b in 1..B where bnode[b] = n)(bool2int(inner[b])) = nleaf[n] - 2);

% The tree: the innermost block around each leaf and each block (0 is the root).
array[1..N, 1..MAXL] of var 0..B: parent_leaf;
array[1..B] of var 0..B: parent_blk;
constraint forall(n in 1..N, p in 1..MAXL)(
    if p > nleaf[n] \/ family[n] = 0 then parent_leaf[n, p] = 0
    else
        (parent_leaf[n, p] = 0 <-> not exists(b in 1..B where bnode[b] = n)(bmem[b, p]))
        /\ forall(b in 1..B where bnode[b] = n)(parent_leaf[n, p] = b <->
            (bmem[b, p] /\ not exists(b2 in 1..B where bnode[b2] = n /\ b2 != b)(bmem[b2, p] /\ within(b2, b))))
        /\ parent_leaf[n, p] in {0} union {b | b in 1..B where bnode[b] = n}
    endif);
constraint forall(b in 1..B)(
    (parent_blk[b] = 0 <-> not exists(b2 in 1..B where bnode[b2] = bnode[b] /\ b2 != b)(inner[b] /\ within(b, b2)))
    /\ forall(b2 in 1..B where bnode[b2] = bnode[b] /\ b2 != b)(parent_blk[b] = b2 <->
        (within(b, b2) /\ not exists(b3 in 1..B where bnode[b3] = bnode[b] /\ b3 != b /\ b3 != b2)(within(b, b3) /\ within(b3, b2))))
    /\ parent_blk[b] in {0} union {b2 | b2 in 1..B where bnode[b2] = bnode[b] /\ b2 != b});
array[1..N, 1..MAXL] of var 1..MAXL: depth;
constraint forall(n in 1..N, p in 1..MAXL)(
    depth[n, p] = 1 + sum(b in 1..B where bnode[b] = n)(bool2int(bmem[b, p])));

% Orders: the children of each block (and of the root) take positions 0 to m - 1.
array[1..N, 1..MAXL] of var 0..MAXL: pos_leaf;
array[1..B] of var 0..MAXL: pos_blk;
function var int: children(int: n, var int: g) =
    sum(p in 1..nleaf[n])(bool2int(parent_leaf[n, p] = g))
    + sum(b in 1..B where bnode[b] = n)(bool2int(inner[b] /\ parent_blk[b] = g));
constraint forall(n in 1..N, p in 1..MAXL)(
    if family[n] = 4 /\ p <= nleaf[n] then (pick[n] -> pos_leaf[n, p] < children(n, parent_leaf[n, p])) /\ (not pick[n] -> pos_leaf[n, p] = 0)
    else pos_leaf[n, p] = 0 endif);
constraint forall(b in 1..B)(
    if family[bnode[b]] = 4 then (inner[b] -> pos_blk[b] < children(bnode[b], parent_blk[b])) /\ (not inner[b] -> pos_blk[b] = 0)
    else pos_blk[b] = 0 endif);
constraint forall(n in 1..N where family[n] = 4)(
    forall(p, q in 1..nleaf[n] where p < q)((pick[n] /\ parent_leaf[n, p] = parent_leaf[n, q]) -> pos_leaf[n, p] != pos_leaf[n, q])
    /\ forall(p in 1..nleaf[n], b in 1..B where bnode[b] = n)((inner[b] /\ parent_leaf[n, p] = parent_blk[b]) -> pos_leaf[n, p] != pos_blk[b])
    /\ forall(b1, b2 in 1..B where b1 < b2 /\ bnode[b1] = n /\ bnode[b2] = n)((inner[b1] /\ inner[b2] /\ parent_blk[b1] = parent_blk[b2]) -> pos_blk[b1] != pos_blk[b2]));
"#;

/// The solution's values of the names decoding needs.
struct Sol {
    pick: Vec<bool>,
    inner: Vec<bool>,
    bmem: Vec<Vec<bool>>,
    pos_leaf: Vec<Vec<i64>>,
    pos_blk: Vec<i64>,
}

fn sol(v: &serde_json::Value) -> Sol {
    let bools = |x: &serde_json::Value| {
        x.as_array()
            .map(|a| a.iter().map(|b| b.as_bool().unwrap_or(false)).collect())
            .unwrap_or_default()
    };
    let ints = |x: &serde_json::Value| {
        x.as_array()
            .map(|a| a.iter().map(|b| b.as_i64().unwrap_or(0)).collect())
            .unwrap_or_default()
    };
    Sol {
        pick: bools(&v["pick"]),
        inner: bools(&v["inner"]),
        bmem: v["bmem"]
            .as_array()
            .map(|r| r.iter().map(bools).collect())
            .unwrap_or_default(),
        pos_leaf: v["pos_leaf"]
            .as_array()
            .map(|r| r.iter().map(ints).collect())
            .unwrap_or_default(),
        pos_blk: ints(&v["pos_blk"]),
    }
}

/// The term a solution denotes.
fn decode(g: &Graph, ix: &Index, s: &Sol) -> Term {
    let mut selection = vec![None; g.classes.len()];
    for (i, &n) in ix.nodes.iter().enumerate() {
        if s.pick.get(i).copied().unwrap_or(false) {
            selection[g.nodes[n].class] = Some(n);
        }
    }
    let mut trees = BTreeMap::new();
    for (i, &n) in ix.nodes.iter().enumerate() {
        if !s.pick.get(i).copied().unwrap_or(false) {
            continue;
        }
        let bs: Vec<usize> = (0..ix.blocks.len())
            .filter(|&b| ix.blocks[b].0 == n)
            .collect();
        let free = bs.first().is_some_and(|_| g.nodes[n].kind.fold().is_none());
        if !free {
            continue;
        }
        let k = leaves(g, n).len();
        let sets: Vec<(usize, BTreeSet<usize>)> = bs
            .iter()
            .filter(|&&b| s.inner[b])
            .map(|&b| (b, (0..k).filter(|&p| s.bmem[b][p]).collect()))
            .collect();
        let pl = s.pos_leaf.get(i).cloned().unwrap_or_default();
        trees.insert(n, build(&sets, &(0..k).collect(), &pl, &s.pos_blk));
    }
    Term { selection, trees }
}

fn build(
    blocks: &[(usize, BTreeSet<usize>)],
    set: &BTreeSet<usize>,
    pl: &[i64],
    pb: &[i64],
) -> Tree {
    let within: Vec<&(usize, BTreeSet<usize>)> = blocks
        .iter()
        .filter(|(_, s)| s.is_subset(set) && s != set)
        .collect();
    let maximal: Vec<&(usize, BTreeSet<usize>)> = within
        .iter()
        .copied()
        .filter(|(_, s)| !within.iter().any(|(_, t)| t != s && s.is_subset(t)))
        .collect();
    let covered: BTreeSet<usize> = maximal
        .iter()
        .flat_map(|(_, s)| s.iter().copied())
        .collect();
    let mut kids: Vec<(i64, usize, Tree)> = Vec::new();
    for &p in set.iter().filter(|p| !covered.contains(p)) {
        kids.push((pl.get(p).copied().unwrap_or(0), p, Tree::Leaf(p)));
    }
    for (b, s) in maximal {
        let least = *s.iter().next().unwrap();
        kids.push((
            pb.get(*b).copied().unwrap_or(0),
            least,
            build(blocks, s, pl, pb),
        ));
    }
    kids.sort_by_key(|(q, l, _)| (*q, *l));
    Tree::Node(kids.into_iter().map(|(_, _, t)| t).collect())
}

/// Constraints fixing `term`: every candidate picked exactly when the term picks it,
/// every block present exactly when the term's tree has it (with its leaves), and at
/// the orders rung every child's position.
pub fn fix_term(g: &Graph, rung: RungKind, term: &Term) -> String {
    let ix = index(g, rung);
    let mut o = String::from("% The term.\n");
    for (i, &n) in ix.nodes.iter().enumerate() {
        let c = g.nodes[n].class;
        let picked = term.selection[c] == Some(n);
        let _ = writeln!(o, "constraint pick[{}] = {picked};", i + 1);
        if !picked || !free_tree(g, n, rung) {
            continue;
        }
        let k = leaves(g, n).len();
        let flat = Tree::Node((0..k).map(Tree::Leaf).collect());
        let tree = term.trees.get(&n).unwrap_or(&flat);
        fn members(t: &Tree, out: &mut BTreeSet<usize>) {
            match t {
                Tree::Leaf(p) => {
                    out.insert(*p);
                }
                Tree::Node(ks) => ks.iter().for_each(|x| members(x, out)),
            }
        }
        // The leaf sets of the tree's internal nodes, the root excluded.
        fn blocks_of(t: &Tree, top: bool, out: &mut Vec<BTreeSet<usize>>) {
            let Tree::Node(ks) = t else { return };
            if !top {
                let mut m = BTreeSet::new();
                members(t, &mut m);
                out.push(m);
            }
            for x in ks {
                blocks_of(x, false, out);
            }
        }
        let mut present: Vec<BTreeSet<usize>> = Vec::new();
        blocks_of(tree, true, &mut present);
        for (b, blk) in ix.blocks.iter().enumerate().filter(|(_, b)| b.0 == n) {
            let set: BTreeSet<usize> = if blk.1 {
                (blk.2..=blk.3).collect()
            } else {
                BTreeSet::new()
            };
            let on = present.iter().any(|m| {
                if blk.1 {
                    *m == set
                } else {
                    m.iter().next() == Some(&blk.2) && m.len() == blk.3
                }
            });
            let _ = writeln!(o, "constraint inner[{}] = {on};", b + 1);
            if on && !blk.1 {
                let m = present
                    .iter()
                    .find(|m| m.iter().next() == Some(&blk.2) && m.len() == blk.3)
                    .unwrap();
                for p in 0..k {
                    let _ = writeln!(
                        o,
                        "constraint bmem[{}, {}] = {};",
                        b + 1,
                        p + 1,
                        m.contains(&p)
                    );
                }
            }
        }
        if rung == RungKind::Orders && g.nodes[n].kind != Kind::Seq(Assoc::Both) {
            fn order(t: &Tree, out: &mut Vec<(Result<usize, BTreeSet<usize>>, usize)>) {
                let Tree::Node(ks) = t else { return };
                for (q, x) in ks.iter().enumerate() {
                    match x {
                        Tree::Leaf(p) => out.push((Ok(*p), q)),
                        Tree::Node(_) => {
                            let mut m = BTreeSet::new();
                            members(x, &mut m);
                            out.push((Err(m), q));
                            order(x, out);
                        }
                    }
                }
            }
            let mut ords = Vec::new();
            order(tree, &mut ords);
            for (x, q) in ords {
                match x {
                    Ok(p) => {
                        let _ = writeln!(o, "constraint pos_leaf[{}, {}] = {q};", i + 1, p + 1);
                    }
                    Err(m) => {
                        let b = ix
                            .blocks
                            .iter()
                            .position(|blk| {
                                blk.0 == n
                                    && !blk.1
                                    && m.iter().next() == Some(&blk.2)
                                    && m.len() == blk.3
                            })
                            .unwrap();
                        let _ = writeln!(o, "constraint pos_blk[{}] = {q};", b + 1);
                    }
                }
            }
        }
    }
    o
}

/// A MiniZinc extraction's outcome: the term, and the objective on it.
#[derive(Debug)]
pub struct MznOutcome {
    pub term: Option<Term>,
    pub cost: Option<i64>,
    pub status: Status,
    /// The solver's lower bound on the objective, when it reports one (`-s`).
    pub bound: Option<i64>,
}

/// Run MiniZinc on `model`: the last solution, its objective, whether the optimum was
/// proved, and whether the model is unsatisfiable. `cmd.program` is `minizinc`, and
/// `cmd.args` names the solver (`--solver cp-sat`) and any limits.
fn minizinc(
    cmd: &OpbCommand,
    model: &str,
    all: bool,
) -> Result<(Vec<serde_json::Value>, bool, bool, Option<i64>), String> {
    let path = crate::extraction::solve::temp_path("mzn");
    std::fs::write(&path, model).map_err(|e| e.to_string())?;
    if let Ok(dir) = std::env::var("EXTRACT_API_KEEP_MZN") {
        let n = std::fs::read_dir(&dir).map(|d| d.count()).unwrap_or(0);
        let _ = std::fs::copy(
            &path,
            std::path::Path::new(&dir).join(format!("call{n:03}.mzn")),
        );
    }
    let mut c = std::process::Command::new(&cmd.program);
    c.args(&cmd.args)
        .args(["--output-mode", "json", "--output-objective", "-s"]);
    // Every improving solution is printed (`-i`), so a solve stopped by a time limit
    // still reports its best; without it, a time-limited optimization prints none.
    c.arg(if all { "-a" } else { "-i" });
    let out = c.arg(&path).output();
    let _ = std::fs::remove_file(&path);
    let out = out.map_err(|e| format!("{}: {e}", cmd.program))?;
    let text = String::from_utf8_lossy(&out.stdout).to_string();
    let unsat = text.contains("=====UNSATISFIABLE=====");
    let optimum = text.contains("==========");
    let mut sols = Vec::new();
    for chunk in text.split("----------") {
        let t = chunk.trim().trim_start_matches("==========").trim();
        if let Some(start) = t.find('{') {
            // The solution is the first JSON value; statistics lines may follow it.
            if let Some(Ok(v)) = serde_json::Deserializer::from_str(&t[start..])
                .into_iter::<serde_json::Value>()
                .next()
            {
                sols.push(v);
            }
        }
    }
    // The bound is printed as a float: above 2^53 it is approximate, and the cast
    // saturates at the i64 range. It is reported, never used to decide a status.
    let bound = text
        .lines()
        .rev()
        .find_map(|l| l.strip_prefix("%%%mzn-stat: objectiveBound="))
        .and_then(|v| v.trim().parse::<f64>().ok())
        .map(|v| v.ceil() as i64);
    if sols.is_empty() && !unsat && !out.status.success() {
        return Err(format!(
            "minizinc: {}",
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok((sols, optimum, unsat, bound))
}

/// `Ok` when every integer the dump writes, a payload integer or a multiplicity, is in
/// the range of the solver `cmd` names ([`OpbCommand::mzn_range`]): Chuffed reads a value
/// past 32 bits wrongly without an error, and a MIP solver one past 2^53. What the criteria
/// compute from these values is checked by the MiniZinc compiler (64-bit), not here.
pub fn fits_minizinc(g: &Graph, cmd: &OpbCommand) -> Result<(), String> {
    fits_minizinc_values(g, cmd)
        .map_err(|e| format!("{e}. {}", crate::extraction::lp::CRITERIA_OWN_RISK))
}

fn fits_minizinc_values(g: &Graph, cmd: &OpbCommand) -> Result<(), String> {
    use crate::extraction::cost::Cost;
    let range = cmd.mzn_range();
    let name = cmd
        .args
        .iter()
        .position(|a| a == "--solver")
        .and_then(|i| cmd.args.get(i + 1))
        .cloned()
        .unwrap_or_else(|| "MiniZinc".into());
    for &c in &g.reachable() {
        for n in g.candidates(c) {
            for &v in &g.nodes[n].ints {
                range.check(
                    &name,
                    &format!("the integer of node {n} ({})", g.nodes[n].op),
                    v,
                )?;
            }
            for i in 0..g.operands(n).len() {
                range.check(
                    &name,
                    &format!("a multiplicity of node {n} ({})", g.nodes[n].op),
                    Cost::from(g.multiplicity(n, i)),
                )?;
            }
        }
    }
    Ok(())
}

/// Every solution of the dump with `extra` appended (a `solve satisfy` enumeration),
/// as terms.
pub fn enumerate(
    g: &Graph,
    rung: RungKind,
    extra: &str,
    cmd: &OpbCommand,
) -> Result<Vec<Term>, String> {
    fits_minizinc(g, cmd)?;
    let ix = index(g, rung);
    let (sols, _, _, _) = minizinc(cmd, &format!("{}\n{extra}\n", dump(g, rung)), true)?;
    Ok(sols.iter().map(|v| decode(g, &ix, &sol(v))).collect())
}

/// The objective of `criteria` on `term` at `rung`.
pub fn cost_of(
    g: &Graph,
    rung: RungKind,
    criteria: &str,
    term: &Term,
    cmd: &OpbCommand,
) -> Result<i64, String> {
    fits_minizinc(g, cmd)?;
    let model = format!(
        "{}\n% The criteria.\n{criteria}\n{}",
        dump(g, rung),
        fix_term(g, rung, term)
    );
    let (sols, _, _, _) = minizinc(cmd, &model, false)?;
    sols.last()
        .and_then(|v| v["_objective"].as_i64())
        .ok_or_else(|| "the term does not satisfy the criteria".to_string())
}

/// Extract with MiniZinc criteria: solve the dump with `criteria` appended, decode
/// the last solution, and report the objective on the term by solving again with the
/// term fixed.
pub fn extract(
    g: &Graph,
    rung: RungKind,
    criteria: &str,
    cmd: &OpbCommand,
) -> Result<MznOutcome, String> {
    fits_minizinc(g, cmd)?;
    let ix = index(g, rung);
    let model = format!("{}\n% The criteria.\n{criteria}\n", dump(g, rung));
    let (sols, optimum, unsat, bound) = minizinc(cmd, &model, false)?;
    let Some(last) = sols.last() else {
        let status = if unsat {
            Status::Infeasible
        } else {
            Status::Bounded
        };
        return Ok(MznOutcome {
            term: None,
            cost: None,
            status,
            bound,
        });
    };
    let term = decode(g, &ix, &sol(last));
    if term.order(g).is_err() {
        return Err(
            "a MiniZinc solution with a cyclic selection: the rank constraints are wrong".into(),
        );
    }
    let cost = cost_of(g, rung, criteria, &term, cmd)?;
    let status = if optimum {
        Status::Proved
    } else {
        Status::Bounded
    };
    Ok(MznOutcome {
        term: Some(term),
        cost: Some(cost),
        status,
        bound,
    })
}
