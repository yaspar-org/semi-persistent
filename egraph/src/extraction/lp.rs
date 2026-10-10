// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The e-graph and a rung as an answer-set program, for criteria written in ASP.
//!
//! [`dump`] writes the reachable e-graph as facts and the rung as rules over named
//! predicates; the user's criteria (rules and `#minimize` statements) are appended,
//! and clingo solves the whole. [`extract`] decodes the answer set into a
//! [`Term`] and reports the criteria's value on that term by solving again with the
//! term fixed. The library's CNF encoding is not involved.
//!
//! # Predicates
//!
//! Always (for the classes reachable from the root, and their candidates):
//!
//! | predicate | meaning |
//! | --- | --- |
//! | `class(C)`, `root(C)` | a class; the root |
//! | `node(N,C,Op)` | node `N` of class `C`, operator `Op` (a string) |
//! | `first(C,N)` | `N` is `C`'s first candidate |
//! | `kid(N,I,K)` | child `I` of `N` (from 0) is class `K`; a flat node's children are its distinct operands |
//! | `operand(N,K)` | `K` is a distinct child of `N` |
//! | `mult(N,K,M)` | operand `K` of `N` has multiplicity `M`: its stored count under an AC operator, 1 otherwise |
//! | `int(N,J,V)`, `str(N,J,S)` | integer and string payload `J` of `N` |
//! | `kind(N,K)` | `plain`, `comm`, `seq`, `seq_left`, `seq_right`, `mset`, or `set` |
//! | `leaf(N,P,K)` | leaf `P` of `N`'s tree is class `K`: the distinct operands of an AC node, the positions of a sequence or fold, the distinct operands of any other node |
//! | `used(C)`, `pick(N)` | the class is in the term; the node is its class's choice |
//!
//! At every rung, for every picked node (blocks exist only at the tree rungs, and for
//! folds at every rung):
//!
//! | predicate | meaning |
//! | --- | --- |
//! | `inner(N,B)` | block `B` (an internal node of `N`'s tree) exists |
//! | `bmem(N,G,P)` | leaf `P` lies under `G`, a block or `root` |
//! | `under(N,G,K)` | class `K` lies under `G` |
//! | `parent(N,X,G)` | the innermost block around `X` (a `leaf(P)` or a block) is `G` |
//! | `depth(N,P,D)` | leaf `P` is at depth `D` (1 directly under the root) |
//! | `pos(N,G,X,Q)` | at the orders rung, child `X` of `G` has position `Q` (AC only) |
//!
//! A block is `blk(I,J)`, the interval `I..J` of a sequence's positions, or
//! `blk(R,S)` for an AC node: the block whose least leaf is `R` and whose size is `S`,
//! which names each set of leaves once.

use crate::extraction::graph::{Assoc, ClassId, Graph, Kind, NodeId, Term, Tree};
use crate::extraction::rung::{MAX_ARITY, MAX_ORDERED_ARITY, RungKind};
use crate::extraction::solve::{OpbCommand, Status};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

fn quote(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

/// The leaves of `n` as the dump numbers them.
fn leaves(g: &Graph, n: NodeId) -> Vec<ClassId> {
    match g.nodes[n].kind {
        Kind::Seq(_) => g.nodes[n].children.clone(),
        _ => g.operands(n),
    }
}

/// Whether `n` gets a free tree at `rung`, as the library's rungs decide it.
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

/// The reachable e-graph as facts, and the rung as rules.
pub fn dump(g: &Graph, rung: RungKind) -> String {
    let mut o = String::new();
    let reach = g.reachable();
    let _ = writeln!(o, "% The e-graph.\nroot({}).", g.root);
    for &c in &reach {
        let _ = writeln!(o, "class({c}).");
        if let Some(n) = g.candidates(c).next() {
            let _ = writeln!(o, "first({c},{n}).");
        }
        for n in g.candidates(c) {
            let node = &g.nodes[n];
            let _ = writeln!(o, "node({n},{c},{}).", quote(&node.op));
            let kind = match node.kind {
                Kind::Plain => "plain",
                Kind::Comm => "comm",
                Kind::Seq(Assoc::Both) => "seq",
                Kind::Seq(Assoc::Left) => "seq_left",
                Kind::Seq(Assoc::Right) => "seq_right",
                Kind::MSet => "mset",
                Kind::Set => "set",
            };
            let _ = writeln!(o, "kind({n},{kind}).");
            for (i, &k) in node.children.iter().enumerate() {
                let _ = writeln!(o, "kid({n},{i},{k}).");
            }
            for (i, k) in g.operands(n).into_iter().enumerate() {
                let m = if node.flat() {
                    g.multiplicity(n, i)
                } else {
                    node.children.iter().filter(|&&x| x == k).count() as u64
                };
                let _ = writeln!(o, "operand({n},{k}). mult({n},{k},{m}).");
            }
            for (j, v) in node.ints.iter().enumerate() {
                let _ = writeln!(o, "int({n},{j},{v}).");
            }
            for (j, v) in node.strings.iter().enumerate() {
                let _ = writeln!(o, "str({n},{j},{}).", quote(v));
            }
            let lv = leaves(g, n);
            for (p, &k) in lv.iter().enumerate() {
                let _ = writeln!(o, "leaf({n},{p},{k}).");
            }
            let k = lv.len();
            if free_tree(g, n, rung) {
                let _ = writeln!(o, "arity({n},{k}).");
                if node.kind == Kind::Seq(Assoc::Both) {
                    for i in 0..k {
                        for j in (i + 1)..k {
                            if (i, j) != (0, k - 1) {
                                let _ = writeln!(
                                    o,
                                    "cand({n},blk({i},{j})). span({n},blk({i},{j}),{i},{j})."
                                );
                            }
                        }
                    }
                } else {
                    let _ = writeln!(o, "ac({n}).");
                    for r in 0..k {
                        for s in 2..k {
                            if r + s <= k {
                                let _ = writeln!(
                                    o,
                                    "cand({n},blk({r},{s})). least({n},blk({r},{s}),{r}). size({n},blk({r},{s}),{s})."
                                );
                            }
                        }
                    }
                }
                if rung == RungKind::Orders && node.kind != Kind::Seq(Assoc::Both) {
                    let _ = writeln!(o, "ordered({n}).");
                }
                match rung {
                    RungKind::Levels => {
                        let _ = writeln!(o, "chains({n}).");
                    }
                    RungKind::Binary => {
                        let _ = writeln!(o, "binary({n}).");
                    }
                    _ => {}
                }
            } else if let Some(dir) = node.kind.fold() {
                // A fold's one bracketing: the prefixes, or the suffixes.
                for len in 2..k {
                    let (i, j) = if dir == Assoc::Left {
                        (0, len - 1)
                    } else {
                        (k - len, k - 1)
                    };
                    let _ = writeln!(
                        o,
                        "fixed({n},blk({i},{j})). span({n},blk({i},{j}),{i},{j})."
                    );
                }
            }
        }
    }
    o.push_str(RULES);
    o
}

/// The selection and tree rules, over the facts [`dump`] writes.
const RULES: &str = r#"
% Selection: the root is used, a used class picks one candidate, a picked node uses
% its operands, and a used class is grounded (its term is finite).
used(C) :- root(C).
{ pick(N) : node(N,C,_) } = 1 :- used(C).
used(K) :- pick(N), operand(N,K).
ok(C) :- pick(N), node(N,C,_), ok(K) : operand(N,K).
:- used(C), not ok(C).

% Blocks: free ones at the tree rungs, a fold's fixed ones at every rung.
{ inner(N,B) : cand(N,B) } :- pick(N), arity(N,_).
inner(N,B) :- pick(N), fixed(N,B).
bmem(N,B,P) :- inner(N,B), span(N,B,I,J), leaf(N,P,_), I <= P, P <= J.
bmem(N,B,R) :- inner(N,B), least(N,B,R).
{ bmem(N,B,P) : leaf(N,P,_), P > R } :- inner(N,B), least(N,B,R).
:- inner(N,B), size(N,B,S), #count { P : bmem(N,B,P) } != S.
bmem(N,root,P) :- pick(N), leaf(N,P,_).

% Blocks that meet nest (a laminar family); under chains, blocks also meet.
meet(N,B1,B2) :- inner(N,B1), inner(N,B2), B1 < B2, bmem(N,B1,P), bmem(N,B2,P).
out(N,B1,B2) :- inner(N,B1), inner(N,B2), B1 != B2, bmem(N,B1,P), not bmem(N,B2,P).
:- meet(N,B1,B2), out(N,B1,B2), out(N,B2,B1).
:- chains(N), inner(N,B1), inner(N,B2), B1 < B2, not meet(N,B1,B2).
:- binary(N), arity(N,K), pick(N), #count { B : inner(N,B) } != K - 2.

% The tree: `sub` is strict containment, `parent` the innermost container.
sub(N,B1,B2) :- inner(N,B1), inner(N,B2), B1 != B2, not out(N,B1,B2).
sub(N,B,root) :- inner(N,B).
closer(N,P,G) :- bmem(N,G,P), bmem(N,B,P), sub(N,B,G).
parent(N,leaf(P),G) :- bmem(N,G,P), not closer(N,P,G).
closerb(N,B,G) :- sub(N,B,H), sub(N,H,G).
parent(N,B,G) :- sub(N,B,G), not closerb(N,B,G).
under(N,G,K) :- bmem(N,G,P), leaf(N,P,K).
depth(N,P,D+1) :- pick(N), leaf(N,P,_), D = #count { B : bmem(N,B,P), inner(N,B) }.

% Orders: the children of each block take positions 0 to m - 1.
child(N,G,X) :- parent(N,X,G), ordered(N).
{ pos(N,G,X,Q) : Q = 0..K-1 } = 1 :- child(N,G,X), arity(N,K).
:- pos(N,G,X,Q), pos(N,G,Y,Q), X != Y.
taken(N,G,Q) :- pos(N,G,_,Q).
:- pos(N,G,_,Q), Q > 0, not taken(N,G,Q-1).

#show pick/1.
#show inner/2.
#show bmem/3.
#show pos/4.
"#;

/// The term an answer set denotes: the picked nodes, and each free tree built from
/// its blocks' leaves (ordered by `pos` where the rung has positions).
pub fn decode(g: &Graph, atoms: &[String]) -> Term {
    let mut selection = vec![None; g.classes.len()];
    let mut blocks: BTreeMap<NodeId, BTreeMap<String, BTreeSet<usize>>> = BTreeMap::new();
    let mut pos: BTreeMap<(NodeId, String), usize> = BTreeMap::new();
    let args = |a: &str, name: &str| -> Option<Vec<String>> {
        let inner = a.strip_prefix(name)?.strip_prefix('(')?.strip_suffix(')')?;
        let (mut out, mut depth, mut cur) = (Vec::new(), 0, String::new());
        for ch in inner.chars() {
            match ch {
                '(' => {
                    depth += 1;
                    cur.push(ch);
                }
                ')' => {
                    depth -= 1;
                    cur.push(ch);
                }
                ',' if depth == 0 => out.push(std::mem::take(&mut cur)),
                _ => cur.push(ch),
            }
        }
        out.push(cur);
        Some(out)
    };
    for a in atoms {
        if let Some(v) = args(a, "pick") {
            let n: NodeId = v[0].parse().unwrap();
            selection[g.nodes[n].class] = Some(n);
        } else if let Some(v) = args(a, "bmem") {
            let n: NodeId = v[0].parse().unwrap();
            if v[1] != "root" && !is_fixed(g, n) {
                blocks
                    .entry(n)
                    .or_default()
                    .entry(v[1].clone())
                    .or_default()
                    .insert(v[2].parse().unwrap());
            }
        } else if let Some(v) = args(a, "pos") {
            let n: NodeId = v[0].parse().unwrap();
            pos.insert((n, v[2].clone()), v[3].parse().unwrap());
        }
    }
    let mut trees = BTreeMap::new();
    for (&n, bs) in &blocks {
        let k = leaves(g, n).len();
        let sets: Vec<(String, BTreeSet<usize>)> =
            bs.iter().map(|(b, s)| (b.clone(), s.clone())).collect();
        trees.insert(n, build(n, &sets, &(0..k).collect(), &pos));
    }
    // A free tree with no block is flat: recorded only when positions order it.
    for &(n, _) in pos.keys() {
        trees.entry(n).or_insert_with(|| {
            let k = leaves(g, n).len();
            build(n, &[], &(0..k).collect(), &pos)
        });
    }
    Term { selection, trees }
}

fn is_fixed(g: &Graph, n: NodeId) -> bool {
    g.nodes[n].kind.fold().is_some()
}

/// The tree over `set` from the laminar `blocks`, children in position order, or in
/// order of their least leaf.
fn build(
    n: NodeId,
    blocks: &[(String, BTreeSet<usize>)],
    set: &BTreeSet<usize>,
    pos: &BTreeMap<(NodeId, String), usize>,
) -> Tree {
    let within: Vec<&(String, BTreeSet<usize>)> = blocks
        .iter()
        .filter(|(_, s)| s.is_subset(set) && s != set)
        .collect();
    let maximal: Vec<&(String, BTreeSet<usize>)> = within
        .iter()
        .copied()
        .filter(|(_, s)| !within.iter().any(|(_, t)| t != s && s.is_subset(t)))
        .collect();
    let covered: BTreeSet<usize> = maximal
        .iter()
        .flat_map(|(_, s)| s.iter().copied())
        .collect();
    let mut kids: Vec<(usize, usize, Tree)> = Vec::new();
    for &p in set.iter().filter(|p| !covered.contains(p)) {
        let key = pos.get(&(n, format!("leaf({p})"))).copied().unwrap_or(p);
        kids.push((key, p, Tree::Leaf(p)));
    }
    for (b, s) in maximal {
        let least = *s.iter().next().unwrap();
        let key = pos.get(&(n, b.clone())).copied().unwrap_or(least);
        kids.push((key, least, build(n, blocks, s, pos)));
    }
    kids.sort_by_key(|(k, l, _)| (*k, *l));
    Tree::Node(kids.into_iter().map(|(_, _, t)| t).collect())
}

/// An ASP extraction's outcome: the term, and the criteria's value on it.
#[derive(Debug)]
pub struct LpOutcome {
    pub term: Option<Term>,
    /// The criteria's optimization values on the term, most important first.
    pub costs: Vec<i64>,
    pub status: Status,
}

/// Run clingo on `program`, returning the last witness's atoms, its costs, and
/// whether the optimum was proved.
fn clingo(
    cmd: &OpbCommand,
    program: &str,
) -> Result<(Option<(Vec<String>, Vec<i64>)>, bool, bool), String> {
    let path = crate::extraction::solve::temp_path("lp");
    std::fs::write(&path, program).map_err(|e| e.to_string())?;
    if let Ok(dir) = std::env::var("EXTRACT_API_KEEP_LP") {
        let n = std::fs::read_dir(&dir).map(|d| d.count()).unwrap_or(0);
        let _ = std::fs::copy(
            &path,
            std::path::Path::new(&dir).join(format!("call{n:03}.lp")),
        );
    }
    let out = std::process::Command::new(&cmd.program)
        .args(["--outf=2", "--quiet=1"])
        .args(&cmd.args)
        .arg(&path)
        .output();
    let _ = std::fs::remove_file(&path);
    let out = out.map_err(|e| format!("{}: {e}", cmd.program))?;
    let v: serde_json::Value = serde_json::from_slice(&out.stdout)
        .map_err(|_| format!("clingo: {}", String::from_utf8_lossy(&out.stderr)))?;
    let result = v["Result"].as_str().unwrap_or("");
    let optimum = result == "OPTIMUM FOUND"
        || (result == "SATISFIABLE" && v["Models"]["Optimum"].as_str() == Some("yes"));
    let unsat = result == "UNSATISFIABLE";
    let w = v["Call"]
        .as_array()
        .and_then(|c| c.last())
        .and_then(|c| c["Witnesses"].as_array())
        .and_then(|w| w.last());
    let Some(w) = w else {
        return Ok((None, optimum, unsat));
    };
    let atoms = w["Value"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|a| a.as_str().map(String::from))
        .collect();
    let costs = w["Costs"]
        .as_array()
        .map(|c| c.iter().filter_map(|x| x.as_i64()).collect())
        .unwrap_or_default();
    Ok((Some((atoms, costs)), optimum, unsat))
}

/// Constraints fixing `term` at `rung`, for evaluating criteria on it: every
/// candidate picked exactly when the term picks it, and every tree atom (`inner`, a
/// block's `bmem`, and at the orders rung `pos`) held exactly when the term's tree
/// has it. A picked node with a free tree and no tree in the term is flat.
pub fn fix_term(g: &Graph, rung: RungKind, term: &Term) -> String {
    let mut o = String::new();
    for c in g.reachable() {
        for n in g.candidates(c) {
            let picked = term.selection[c] == Some(n);
            let _ = writeln!(o, "{}pick({n}).", if picked { ":- not " } else { ":- " });
            if !picked || !free_tree(g, n, rung) {
                continue;
            }
            let k = leaves(g, n).len();
            let flat = Tree::Node((0..k).map(Tree::Leaf).collect());
            let tree = term.trees.get(&n).unwrap_or(&flat);
            let seq = g.nodes[n].kind == Kind::Seq(Assoc::Both);
            let ordered = rung == RungKind::Orders && !seq;
            fn members(t: &Tree, out: &mut Vec<usize>) {
                match t {
                    Tree::Leaf(p) => out.push(*p),
                    Tree::Node(ks) => ks.iter().for_each(|x| members(x, out)),
                }
            }
            let name = |t: &Tree| -> String {
                let mut m = Vec::new();
                members(t, &mut m);
                let (lo, hi) = (*m.iter().min().unwrap(), *m.iter().max().unwrap());
                if seq {
                    format!("blk({lo},{hi})")
                } else {
                    format!("blk({lo},{})", m.len())
                }
            };
            fn walk(
                n: NodeId,
                t: &Tree,
                g_name: &str,
                top: bool,
                ordered: bool,
                name: &dyn Fn(&Tree) -> String,
                o: &mut String,
            ) {
                let Tree::Node(ks) = t else { return };
                if !top {
                    let _ = writeln!(o, "held_inner({n},{g_name}).");
                    let mut m = Vec::new();
                    members(t, &mut m);
                    for p in m {
                        let _ = writeln!(o, "held_bmem({n},{g_name},{p}).");
                    }
                }
                for (q, x) in ks.iter().enumerate() {
                    let xn = match x {
                        Tree::Leaf(p) => format!("leaf({p})"),
                        Tree::Node(_) => name(x),
                    };
                    if ordered {
                        let _ = writeln!(o, "held_pos({n},{g_name},{xn},{q}).");
                    }
                    if let Tree::Node(_) = x {
                        walk(n, x, &xn, false, ordered, name, o);
                    }
                }
            }
            walk(n, tree, "root", true, ordered, &name, &mut o);
        }
    }
    o.push_str("free(N) :- arity(N,_).\n");
    o.push_str(
        ":- inner(N,B), free(N), not held_inner(N,B).\n:- held_inner(N,B), not inner(N,B).\n",
    );
    o.push_str(":- bmem(N,B,P), free(N), B != root, not held_bmem(N,B,P).\n:- held_bmem(N,B,P), not bmem(N,B,P).\n");
    o.push_str(
        ":- pos(N,G,X,Q), not held_pos(N,G,X,Q).\n:- held_pos(N,G,X,Q), not pos(N,G,X,Q).\n",
    );
    o.push_str("held_inner(0,none) :- #false.\nheld_bmem(0,none,0) :- #false.\nheld_pos(0,none,none,0) :- #false.\n");
    o
}

/// `Ok` when every integer the dump writes, a payload integer or a multiplicity, is
/// one of clingo's 32-bit integers ([`crate::extraction::asp::clingo_int`]): clingo wraps one past
/// them silently.
pub fn fits_clingo(g: &Graph) -> Result<(), String> {
    fits_clingo_values(g).map_err(|e| format!("{e}. {CRITERIA_OWN_RISK}"))
}

/// Said with every refusal of the ASP and MiniZinc dumps: Semper checks the numbers it
/// writes, not what the criteria compute from them (user, 2026-10-06).
pub const CRITERIA_OWN_RISK: &str = "Semper checks the numbers it writes for the solver; an overflow inside your ASP or MiniZinc criteria is not checked, and is yours to rule out";

fn fits_clingo_values(g: &Graph) -> Result<(), String> {
    use crate::extraction::cost::Cost;
    for &c in &g.reachable() {
        for n in g.candidates(c) {
            for &v in &g.nodes[n].ints {
                crate::extraction::asp::clingo_int(
                    &format!("the integer of node {} ({})", n, g.nodes[n].op),
                    v,
                )?;
            }
            for i in 0..g.operands(n).len() {
                crate::extraction::asp::clingo_int(
                    &format!("a multiplicity of node {} ({})", n, g.nodes[n].op),
                    Cost::from(g.multiplicity(n, i)),
                )?;
            }
        }
    }
    Ok(())
}

/// The criteria's values on `term` at `rung`: the dump and the criteria with the
/// term fixed, solved once.
pub fn cost_of(
    g: &Graph,
    rung: RungKind,
    criteria: &str,
    term: &Term,
    cmd: &OpbCommand,
) -> Result<Vec<i64>, String> {
    fits_clingo(g)?;
    let program = format!(
        "{}\n% The criteria.\n{criteria}\n% The term.\n{}",
        dump(g, rung),
        fix_term(g, rung, term)
    );
    let (w, _, _) = clingo(cmd, &program)?;
    w.map(|(_, c)| c)
        .ok_or_else(|| "the term does not satisfy the criteria".to_string())
}

/// Extract with ASP criteria: solve the dump with `criteria` appended, decode the
/// answer set, and report the criteria's values on the term by solving again with
/// the term fixed.
pub fn extract(
    g: &Graph,
    rung: RungKind,
    criteria: &str,
    cmd: &OpbCommand,
) -> Result<LpOutcome, String> {
    fits_clingo(g)?;
    let program = format!("{}\n% The criteria.\n{criteria}\n", dump(g, rung));
    let (witness, optimum, unsat) = clingo(cmd, &program)?;
    let Some((atoms, _)) = witness else {
        let status = if unsat {
            Status::Infeasible
        } else {
            Status::Bounded
        };
        return Ok(LpOutcome {
            term: None,
            costs: Vec::new(),
            status,
        });
    };
    let term = decode(g, &atoms);
    if term.order(g).is_err() {
        return Err(
            "an answer set with a cyclic selection: the groundedness rules are wrong".into(),
        );
    }
    let costs = cost_of(g, rung, criteria, &term, cmd)?;
    let status = if optimum {
        Status::Proved
    } else {
        Status::Bounded
    };
    Ok(LpOutcome {
        term: Some(term),
        costs,
        status,
    })
}
