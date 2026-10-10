// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Named cost models for `(extract … :cost NAME)`.
//!
//! `(cost-model NAME :script "file.roto")` compiles a Roto cost script when the
//! program is checked, so a type error in the script, a polarity error included, is
//! a program error before anything runs. `(cost-model NAME :rust "id")` names a cost
//! registered in Rust. Extraction under a named model hands the e-graph to
//! [`crate::extraction`], which lowers the cost to CNF or OPB, solves, breaks cycles, and
//! reports the interpreted cost of the term it returns.

/// `--cost-bits 32|64|big`: the range a cost model's values and costs must lie in,
/// signed (`crate::extraction::CostWidth`). A value outside is a reported error.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum CostBits {
    W32,
    W64,
    #[default]
    Big,
}

impl CostBits {
    /// `32`, `64`, or `big`.
    pub fn parse(s: &str) -> Result<CostBits, String> {
        match s {
            "32" => Ok(CostBits::W32),
            "64" => Ok(CostBits::W64),
            "big" => Ok(CostBits::Big),
            _ => Err(format!("expected '32', '64', or 'big', got '{s}'")),
        }
    }
}

use crate::ast::{CostSource, SolverSpec};
use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::extraction::graph::{Assoc, Graph, Kind, Node, Term, Tree};
use crate::extraction::rung::RungKind;
use crate::extraction::script::{CostModel, Script};
use crate::extraction::solve::{OpbCommand, Solver, Status};
use crate::extraction::{Cost, CostWidth};
use crate::literal::LitVal;
use crate::multiplicity::MultiplicityLike;
use crate::registry::{AssocDir, OpKind};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

/// A compiled cost model, shared by the commands that name it.
#[derive(Clone)]
pub struct Handle(pub Arc<CostModel>);

impl std::fmt::Debug for Handle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("CostModel")
    }
}

/// Costs written in Rust that `:rust` may name.
fn native(id: &str) -> Option<crate::extraction::script::NativeCost> {
    match id {
        "mltl-memory" => Some(|r, b| crate::extraction::mltl_cost::mltl_memory(r, b)),
        "pipeline-registers" => Some(|r, b| crate::extraction::mltl_cost::pipeline_registers(r, b)),
        "monitor-history" => Some(|r, b| crate::extraction::mltl_cost::monitor_history(r, b)),
        _ => None,
    }
}

pub fn compile(source: &CostSource) -> Result<Handle, String> {
    let model = match source {
        CostSource::Script(path) => CostModel::Script(Script::compile(path)?),
        CostSource::Asp(path) => CostModel::Lp(std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?),
        CostSource::MiniZinc(path) => CostModel::Mzn(std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?),
        CostSource::Rust(id) => CostModel::Native(native(id).ok_or_else(|| format!("no Rust cost model named '{id}' (registered: mltl-memory, pipeline-registers, monitor-history)"))?),
    };
    Ok(Handle(Arc::new(model)))
}

/// Whether the model is written in ASP, and so needs an ASP solver.
pub fn is_asp(h: &Handle) -> bool {
    matches!(*h.0, CostModel::Lp(_))
}

/// Whether the model is written in MiniZinc, and so needs a MiniZinc solver.
pub fn is_minizinc(h: &Handle) -> bool {
    matches!(*h.0, CostModel::Mzn(_))
}

pub fn check_rung(rung: &str) -> Result<(), String> {
    RungKind::parse(rung)
        .map(|_| ())
        .ok_or_else(|| format!("unknown rung '{rung}' (selection, levels, splits, binary, orders)"))
}

/// The e-graph reachable from `root` as the library's graph.
///
/// A child whose sort is a value sort becomes payload of its parent, depth
/// first and left to right, so an interval's bounds arrive in order: an integer
/// literal as an int, any other literal as a string. The value sorts are the
/// least set closed under "every node of the sort has only value-sort children",
/// less the root's sort; literal sorts are in it because a literal has no
/// children. A multiset child of multiplicity k is one operand with count k, as in
/// `dump-egraph`, and an AC or ACI node is flat.
///
/// `Err` when a count does not fit the graph's u64 multiplicity (not reachable at the
/// built widths, u32 and u64; `to_u64` is fallible by contract).
pub fn to_graph<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>(
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    root: Cfg::G,
) -> Result<Graph, String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    Ok(to_graph_mapped(eg, root)?.0)
}

/// As [`to_graph`], with the graph node of each e-node that became one.
pub fn to_graph_mapped<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>(
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    root: Cfg::G,
) -> Result<(Graph, BTreeMap<usize, usize>), String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let ids: Vec<Cfg::G> = eg.node_ids().collect();
    // The extraction graph holds a count in u64; refuse a wider one before building.
    for &id in &ids {
        let mut wide = None;
        eg.for_each_child(id, |_, m| {
            if m.to_u64().is_none() {
                wide = Some(m);
            }
        });
        if let Some(m) = wide {
            return Err(format!(
                "multiplicity overflow: the count {m} does not fit the extraction graph's 64-bit count"
            ));
        }
    }
    // A node's children with their counts, as the node stores them: an AC child of
    // multiplicity k is one entry.
    let children = |id: Cfg::G| {
        let mut out: Vec<(Cfg::G, u64)> = Vec::new();
        eg.for_each_child(id, |c, m| {
            out.push((
                eg.class_repr(c),
                m.to_u64().expect("every count fits u64, checked above"),
            ));
        });
        out
    };
    // Classes, their members, and unordered children are taken in content-colour
    // order (`crate::canon_colour`), as `dump-egraph` writes them, so the graph's
    // indices, and with them the extractor's choice among ties, do not depend on ids
    // (`doc/goal-stable-extraction.md`, step 2).
    let colouring = eg.canon_colours();
    let class_key = |c: Cfg::G| {
        let ci = colouring.class_of(eg.class_repr(c));
        (
            ci.and_then(|i| colouring.class_colour.get(i)).copied(),
            ci.and_then(|i| colouring.members.get(i))
                .and_then(|ms| ms.first())
                .map(|id| id.to_usize()),
        )
    };
    let node_key = |id: Cfg::G| {
        let ci = colouring.class_of(eg.class_repr(id));
        ci.and_then(|i| {
            let j = colouring.members.get(i)?.iter().position(|&m| m == id)?;
            colouring.node_colour.get(i)?.get(j).copied()
        })
    };
    let mut members: BTreeMap<usize, Vec<Cfg::G>> = BTreeMap::new();
    for &id in &ids {
        // As in `dump-egraph`: a congruent duplicate is an identical alternative, so it
        // is not offered to the extractor as a separate choice.
        if eg.node_flags(id) & crate::node_types::FLAG_CONGRUENT_DUP != 0 {
            continue;
        }
        members
            .entry(eg.class_repr(id).to_usize())
            .or_default()
            .push(id);
    }
    for v in members.values_mut() {
        // Members in colour order; the id only orders two members of equal colour,
        // which exist only beside symmetric classes (decision 4).
        v.sort_by_key(|&id| (node_key(id), id.to_usize()));
    }
    let mut class_order: Vec<usize> = members.keys().copied().collect();
    class_order.sort_by_key(|&c| {
        let first = members[&c][0];
        (class_key(first), c)
    });
    let sort_of = |id: Cfg::G| eg.node_sort(id).to_usize();
    let root_sort = sort_of(root);
    let mut value: BTreeSet<usize> = BTreeSet::new();
    loop {
        let mut blocked: BTreeSet<usize> = BTreeSet::new();
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        for &id in &ids {
            let s = sort_of(id);
            seen.insert(s);
            if children(id)
                .iter()
                .any(|&(c, _)| !value.contains(&sort_of(c)))
            {
                blocked.insert(s);
            }
        }
        let grown: BTreeSet<usize> = seen
            .difference(&blocked)
            .copied()
            .filter(|&s| s != root_sort)
            .collect();
        if grown == value {
            break;
        }
        value = grown;
    }
    fn gather<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>(
        eg: &EGraph<Cfg, L, TRACK, PROOFS>,
        members: &BTreeMap<usize, Vec<Cfg::G>>,
        class: Cfg::G,
        node: &mut Node,
    ) where
        MSetCanon: VarCanon<Cfg::G, Cfg::C>,
        Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
    {
        let id = members[&class.to_usize()][0];
        if let Some(v) = eg.get_lit_val(id) {
            let t = v.to_string();
            let t = t.trim_matches('"');
            // Any integer literal is a number, exactly: one past `i64` (an `IBig` or
            // `UBig` literal) used to arrive as a string.
            match Cost::parse(t) {
                Some(i) => node.ints.push(i),
                None => node.strings.push(t.to_owned()),
            }
            return;
        }
        let mut kids = Vec::new();
        eg.for_each_child(id, |c, _| kids.push(eg.class_repr(c)));
        for k in kids {
            gather(eg, members, k, node);
        }
    }

    let mut class_ix: BTreeMap<usize, usize> = BTreeMap::new();
    let mut classes: Vec<Vec<usize>> = Vec::new();
    let mut intern = |c: usize, classes: &mut Vec<Vec<usize>>| {
        *class_ix.entry(c).or_insert_with(|| {
            classes.push(Vec::new());
            classes.len() - 1
        })
    };
    let mut nodes = Vec::new();
    let mut mapped = BTreeMap::new();
    for &c in &class_order {
        let ms = &members[&c];
        if value.contains(&sort_of(ms[0])) {
            continue;
        }
        for &id in ms {
            let info = eg.ops().info(eg.node_op(id));
            let mut node = Node {
                op: info.name.clone(),
                ints: Vec::new(),
                strings: Vec::new(),
                children: Vec::new(),
                mults: Vec::new(),
                class: 0,
                kind: match &info.kind {
                    OpKind::Normal { .. } => Kind::Plain,
                    OpKind::Commutative { .. } => Kind::Comm,
                    OpKind::A { dir, .. } => Kind::Seq(match dir {
                        AssocDir::Both => Assoc::Both,
                        AssocDir::Left => Assoc::Left,
                        AssocDir::Right => Assoc::Right,
                    }),
                    OpKind::MSet { .. } => Kind::MSet,
                    OpKind::Set { .. } => Kind::Set,
                    OpKind::Lit => Kind::Plain,
                },
                subsumed: eg.node_flags(id) & crate::node_types::FLAG_SUBSUMED != 0,
            };
            let mut kids = children(id);
            if matches!(
                info.kind,
                OpKind::MSet { .. } | OpKind::Set { .. } | OpKind::Commutative { .. }
            ) {
                kids.sort_by_key(|&(k, _)| class_key(k));
            }
            let multiset = matches!(info.kind, OpKind::MSet { .. });
            for (k, m) in kids {
                if value.contains(&sort_of(k)) {
                    // A value child is payload, read once whatever its count.
                    gather(eg, &members, k, &mut node);
                } else {
                    node.children.push(intern(k.to_usize(), &mut classes));
                    if multiset {
                        node.mults.push(m);
                    }
                }
            }
            node.class = intern(c, &mut classes);
            classes[node.class].push(nodes.len());
            mapped.insert(id.to_usize(), nodes.len());
            nodes.push(node);
        }
    }
    let root = intern(eg.class_repr(root).to_usize(), &mut classes);
    Ok((
        Graph {
            nodes,
            classes,
            root,
        },
        mapped,
    ))
}

/// The additive-greedy term (Semper's `(extract t)`), as a selection of `g`.
fn greedy_term<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>(
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    g: &Graph,
    mapped: &BTreeMap<usize, usize>,
) -> Result<Term, String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let (cost, best) = crate::extract::best_members(eg);
    let mut selection = vec![None; g.classes.len()];
    let mut stack = vec![g.root];
    while let Some(c) = stack.pop() {
        if selection[c].is_some() {
            continue;
        }
        // The greedy member of the e-class behind graph class `c`.
        let any = g.classes[c].first().ok_or("an empty class")?;
        let sid = mapped
            .iter()
            .find(|(_, n)| **n == *any)
            .map(|(s, _)| *s)
            .ok_or("unmapped")?;
        let repr = eg.class_repr(Cfg::G::from_usize(sid)).to_usize();
        if cost[repr] == usize::MAX {
            return Err("no grounded term".into());
        }
        let n = *mapped
            .get(&best[repr].to_usize())
            .ok_or("the greedy member is a value node")?;
        selection[c] = Some(n);
        stack.extend(g.nodes[n].children.iter().copied());
    }
    Ok(Term {
        selection,
        trees: Default::default(),
    })
}

/// Estimated clauses above which a rung steps down: 3M stays well under 8 GB. The
/// hard instances of `doc/goal-stable-extraction.md` need it raised (`:budget`).
const DEFAULT_BUDGET: u64 = 3_000_000;

fn solver(spec: &SolverSpec) -> Solver {
    match spec {
        SolverSpec::Greedy => unreachable!("handled before solving"),
        SolverSpec::Internal => Solver::Internal {
            max_solves: 100_000,
            max_conflicts: None,
        },
        SolverSpec::Dpw => Solver::Dpw {
            max_solves: 100_000,
            max_conflicts: None,
        },
        SolverSpec::RoundingSat => {
            let mut c = OpbCommand::roundingsat().unwrap_or_else(|| {
                OpbCommand::new("roundingsat")
                    .arg("--print-sol=1")
                    .arg("--verbosity=0")
            });
            c.timeout = std::time::Duration::from_secs(3600);
            Solver::Opb(c)
        }
        SolverSpec::Opb(cmd) => Solver::Opb(OpbCommand {
            program: cmd[0].clone(),
            args: cmd[1..].to_vec(),
            timeout: std::time::Duration::from_secs(3600),
            proof_dir: None,
        }),
        SolverSpec::MiniZinc(cmd) => {
            let mut c = OpbCommand::new("minizinc").arg("--solver").arg(&cmd[0]);
            c.args.extend(cmd[1..].iter().cloned());
            Solver::MiniZinc(c)
        }
        SolverSpec::Asp(cmd) => Solver::Asp(OpbCommand {
            program: cmd[0].clone(),
            args: cmd[1..].to_vec(),
            timeout: std::time::Duration::from_secs(3600),
            proof_dir: None,
        }),
    }
}

fn render(g: &Graph, term: &Term, c: usize, tree: Option<(&Tree, &[usize])>) -> String {
    let n = term.selection[c].expect("a class of the term");
    let node = &g.nodes[n];
    // An AC, ACI, or commutative node's operands print sorted by their own text: an
    // order fixed by content, as the export's is, and readable
    // (`doc/goal-stable-extraction.md`, the user's choice of 2026-10-02).
    let unordered = matches!(node.kind, Kind::MSet | Kind::Set | Kind::Comm);
    let head = |mut kids: Vec<String>| {
        if unordered {
            kids.sort();
        }
        let mut parts = vec![node.op.clone()];
        parts.extend(node.ints.iter().map(|i| i.to_string()));
        parts.extend(node.strings.iter().map(|s| format!("{s:?}")));
        parts.extend(kids);
        format!("({})", parts.join(" "))
    };
    match (tree, term.trees.get(&n)) {
        // A leaf is an operand with its whole multiplicity, written once as `x:k`.
        (Some((Tree::Node(ts), ops)), _) => head(
            ts.iter()
                .map(|t| {
                    let times = if let Tree::Leaf(i) = t {
                        g.leaf_multiplicity(n, *i)
                    } else {
                        1
                    };
                    counted(render_tree(g, term, c, t, ops), times)
                })
                .collect(),
        ),
        (_, Some(t)) => {
            let ops = g.leaves(n);
            render(g, term, c, Some((t, &ops)))
        }
        _ => head(
            node.children
                .iter()
                .enumerate()
                .map(|(i, &k)| counted(render(g, term, k, None), g.leaf_multiplicity(n, i)))
                .collect(),
        ),
    }
}

/// An operand written once with its multiplicity, `x:k`, as Semper reads it back.
fn counted(text: String, k: u64) -> String {
    if k == 1 { text } else { format!("{text}:{k}") }
}

fn render_tree(g: &Graph, term: &Term, c: usize, t: &Tree, ops: &[usize]) -> String {
    match t {
        Tree::Leaf(i) => render(g, term, ops[*i], None),
        Tree::Node(_) => render(g, term, c, Some((t, ops))),
    }
}

/// Run `(extract … :cost …)`: print the cost, its status, and the term, and write
/// the term as JSON to `file` if given.
pub fn run<Cfg: EGraphConfig, L: LitVal, const TRACK: bool, const PROOFS: bool>(
    eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    root: Cfg::G,
    model: &Handle,
    rung: &str,
    budget: Option<u64>,
    spec: &SolverSpec,
    file: Option<&str>,
    proof: Option<&str>,
    band: Option<(u64, u64, u64)>,
    bits: CostBits,
) -> Result<(), String>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
    Cfg::Policy: crate::config::StorePolicy<Cfg, TRACK>,
{
    let width = match bits {
        CostBits::W32 => CostWidth::W32,
        CostBits::W64 => CostWidth::W64,
        CostBits::Big => CostWidth::Big,
    };
    let (g, mapped) = to_graph_mapped(eg, root)?;
    let g = Arc::new(g);
    if let SolverSpec::Greedy = spec {
        // The greedy term scored by the cost model, at the selection rung.
        let term = greedy_term(eg, &g, &mapped)?;
        let cost = model
            .0
            .try_cost_of(g.clone(), RungKind::Selection, &term, width)?;
        println!("; cost {cost} greedy at rung selection");
        println!("{}", render(&g, &term, g.root, None));
        if let Some(f) = file {
            let json = term
                .to_json(&g)
                .map_err(|_| "the term is cyclic".to_string())?;
            std::fs::write(f, json).map_err(|e| format!(":file '{f}': {e}"))?;
        }
        return Ok(());
    }
    let asked = RungKind::parse(rung).expect("checked");
    let kind = asked.within(&g, budget.unwrap_or(DEFAULT_BUDGET));
    if kind != asked {
        eprintln!(
            "warning: rung {} estimated above the budget; extracting at {}",
            asked.name(),
            kind.name()
        );
    }
    let rung = kind.name();
    if let Some((lo, hi, count)) = band {
        // The band's bounds are exact: one past every cost is the same band.
        let found = model.0.band(
            g.clone(),
            kind,
            crate::extraction::solve::Band {
                lo: Cost::from(lo),
                hi: Cost::from(hi),
                count: usize::try_from(count).unwrap_or(usize::MAX),
            },
            width,
        )?;
        println!(
            "; {} terms with cost in [{lo}, {hi}] at rung {rung}",
            found.len()
        );
        for (i, (cost, term)) in found.iter().enumerate() {
            println!("; cost {cost} in band at rung {rung}");
            println!("{}", render(&g, term, g.root, None));
            if let Some(f) = file {
                let json = term
                    .to_json(&g)
                    .map_err(|_| "the term is cyclic".to_string())?;
                std::fs::write(format!("{f}.{i}.json"), json)
                    .map_err(|e| format!(":file '{f}': {e}"))?;
            }
        }
        return Ok(());
    }
    let mut solver = solver(spec);
    if let (Solver::Opb(cmd), Some(dir)) = (&mut solver, proof) {
        cmd.proof_dir = Some(dir.into());
    }
    let out = model.0.extract(g.clone(), kind, &solver, width)?;
    for w in &out.warnings {
        eprintln!("warning: {w:?}");
    }
    let (Some(term), Some(cost)) = (out.term, out.cost) else {
        return Err(format!("no term: {:?}", out.status));
    };
    let status = match out.status {
        Status::Proved => "proved",
        Status::Bounded => "bounded",
        Status::Infeasible => "infeasible",
    };
    println!(
        "; cost {cost} {status} at rung {rung} ({} solves, {} cycle exclusions)",
        out.stats.solves, out.stats.cycle_exclusions
    );
    if let Some(c) = &out.certificate {
        println!(
            "; certificate {:?}: veripb {} {}",
            c.claim,
            c.instance.display(),
            c.proof.display()
        );
    }
    if !out.solver_costs.is_empty() {
        if is_minizinc(model) {
            // The MiniZinc solver's lower bound on the objective.
            println!("; solver lower bound {}", out.solver_costs[0]);
        } else {
            // An ASP criteria's objectives: the solver's values, most important first.
            println!(
                "; solver objective {:?} (most important first)",
                out.solver_costs
            );
        }
    }
    println!("{}", render(&g, &term, g.root, None));
    if let Some(f) = file {
        let json = term
            .to_json(&g)
            .map_err(|_| "the term is cyclic".to_string())?;
        std::fs::write(f, json).map_err(|e| format!(":file '{f}': {e}"))?;
    }
    Ok(())
}
