// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Where an extraction's size goes: `diagnose DUMP.json [gte|block|solve]`.
//!
//! Reads a Semper `dump-egraph` file (extraction-gym JSON), builds the selection
//! rung and the pipeline-register cost on a CNF target, finds a first model, and
//! then either builds the objective's totalizer at the bound below it (`gte`, the
//! windowed generalized totalizer; `block`, the same construction with each charged
//! integer's thresholds as one sorted leaf) or runs the full extraction (`solve`).
//! Reports clauses and the process's resident size, and stops above 6 GB.
//!
//! A dump of a Herbie program after rewriting, as the programs harness builds it:
//! `PRELUDE + rules/programs.egg + (let e0 TERM) (run 2) (dump-egraph e0 :file F)`
//! with `PRELUDE` and `TERM` from `tools/apps/programs.py` (`programs.translate`).
//! The measurements of 2026-09-27 are in `egraph/doc/design/11-extraction.md`, §11.3.
use semi_persistent_egraph::extraction::Lit;
use semi_persistent_egraph::extraction::cnf::{ClauseSink, VecSink};
use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node};
use semi_persistent_egraph::extraction::oint::Build;
use semi_persistent_egraph::extraction::rung::{Rung, Selection};
use semi_persistent_egraph::extraction::target::CnfTarget;
use semi_persistent_egraph::extraction::{Cost, CostWidth};
use std::collections::BTreeMap;
use std::sync::Arc;

fn rss_mb() -> u64 {
    let out = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output()
        .unwrap();
    String::from_utf8_lossy(&out.stdout)
        .trim()
        .parse::<u64>()
        .unwrap_or(0)
        / 1024
}

fn load(path: &str) -> Graph {
    let v: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let nodes = v["nodes"].as_object().unwrap();
    let is_e = |c: &str| c.starts_with("E-");
    let mut class_ix: BTreeMap<String, usize> = BTreeMap::new();
    for (_, n) in nodes {
        let c = n["eclass"].as_str().unwrap();
        if is_e(c) {
            let len = class_ix.len();
            class_ix.entry(c.to_string()).or_insert(len);
        }
    }
    let mut g = Graph {
        classes: vec![Vec::new(); class_ix.len()],
        ..Default::default()
    };
    for (_, n) in nodes {
        let c = n["eclass"].as_str().unwrap();
        if !is_e(c) {
            continue;
        }
        let children: Vec<usize> = n["children"]
            .as_array()
            .unwrap()
            .iter()
            .map(|k| nodes[k.as_str().unwrap()]["eclass"].as_str().unwrap())
            .filter(|k| is_e(k))
            .map(|k| class_ix[k])
            .collect();
        let op = n["op"].as_str().unwrap().to_string();
        let kind = if op == "Add" || op == "Mul" {
            Kind::MSet
        } else {
            Kind::Plain
        };
        let class = class_ix[c];
        g.classes[class].push(g.nodes.len());
        g.nodes.push(Node {
            op,
            ints: vec![],
            strings: vec![],
            children,
            mults: Vec::new(),
            class,
            kind,
            subsumed: n["subsumed"].as_bool().unwrap_or(false),
        });
    }
    g.root = class_ix[v["root_eclasses"][0].as_str().unwrap()];
    g
}

/// The windowed totalizer with sorted blocks as leaves. A leaf's values are the
/// prefix sums of its weights and its indicator for a value is the block's own
/// threshold literal; the chain clauses that make the block sorted belong to the
/// integer and are already in the formula.
struct BlockSum {
    nodes: Vec<BNode>,
    cap: u64,
    max_step: u64,
    clauses: usize,
}
struct BNode {
    values: Vec<u64>,
    defined: BTreeMap<u64, Lit>,
    kids: Option<(usize, usize)>,
    leaf: Option<Vec<Lit>>,
}
impl BlockSum {
    fn new(blocks: &[(Vec<u64>, Vec<Lit>)], max_bound: u64) -> Self {
        let max_step = blocks
            .iter()
            .flat_map(|(v, _)| v.windows(2).map(|w| w[1] - w[0]).chain(v.first().copied()))
            .max()
            .unwrap_or(0);
        let mut s = BlockSum {
            nodes: Vec::new(),
            cap: max_bound + max_step,
            max_step,
            clauses: 0,
        };
        s.build(blocks);
        s
    }
    fn build(&mut self, blocks: &[(Vec<u64>, Vec<Lit>)]) -> usize {
        if blocks.len() == 1 {
            let (v, l) = &blocks[0];
            self.nodes.push(BNode {
                values: v.clone(),
                defined: BTreeMap::new(),
                kids: None,
                leaf: Some(l.clone()),
            });
            return self.nodes.len() - 1;
        }
        let mid = blocks.len() / 2;
        let (a, b) = (self.build(&blocks[..mid]), self.build(&blocks[mid..]));
        let mut values = Vec::new();
        for &l in std::iter::once(&0).chain(self.nodes[a].values.iter()) {
            for &r in std::iter::once(&0).chain(self.nodes[b].values.iter()) {
                let t = l + r;
                if t > 0 && t <= self.cap {
                    values.push(t);
                }
            }
        }
        values.sort_unstable();
        values.dedup();
        self.nodes.push(BNode {
            values,
            defined: BTreeMap::new(),
            kids: Some((a, b)),
            leaf: None,
        });
        self.nodes.len() - 1
    }
    fn deny_above(&mut self, sink: &mut VecSink, ub: u64) -> Vec<Lit> {
        let root = self.nodes.len() - 1;
        let hi = ub + self.max_step;
        let window: Vec<u64> = self.nodes[root]
            .values
            .iter()
            .copied()
            .filter(|&v| v > ub && v <= hi)
            .collect();
        window
            .into_iter()
            .map(|v| self.define(sink, root, v))
            .collect()
    }
    fn define(&mut self, sink: &mut VecSink, node: usize, v: u64) -> Lit {
        if let Some(&l) = self.nodes[node].defined.get(&v) {
            return l;
        }
        if let Some(lits) = &self.nodes[node].leaf {
            let j = self.nodes[node]
                .values
                .binary_search(&v)
                .expect("a value of the block");
            let l = lits[j];
            self.nodes[node].defined.insert(v, l);
            return l;
        }
        let (a, b) = self.nodes[node].kids.unwrap();
        let mut pairs = Vec::new();
        for &l in &self.nodes[a].values {
            if l > v {
                break;
            }
            let r = v - l;
            if r == 0 || self.nodes[b].values.binary_search(&r).is_ok() {
                pairs.push((l, r));
            }
        }
        if self.nodes[b].values.binary_search(&v).is_ok() {
            pairs.push((0, v));
        }
        let out = Lit::pos(sink.fresh());
        self.nodes[node].defined.insert(v, out);
        for (l, r) in pairs {
            let mut cl = vec![out];
            if l > 0 {
                cl.push(self.define(sink, a, l).not());
            }
            if r > 0 {
                cl.push(self.define(sink, b, r).not());
            }
            sink.clause(&cl);
            self.clauses += 1;
        }
        out
    }
}

fn main() {
    std::thread::spawn(|| {
        loop {
            if rss_mb() > 6000 {
                eprintln!("stopped at {} MB", rss_mb());
                std::process::exit(3);
            }
            std::thread::sleep(std::time::Duration::from_millis(200));
        }
    });
    let path = std::env::args().nth(1).expect("dump path");
    let mode = std::env::args().nth(2).unwrap_or_else(|| "gte".into());
    let g = Arc::new(load(&path));
    let mut t = CnfTarget::default();
    let mut b = Build::new(&mut t);
    let sel = Selection::build(g.clone(), &mut b);
    let at = |b: &Build| b.cnf().unwrap().sink.clauses.len();
    let c0 = at(&b);
    if mode == "parts" {
        let lat = |n: &Node| match n.op.as_str() {
            "Add" | "Neg" => 1,
            "Mul" => 3,
            "Div" => 12,
            "Call1" | "Call2" | "Call3" => 20,
            _ => 0,
        };
        let _ = b.rec_max(&sel, &lat);
        let c1 = at(&b);
        let _ = b.rec_max_down(&sel, &lat);
        let c2 = at(&b);
        eprintln!(
            "  selection {c0}, rec_max {}, rec_max_down {}",
            c1 - c0,
            c2 - c1
        );
        // The rest of pipeline_registers, counted by operation.
        let late = b.rec_max(&sel, &lat);
        let early = b.rec_max_down(&sel, &lat);
        let (mut cmax, mut csub, mut cif, mut parts, mut sub_net) = (0, 0, 0, 0, 0);
        for &c in &sel.reachable {
            let mut peers = Vec::new();
            for &n in sel.parents(c) {
                for (gates, s) in sel.siblings(n, c) {
                    peers.push((gates, late[s].clone().unwrap()));
                }
            }
            parts += peers.len();
            let k0 = at(&b);
            let m = b.max_of(&peers);
            let k1 = at(&b);
            if semi_persistent_egraph::extraction::oint::SumMethod::choose(
                m.values(),
                early[c].as_ref().unwrap().values(),
            ) == semi_persistent_egraph::extraction::oint::SumMethod::Network
            {
                sub_net += 1;
            }
            let w = b.clamp_sub(&m, early[c].as_ref().unwrap());
            let k2 = at(&b);
            b.cost(&w);
            b.cost_if(sel.class(c), 1);
            let k3 = at(&b);
            cmax += k1 - k0;
            csub += k2 - k1;
            cif += k3 - k2;
        }
        eprintln!(
            "  max_of {cmax} over {parts} parts, clamp_sub {csub} ({sub_net} by network), charges {cif}"
        );
        return;
    }
    semi_persistent_egraph::extraction::mltl_cost::pipeline_registers(&sel, &mut b);
    drop(b);
    // A diagnostic over the u64 encodings: this example's objectives fit u64.
    let obj: Vec<(semi_persistent_egraph::extraction::Lit, u64)> = t
        .objective
        .iter()
        .map(|&(l, w)| (l, w.to_u64().expect("a weight in u64")))
        .collect();
    let in_blocks: usize = t.blocks.iter().map(|r| r.len()).sum();
    eprintln!(
        "{path}: {} classes, {} nodes; formula {} clauses; objective {} terms ({} in {} blocks), total weight {}",
        g.classes.len(),
        g.nodes.len(),
        t.sink.clauses.len(),
        obj.len(),
        in_blocks,
        t.blocks.len(),
        obj.iter().map(|&(_, w)| w).sum::<u64>()
    );
    let model = semi_persistent_egraph::extraction::script::CostModel::Native(|r, b| {
        semi_persistent_egraph::extraction::mltl_cost::pipeline_registers(r, b)
    });
    let one = semi_persistent_egraph::extraction::solve::Solver::Internal {
        max_solves: 1,
        max_conflicts: None,
    };
    let first = model
        .extract(
            g.clone(),
            semi_persistent_egraph::extraction::rung::RungKind::Selection,
            &one,
            CostWidth::default(),
        )
        .unwrap()
        .cost
        .unwrap();
    let bound = u64::try_from(first - t.base - Cost::ONE).expect("a bound in u64");
    let t0 = std::time::Instant::now();
    match mode.as_str() {
        "gte" => {
            let mut sink = VecSink::new(t.sink.next_var);
            let mut w =
                semi_persistent_egraph::extraction::totalizer::WindowedSum::new(&obj, bound);
            let _ = w.deny_above(&mut sink, bound);
            eprintln!(
                "  gte   at bound {bound}: {:>10} clauses, {:.1}s, {} MB",
                sink.clauses.len(),
                t0.elapsed().as_secs_f64(),
                rss_mb()
            );
        }
        "block" => {
            let mut blocks: Vec<(Vec<u64>, Vec<Lit>)> = Vec::new();
            let mut covered = vec![false; obj.len()];
            for r in &t.blocks {
                let mut acc = 0;
                let (mut v, mut l) = (Vec::new(), Vec::new());
                for i in r.clone() {
                    acc += obj[i].1;
                    v.push(acc);
                    l.push(obj[i].0);
                    covered[i] = true;
                }
                blocks.push((v, l));
            }
            for (i, &(l, w)) in obj.iter().enumerate() {
                if !covered[i] {
                    blocks.push((vec![w], vec![l]));
                }
            }
            let mut sink = VecSink::new(t.sink.next_var);
            let mut s = BlockSum::new(&blocks, bound);
            let _ = s.deny_above(&mut sink, bound);
            eprintln!(
                "  block at bound {bound}: {:>10} clauses, {:.1}s, {} MB",
                s.clauses,
                t0.elapsed().as_secs_f64(),
                rss_mb()
            );
        }
        _ => {
            let solver = semi_persistent_egraph::extraction::solve::Solver::Internal {
                max_solves: 5000,
                max_conflicts: None,
            };
            let out = model
                .extract(
                    g.clone(),
                    semi_persistent_egraph::extraction::rung::RungKind::Selection,
                    &solver,
                    CostWidth::default(),
                )
                .unwrap();
            eprintln!(
                "  solve: first {first}, cost {:?} {:?}, {} solves, {:.1}s, {} MB",
                out.cost,
                out.status,
                out.stats.solves,
                t0.elapsed().as_secs_f64(),
                rss_mb()
            );
        }
    }
}
