// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The claims of `doc/paper/paper-draft.md` that cited tests of `memdag-extract`, regenerated
//! on the in-process extraction path (`crate::extraction` with the MLTL memory cost of
//! `extraction::mltl_cost`) after that crate was deleted (`doc/goals/goal-stable-extraction.md`,
//! 2026-10-03):
//!
//! - choosing the grouping after the nodes is not optimal (§1);
//! - band extraction returns exactly the terms whose cost lies in the band (§5);
//! - RoundingSat's proof of every optimum is certified by VeriPB (§5);
//! - four costs only ASP states, each against enumeration (§8).
//!
//! The reference cost of a term is the model's own interpretation of it
//! (`CostModel::cost_of`), which evaluates the cost function on the term with no
//! solving; the solver paths are checked against it.

use semi_persistent_egraph::extraction::asp::AspBuild;
use semi_persistent_egraph::extraction::graph::{Graph, Kind, Node, Term};
use semi_persistent_egraph::extraction::rung::{Rung, RungKind, Selection};
use semi_persistent_egraph::extraction::script::CostModel;
use semi_persistent_egraph::extraction::solve::{Band, Claim, OpbCommand, Solver, Status};
use semi_persistent_egraph::extraction::{Cost, CostWidth};
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::sync::Arc;
use std::time::Duration;

/// Whether `program` runs. A test that needs an external solver returns early, saying
/// so, when it is absent: CI installs none of them.
fn installed(program: &str) -> bool {
    let ok = std::process::Command::new(program)
        .arg("--version")
        .output()
        .is_ok();
    if !ok {
        eprintln!("{program} not installed: this test did not run");
    }
    ok
}

const INTERNAL: Solver = Solver::Internal {
    max_solves: 100_000,
    max_conflicts: None,
};

fn memory() -> CostModel {
    CostModel::Native(|r, b| semi_persistent_egraph::extraction::mltl_cost::mltl_memory(r, b))
}

struct Rng(u64);
impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        usize::try_from(self.0 % u64::try_from(n).unwrap_or(1)).unwrap_or(0)
    }
}

/// A random e-graph over the MLTL operators: class 0 is the root, the last two
/// classes hold atoms, and every other class holds one to three nodes whose children
/// lie below it, except for an occasional back edge. A conjunction or disjunction is
/// flat, its operands deduplicated, as Semper's ACI canonization leaves them.
fn random_graph(rng: &mut Rng, classes: usize) -> Graph {
    let mut g = Graph {
        classes: vec![Vec::new(); classes],
        ..Default::default()
    };
    for c in 0..classes {
        let count = 1 + rng.below(if c + 2 >= classes { 2 } else { 3 });
        for _ in 0..count {
            let node = if c + 2 >= classes {
                Node {
                    op: "Var".into(),
                    ints: vec![],
                    strings: vec![format!("a{}", rng.below(3))],
                    children: vec![],
                    mults: Vec::new(),
                    class: c,
                    kind: Kind::Plain,
                    subsumed: false,
                }
            } else {
                let (op, kind, arity, ints) = match rng.below(5) {
                    0 => {
                        let lb = i64::try_from(rng.below(4)).unwrap_or(0);
                        (
                            "Global",
                            Kind::Plain,
                            1,
                            vec![lb, lb + i64::try_from(rng.below(8)).unwrap_or(0)],
                        )
                    }
                    1 => {
                        let lb = i64::try_from(rng.below(4)).unwrap_or(0);
                        (
                            "Future",
                            Kind::Plain,
                            1,
                            vec![lb, lb + i64::try_from(rng.below(8)).unwrap_or(0)],
                        )
                    }
                    2 => ("Not", Kind::Plain, 1, vec![]),
                    3 => ("And", Kind::Set, 2 + rng.below(3), vec![]),
                    _ => ("Or", Kind::Set, 2 + rng.below(2), vec![]),
                };
                let mut children: Vec<usize> = (0..arity)
                    .map(|_| c + 1 + rng.below(classes - c - 1))
                    .collect();
                if rng.below(8) == 0 {
                    children[0] = rng.below(c + 1);
                }
                if kind == Kind::Set {
                    children.sort_unstable();
                    children.dedup();
                }
                Node {
                    op: op.into(),
                    ints: ints
                        .into_iter()
                        .map(semi_persistent_egraph::extraction::Cost::from)
                        .collect(),
                    strings: vec![],
                    children,
                    mults: Vec::new(),
                    class: c,
                    kind,
                    subsumed: false,
                }
            };
            g.classes[c].push(g.nodes.len());
            g.nodes.push(node);
        }
    }
    // A multiset node may draw one class twice: store it as one operand with its count.
    g.coalesce().unwrap();
    g
}

/// Every acyclic term of `g` at the selection rung: one candidate per reachable
/// class, restricted to the classes the root reaches through the choice.
fn terms(g: &Graph) -> Vec<Term> {
    let reach = g.reachable();
    let choices: Vec<Vec<usize>> = reach.iter().map(|&c| g.candidates(c).collect()).collect();
    if choices.iter().any(|c| c.is_empty()) {
        return Vec::new();
    }
    let (mut out, mut seen) = (Vec::new(), BTreeSet::new());
    let mut idx = vec![0usize; reach.len()];
    loop {
        let mut selection = vec![None; g.classes.len()];
        for (i, &c) in reach.iter().enumerate() {
            selection[c] = Some(choices[i][idx[i]]);
        }
        let full = Term {
            selection,
            trees: Default::default(),
        };
        if let Ok(order) = full.order(g) {
            let mut sel = vec![None; g.classes.len()];
            for c in order {
                sel[c] = full.selection[c];
            }
            if seen.insert(sel.clone()) {
                out.push(Term {
                    selection: sel,
                    trees: Default::default(),
                });
            }
        }
        let mut i = 0;
        loop {
            if i == idx.len() {
                return out;
            }
            idx[i] += 1;
            if idx[i] < choices[i].len() {
                break;
            }
            idx[i] = 0;
            i += 1;
        }
    }
}

// ── §1: the grouping chosen after the nodes ─────────────────────────────────────

/// `g` with only `term`'s nodes extractable: every other candidate of a class the
/// term uses is subsumed, so an extraction over it chooses the grouping alone.
fn fixed(g: &Graph, term: &Term) -> Graph {
    let mut h = g.clone();
    for (c, sel) in term.selection.iter().enumerate() {
        if let Some(n) = sel {
            for &m in &g.classes[c] {
                if m != *n {
                    h.nodes[m].subsumed = true;
                }
            }
        }
    }
    h
}

/// An instance where both decisions matter: a flat conjunction over `k` classes (3 to
/// 5), each offering two `Global` candidates over one atom with different intervals,
/// so the selection changes a class's delay and therefore what its siblings are
/// charged, and the conjunction's grouping is free.
fn grouping_instance(rng: &mut Rng) -> Graph {
    let k = 3 + rng.below(3);
    let classes = k + 2;
    let mut g = Graph {
        classes: vec![Vec::new(); classes],
        root: classes - 1,
        ..Default::default()
    };
    let push = |g: &mut Graph,
                op: &str,
                class: usize,
                children: Vec<usize>,
                ints: Vec<i64>,
                strings: Vec<String>,
                kind: Kind| {
        g.classes[class].push(g.nodes.len());
        g.nodes.push(Node {
            op: op.into(),
            ints: ints
                .into_iter()
                .map(semi_persistent_egraph::extraction::Cost::from)
                .collect(),
            strings,
            children,
            mults: Vec::new(),
            class,
            kind,
            subsumed: false,
        });
    };
    push(
        &mut g,
        "Var",
        0,
        vec![],
        vec![],
        vec!["p".into()],
        Kind::Plain,
    );
    for j in 1..=k {
        for _ in 0..2 {
            let ub = i64::try_from(rng.below(40)).unwrap_or(0);
            push(
                &mut g,
                "Global",
                j,
                vec![0],
                vec![0, ub],
                vec![],
                Kind::Plain,
            );
        }
    }
    push(
        &mut g,
        "And",
        classes - 1,
        (1..=k).collect(),
        vec![],
        vec![],
        Kind::Set,
    );
    g
}

/// The best grouping of `term`'s nodes: the `splits` optimum over `g` restricted to
/// them.
fn grouped(model: &CostModel, g: &Arc<Graph>, term: &Term) -> i64 {
    let out = model
        .extract(
            Arc::new(fixed(g, term)),
            RungKind::Splits,
            &INTERNAL,
            CostWidth::default(),
        )
        .unwrap();
    assert_eq!(
        out.status,
        Status::Proved,
        "the grouping of a fixed selection"
    );
    i64::try_from(out.cost.unwrap()).unwrap()
}

/// The sequential pipeline chooses the nodes by the flat cost (the solver's optimum at
/// the selection rung), then the best grouping of those nodes. The joint extraction
/// chooses both at once at the `splits` rung (every unordered tree). Also reported:
/// the sequential pipeline at its most favourable, over every flat optimum
/// (enumerated by band extraction at the optimum), which isolates the ranking
/// inversion from the solver's choice among flat ties.
#[test]
fn choosing_the_grouping_after_the_nodes_is_not_optimal() {
    let model = memory();
    let mut rng = Rng(0x10_1A_7E);
    let (mut instances, mut above, mut above_best, mut worst) = (0usize, 0usize, 0usize, 0.0f64);
    for trial in 0..600 {
        let g = Arc::new(grouping_instance(&mut rng));
        let flat = model
            .extract(
                g.clone(),
                RungKind::Selection,
                &INTERNAL,
                CostWidth::default(),
            )
            .unwrap();
        assert_eq!(flat.status, Status::Proved, "trial {trial}: flat");
        let joint = model
            .extract(g.clone(), RungKind::Splits, &INTERNAL, CostWidth::default())
            .unwrap();
        assert_eq!(joint.status, Status::Proved, "trial {trial}: joint");
        let joint = i64::try_from(joint.cost.unwrap()).unwrap();
        let sequential = grouped(&model, &g, flat.term.as_ref().unwrap());
        let opt = flat.cost.unwrap();
        let best = model
            .band(
                g.clone(),
                RungKind::Selection,
                Band {
                    lo: opt,
                    hi: opt,
                    count: 10_000,
                },
                CostWidth::default(),
            )
            .unwrap()
            .iter()
            .map(|(_, t)| grouped(&model, &g, t))
            .min()
            .unwrap();
        // The joint search ranges over every pair the sequential one does.
        assert!(
            joint <= best && best <= sequential,
            "trial {trial}: {joint} {best} {sequential}"
        );
        instances += 1;
        if sequential > joint {
            above += 1;
            worst = worst.max((sequential - joint) as f64 / joint as f64);
        }
        above_best += (best > joint) as usize;
    }
    let pct = |n: usize| 100.0 * n as f64 / instances as f64;
    eprintln!(
        "{instances} instances: the sequential pipeline is above the joint optimum on {above} ({:.1}%), \
         by up to {:.0}%; over its most favourable flat optimum, on {above_best} ({:.1}%)",
        pct(above),
        100.0 * worst,
        pct(above_best)
    );
    assert_eq!(instances, 600);
    assert!(above > 0, "no instance separates the two pipelines");
}

// ── §5: band extraction ─────────────────────────────────────────────────────────

#[test]
fn band_extraction_returns_exactly_the_terms_in_the_band() {
    let model = memory();
    let mut rng = Rng(0xBA7D);
    let (mut checked, mut returned) = (0, 0);
    for trial in 0..200 {
        let g = Arc::new(random_graph(&mut rng, 5 + trial % 3));
        let scored: Vec<(Cost, Vec<Option<usize>>)> = terms(&g)
            .into_iter()
            .map(|t| {
                (
                    model.cost_of(g.clone(), RungKind::Selection, &t),
                    t.selection,
                )
            })
            .collect();
        let Some(opt) = scored.iter().map(|x| x.0).min() else {
            continue;
        };
        let (lo, hi) = (opt + Cost::from(1), opt + Cost::from(6));
        let want: BTreeSet<(Cost, Vec<Option<usize>>)> = scored
            .into_iter()
            .filter(|(c, _)| *c >= lo && *c <= hi)
            .collect();
        let got: BTreeSet<(Cost, Vec<Option<usize>>)> = model
            .band(
                g.clone(),
                RungKind::Selection,
                Band {
                    lo,
                    hi,
                    count: 10_000,
                },
                CostWidth::default(),
            )
            .unwrap()
            .into_iter()
            .map(|(c, t)| (c, t.selection))
            .collect();
        assert_eq!(got, want, "trial {trial}: band [{lo}, {hi}]");
        checked += 1;
        returned += got.len();
    }
    assert!(checked >= 150, "only {checked} e-graphs had a term");
    eprintln!("{checked} e-graphs: band extraction equals enumeration ({returned} terms in bands)");
}

// ── §5: certified optima ────────────────────────────────────────────────────────

/// An e-graph in the egglog JSON format `dump-egraph` writes, as extraction reads
/// it: a value child (an interval, a string, an integer) becomes payload of its
/// parent, depth first and left to right, and a conjunction or disjunction is flat.
fn load_egglog(text: &str) -> Graph {
    let v: serde_json::Value = serde_json::from_str(text).expect("JSON");
    let nodes = v["nodes"].as_object().expect("nodes");
    let is_value = |id: &str| {
        ["Interval", "String", "i64", "bool"]
            .iter()
            .any(|s| id.contains(s))
    };
    let kids = |id: &str| -> Vec<String> {
        nodes[id]["children"]
            .as_array()
            .map(|a| {
                a.iter()
                    .filter_map(|s| s.as_str().map(String::from))
                    .collect()
            })
            .unwrap_or_default()
    };
    // The payload of a value child, with an explicit stack in place of recursion.
    let gather = |id: &str, ints: &mut Vec<i64>, strings: &mut Vec<String>| {
        let mut stack = vec![id.to_string()];
        while let Some(x) = stack.pop() {
            let ks = kids(&x);
            if ks.is_empty() {
                let t = nodes[&x]["op"]
                    .as_str()
                    .unwrap_or("")
                    .trim_matches('"')
                    .to_string();
                match t.parse::<i64>() {
                    Ok(i) => ints.push(i),
                    Err(_) if t == "true" || t == "false" => {}
                    Err(_) => strings.push(t),
                }
            } else {
                stack.extend(ks.into_iter().rev());
            }
        }
    };
    let mut names: Vec<&String> = nodes.keys().collect();
    names.sort();
    let mut class_ix: std::collections::BTreeMap<String, usize> = Default::default();
    let mut g = Graph::default();
    let mut intern = |name: &str, g: &mut Graph| -> usize {
        *class_ix.entry(name.to_string()).or_insert_with(|| {
            g.classes.push(Vec::new());
            g.classes.len() - 1
        })
    };
    for id in names {
        if is_value(id) {
            continue;
        }
        let body = &nodes[id];
        let op = body["op"].as_str().expect("op").to_string();
        let (mut ints, mut strings, mut children) = (Vec::new(), Vec::new(), Vec::new());
        for k in kids(id) {
            if is_value(&k) {
                gather(&k, &mut ints, &mut strings);
            } else {
                children.push(intern(
                    nodes[&k]["eclass"].as_str().expect("eclass"),
                    &mut g,
                ));
            }
        }
        let class = intern(body["eclass"].as_str().expect("eclass"), &mut g);
        let kind = if op.starts_with("And") || op.starts_with("Or") {
            Kind::MSet
        } else {
            Kind::Plain
        };
        g.classes[class].push(g.nodes.len());
        g.nodes.push(Node {
            op,
            ints: ints
                .into_iter()
                .map(semi_persistent_egraph::extraction::Cost::from)
                .collect(),
            strings,
            children,
            mults: Vec::new(),
            class,
            kind,
            subsumed: body["subsumed"].as_bool().unwrap_or(false),
        });
    }
    let root = v["root_eclasses"][0].as_str().expect("root");
    g.root = intern(root, &mut g);
    g
}

fn tampered(
    cert: &semi_persistent_egraph::extraction::solve::Certificate,
    dir: &std::path::Path,
    f: &dyn Fn(i64, i64) -> (i64, i64),
) -> semi_persistent_egraph::extraction::solve::Certificate {
    let text = std::fs::read_to_string(&cert.proof).unwrap();
    let mut out = String::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("conclusion BOUNDS ") {
            let mut it = rest.splitn(3, ' ');
            let (a, b) = (
                it.next().unwrap().parse().unwrap(),
                it.next().unwrap().parse().unwrap(),
            );
            let (a, b) = f(a, b);
            let _ = writeln!(out, "conclusion BOUNDS {a} {b} {}", it.next().unwrap_or(""));
        } else {
            out.push_str(line);
            out.push('\n');
        }
    }
    let p = dir.join("tampered.pbp");
    std::fs::write(&p, out).unwrap();
    semi_persistent_egraph::extraction::solve::Certificate {
        proof: p,
        ..cert.clone()
    }
}

/// On the 64 monitor instances of `results/portfolio`, the MLTL memory is extracted
/// through RoundingSat with proof logging; VeriPB must verify every final call's
/// proof, its bound must equal the reported cost, and a proof whose conclusion is
/// altered by one must be rejected.
#[test]
#[cfg_attr(
    not(feature = "slow-tests"),
    ignore = "external solvers under a time limit: --features slow-tests"
)]
fn every_optimum_is_certified_by_veripb() {
    let home = std::env::var("HOME").unwrap();
    let veripb = format!("{home}/.local/bin/veripb");
    // E-graph dumps of the MLTL corpus: derived from a third-party benchmark set, so they
    // are not stored in this crate (`doc/goal-one-crate.md`, step 3). `SEMPER_MLTL_RESULTS`
    // names the directory; without it the test says so and passes.
    let Some(dir) = std::env::var_os("SEMPER_MLTL_RESULTS").map(std::path::PathBuf::from) else {
        eprintln!(
            "SEMPER_MLTL_RESULTS is unset: the certification corpus is not in this crate, so this test did not run"
        );
        return;
    };
    let mut names: Vec<_> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("SEMPER_MLTL_RESULTS={dir:?}: {e}"))
        .flatten()
        .map(|e| e.path())
        .collect();
    names.sort();
    let model = memory();
    let work = std::env::temp_dir().join(format!("certified_{}", std::process::id()));
    let (mut certified, mut rejected) = (0, 0);
    let mut crashed: Vec<String> = Vec::new();
    let (mut t_plain, mut t_logged) = (0.0, 0.0);
    for p in names {
        let Ok(text) = std::fs::read_to_string(p.join("egraph.json")) else {
            continue;
        };
        let g = Arc::new(load_egglog(&text));
        let proofs = work.join(p.file_name().unwrap());
        let cmd = OpbCommand {
            program: format!("{home}/.local/bin/roundingsat"),
            args: vec![
                "--print-sol=1".into(),
                "--verbosity=0".into(),
                "--time-limit=60".into(),
            ],
            timeout: Duration::from_secs(120),
            proof_dir: Some(proofs.clone()),
        };
        let plain = OpbCommand {
            proof_dir: None,
            ..cmd.clone()
        };
        // RoundingSat aborts on some valid clause sets (`std::length_error`, reproduced
        // on 58 clauses in `tests/roundingsat_length_error.opb`). Such an instance has
        // no answer to certify; it is listed, with the internal descent's optimum.
        let probe = model
            .extract(
                g.clone(),
                RungKind::Selection,
                &Solver::Opb(OpbCommand {
                    proof_dir: None,
                    ..cmd.clone()
                }),
                CostWidth::default(),
            )
            .unwrap();
        if probe.status == Status::Bounded && probe.cost.is_none() {
            let internal = model
                .extract(
                    g.clone(),
                    RungKind::Selection,
                    &INTERNAL,
                    CostWidth::default(),
                )
                .unwrap();
            assert_eq!(internal.status, Status::Proved, "{}", p.display());
            crashed.push(format!(
                "{} (internal optimum {:?})",
                p.file_name().unwrap().to_string_lossy(),
                internal.cost
            ));
            continue;
        }
        let t0 = std::time::Instant::now();
        let base = model
            .extract(
                g.clone(),
                RungKind::Selection,
                &Solver::Opb(plain),
                CostWidth::default(),
            )
            .unwrap();
        t_plain += t0.elapsed().as_secs_f64();
        let t0 = std::time::Instant::now();
        let out = model
            .extract(
                g.clone(),
                RungKind::Selection,
                &Solver::Opb(cmd),
                CostWidth::default(),
            )
            .unwrap();
        t_logged += t0.elapsed().as_secs_f64();
        assert_eq!(
            base.cost,
            out.cost,
            "{}: logging changed the optimum",
            p.display()
        );
        assert_eq!(out.status, Status::Proved, "{}", p.display());
        let cert = out.certificate.as_ref().expect("a certificate");
        let lower = semi_persistent_egraph::extraction::solve::verify(cert, &veripb)
            .unwrap_or_else(|e| panic!("{}: {e}", p.display()));
        assert_eq!(
            lower,
            out.cost,
            "{}: certified bound against the reported cost",
            p.display()
        );
        certified += 1;
        if let Claim::Bounds { .. } = cert.claim {
            type Perturb<'a> = (&'a str, &'a dyn Fn(i64, i64) -> (i64, i64));
            let better = |a: i64, b: i64| (a, b - 1);
            let higher = |a: i64, b: i64| (a + 1, b);
            let cases: [Perturb<'_>; 2] = [
                ("a better solution", &better),
                ("a higher lower bound", &higher),
            ];
            for (what, f) in cases {
                let bad = tampered(cert, &proofs, f);
                assert!(
                    semi_persistent_egraph::extraction::solve::verify(&bad, &veripb).is_err(),
                    "{}: a proof claiming {what} was accepted",
                    p.display()
                );
                rejected += 1;
            }
        }
    }
    let _ = std::fs::remove_dir_all(&work);
    let overhead = 100.0 * (t_logged - t_plain) / t_plain;
    eprintln!(
        "{certified}/64 certified, {rejected} tampered proofs rejected; logging costs {overhead:.0}% of solve time; \
         RoundingSat aborted on {}: {crashed:?}",
        crashed.len()
    );
    assert_eq!(certified + crashed.len(), 64);
}

// ── §8: costs only ASP states ───────────────────────────────────────────────────

fn bounds(op: &str, ints: &[i64]) -> (i64, i64) {
    match op {
        "Global" | "Future" | "Until" | "Release" if ints.len() >= 2 => {
            (ints[0].max(0), ints[1].max(0))
        }
        _ => (0, 0),
    }
}

/// Facts about the graph and the selection: `sel(n)` when node `n` is chosen,
/// `cls(n, c)`, `child(n, k)` for distinct children, `child_at(n, i, k)` and
/// `arity(n, a)` positionally, `sig(n, s)` for the operator and payload, the interval
/// `ub`/`lb` scaled per scenario, `boolc(c)` for a Boolean constant's class, and
/// `root(c)`.
fn facts(r: &Selection, b: &AspBuild, scale: &[i64]) -> String {
    let g: &Graph = r.graph();
    let mut out = String::new();
    let mut total_ub = 0i64;
    let _ = writeln!(out, "root({}).", g.root);
    for &c in &r.reachable {
        if g.candidates(c)
            .next()
            .is_some_and(|n| g.nodes[n].op == "Bool")
        {
            let _ = writeln!(out, "boolc({c}).");
        }
        for n in g.candidates(c) {
            let node = &g.nodes[n];
            let _ = writeln!(out, "sel({n}) :- {}.", b.atom(r.node(n)));
            let _ = writeln!(out, "cls({n},{c}).");
            let mut seen = Vec::new();
            for (i, &k) in node.children.iter().enumerate() {
                let _ = writeln!(out, "child_at({n},{i},{k}).");
                if !seen.contains(&k) {
                    seen.push(k);
                    let _ = writeln!(out, "child({n},{k}).");
                }
            }
            let _ = writeln!(out, "arity({n},{}).", node.children.len());
            let sig = format!("{}|{:?}|{:?}", node.op, node.ints, node.strings).replace('"', "'");
            let _ = writeln!(out, "sig({n},\"{sig}\").");
            let ints: Vec<i64> = node
                .ints
                .iter()
                .map(|v| v.to_i64().expect("an i64 payload"))
                .collect();
            let (lb, ub) = bounds(&node.op, &ints);
            for (s, k) in scale.iter().enumerate() {
                let _ = writeln!(out, "ub({s},{n},{}). lb({s},{n},{}).", ub * k, lb * k);
            }
            total_ub += ub;
        }
    }
    // A delay of an acyclic term is at most the sum of every bound. Grounding follows
    // every candidate, cycles included, so without the cap the recursive rules would
    // instantiate without end.
    for (s, k) in scale.iter().enumerate() {
        let _ = writeln!(out, "cap({s},{}).", total_ub * k);
    }
    out.push_str(
        "selc(C) :- sel(N), cls(N,C).\n\
         reach(C) :- root(C).\n\
         reach(K) :- reach(C), sel(N), cls(N,C), child(N,K).\n\
         haskid(N) :- child(N,_).\n",
    );
    out
}

/// Memory per scenario `S`: the delays by recursion, then a queue per selected class
/// that is not a Boolean constant, `max(max sibling wpd - own bpd, 0) + 1`, and the
/// specification wrapper's 1. `mem(S, V)` is the total.
const MEMORY: &str = "\
scen(S) :- ub(S,_,_).
wpd(S,C,U+M) :- scen(S), sel(N), cls(N,C), ub(S,N,U), M = #max { V,K : child(N,K), wpd(S,K,V) ; 0,none }, cap(S,X), U+M <= X.
bpd(S,C,L+M) :- scen(S), sel(N), cls(N,C), lb(S,N,L), haskid(N), M = #min { V,K : child(N,K), bpd(S,K,V) }, cap(S,X), L+M <= X.
bpd(S,C,L) :- scen(S), sel(N), cls(N,C), lb(S,N,L), not haskid(N).
peer(S,C,K,W) :- sel(N), child(N,C), child(N,K), C != K, wpd(S,K,W).
mp(S,C,M) :- scen(S), selc(C), M = #max { W,K : peer(S,C,K,W) ; 0,none }.
q(S,C,M-B+1) :- mp(S,C,M), bpd(S,C,B), not boolc(C), M >= B.
q(S,C,1) :- mp(S,C,M), bpd(S,C,B), not boolc(C), M < B.
mem(S,V+1) :- scen(S), V = #sum { Q,C : q(S,C,Q) }.
";

/// Structural equality of chosen subterms, by positive recursion over children
/// position by position; a class is a duplicate when an equal class has a smaller
/// id. The cost is the number of reachable classes that are not.
const DISTINCT: &str = "\
pair(N,M) :- sel(N), sel(M), N != M, sig(N,S), sig(M,S), arity(N,A), arity(M,A).
pre(N,M,0) :- pair(N,M).
pre(N,M,I+1) :- pre(N,M,I), child_at(N,I,K), child_at(M,I,L), same(K,L).
eq(C,D) :- pair(N,M), cls(N,C), cls(M,D), arity(N,A), pre(N,M,A).
same(K,K) :- selc(K).
same(K,L) :- eq(K,L).
dup(C) :- reach(C), reach(D), D < C, same(D,C).
";

fn clingo() -> OpbCommand {
    OpbCommand {
        program: "clingo".into(),
        args: vec!["--time-limit=60".into()],
        timeout: Duration::from_secs(120),
        proof_dir: None,
    }
}

/// Structurally distinct subterms of `t`, children in stored order: each class's text
/// built after its children's, with an explicit stack (post-order).
fn distinct(g: &Graph, t: &Term) -> u64 {
    let mut text: Vec<Option<String>> = vec![None; g.classes.len()];
    let mut stack = vec![(g.root, false)];
    while let Some((c, expanded)) = stack.pop() {
        if text[c].is_some() {
            continue;
        }
        let n = &g.nodes[t.selection[c].expect("a class of the term")];
        if !expanded {
            stack.push((c, true));
            stack.extend(
                n.children
                    .iter()
                    .filter(|&&k| text[k].is_none())
                    .map(|&k| (k, false)),
            );
            continue;
        }
        let kids: Vec<String> = n
            .children
            .iter()
            .map(|&k| text[k].clone().unwrap_or_default())
            .collect();
        text[c] = Some(format!(
            "({}|{:?}|{:?} {})",
            n.op,
            n.ints,
            n.strings,
            kids.join(" ")
        ));
    }
    let set: BTreeSet<&String> = text.iter().flatten().collect();
    set.len() as u64
}

fn size(t: &Term) -> u64 {
    t.selection.iter().filter(|s| s.is_some()).count() as u64
}

fn scaled(g: &Graph, k: i64) -> Graph {
    let mut h = g.clone();
    for n in &mut h.nodes {
        for x in &mut n.ints {
            *x = *x * semi_persistent_egraph::extraction::Cost::from(k);
        }
    }
    h
}

fn flat_memory(g: &Arc<Graph>, t: &Term) -> u64 {
    u64::try_from(memory().cost_of(g.clone(), RungKind::Selection, t)).unwrap_or(u64::MAX)
}

type Score<'a> = &'a dyn Fn(&Arc<Graph>, &Term) -> Vec<u64>;

fn check_asp(
    name: &str,
    cases: &[Graph],
    cost: &dyn Fn(&Selection, &mut AspBuild),
    score: Score<'_>,
) {
    let mut checked = 0;
    for (i, g) in cases.iter().enumerate() {
        let g = Arc::new(g.clone());
        let all = terms(&g);
        if all.is_empty() {
            continue;
        }
        let want = all.iter().map(|t| score(&g, t)).min().unwrap();
        let (out, stats) = semi_persistent_egraph::extraction::solve::extract_asp(
            g.clone(),
            |s, _| s,
            |r: &Selection, b: &mut AspBuild| cost(r, b),
            &clingo(),
        )
        .unwrap();
        assert_eq!(out.status, Status::Proved, "{name} {i}");
        let got: Vec<u64> = stats
            .costs
            .iter()
            .map(|&c| u64::try_from(c).unwrap_or(u64::MAX))
            .collect();
        assert_eq!(got, want, "{name} {i}: clingo optimum against enumeration");
        assert_eq!(
            score(&g, out.term.as_ref().unwrap()),
            want,
            "{name} {i}: the returned term"
        );
        checked += 1;
    }
    assert!(
        checked * 4 >= cases.len() * 3,
        "{name}: only {checked} of {}",
        cases.len()
    );
    eprintln!("{name}: {checked} e-graphs equal enumeration");
}

fn random_cases() -> Vec<Graph> {
    let mut rng = Rng(0xA5B);
    (0..200)
        .map(|t| random_graph(&mut rng, 5 + t % 3))
        .collect()
}

#[test]
#[cfg_attr(
    not(feature = "slow-tests"),
    ignore = "external solver under a time limit: --features slow-tests"
)]
fn asp_memory_by_recursive_rules() {
    if !installed("clingo") {
        return;
    }
    check_asp(
        "memory by rules",
        &random_cases(),
        &|r, b| {
            let f = facts(r, b, &[1]);
            b.rules(&f);
            b.rules(MEMORY);
            b.minimize("V@1 : mem(0,V)");
        },
        &|g, t| vec![flat_memory(g, t)],
    );
}

#[test]
#[cfg_attr(
    not(feature = "slow-tests"),
    ignore = "external solver under a time limit: --features slow-tests"
)]
fn asp_distinct_subterm_counting() {
    if !installed("clingo") {
        return;
    }
    check_asp(
        "distinct subterms",
        &random_cases(),
        &|r, b| {
            let f = facts(r, b, &[1]);
            b.rules(&f);
            b.rules(DISTINCT);
            b.minimize("1@1,C : reach(C), not dup(C)");
        },
        &|g, t| vec![distinct(g, t)],
    );
}

#[test]
#[cfg_attr(
    not(feature = "slow-tests"),
    ignore = "external solver under a time limit: --features slow-tests"
)]
fn asp_lexicographic_memory_then_size() {
    if !installed("clingo") {
        return;
    }
    check_asp(
        "memory then size",
        &random_cases(),
        &|r, b| {
            let f = facts(r, b, &[1]);
            b.rules(&f);
            b.rules(MEMORY);
            b.minimize("V@2 : mem(0,V)");
            b.minimize("1@1,C : reach(C)");
        },
        &|g, t| vec![flat_memory(g, t), size(t)],
    );
}

/// A conjunction of `k` atoms, each under one of two `Global` candidates of random
/// intervals: the instances on which the scenario scaling changes the answer.
fn instance(rng: &mut Rng, k: usize) -> Graph {
    let classes = 2 * k + 1;
    let mut g = Graph {
        classes: vec![Vec::new(); classes],
        root: classes - 1,
        ..Default::default()
    };
    let push = |g: &mut Graph,
                op: &str,
                class: usize,
                children: Vec<usize>,
                ints: Vec<i64>,
                strings: Vec<String>,
                kind: Kind| {
        g.classes[class].push(g.nodes.len());
        g.nodes.push(Node {
            op: op.into(),
            ints: ints
                .into_iter()
                .map(semi_persistent_egraph::extraction::Cost::from)
                .collect(),
            strings,
            children,
            mults: Vec::new(),
            class,
            kind,
            subsumed: false,
        });
    };
    for j in 0..k {
        push(
            &mut g,
            "Var",
            j,
            vec![],
            vec![],
            vec![format!("p{j}")],
            Kind::Plain,
        );
    }
    for j in 0..k {
        for _ in 0..2 {
            let lb = i64::try_from(rng.below(6)).unwrap_or(0);
            let ub = lb + i64::try_from(rng.below(30)).unwrap_or(0);
            push(
                &mut g,
                "Global",
                k + j,
                vec![j],
                vec![lb, ub],
                vec![],
                Kind::Plain,
            );
        }
    }
    push(
        &mut g,
        "And",
        classes - 1,
        (k..2 * k).collect(),
        vec![],
        vec![],
        Kind::Set,
    );
    g
}

#[test]
#[cfg_attr(
    not(feature = "slow-tests"),
    ignore = "external solver under a time limit: --features slow-tests"
)]
fn asp_worst_case_over_two_scenarios() {
    if !installed("clingo") {
        return;
    }
    static SCALE: [i64; 2] = [1, 3];
    let mut rng = Rng(0xE7E7);
    let cases: Vec<Graph> = (0..120).map(|t| instance(&mut rng, 3 + t % 3)).collect();
    check_asp(
        "worst case",
        &cases,
        &|r, b| {
            let f = facts(r, b, &SCALE);
            b.rules(&f);
            b.rules(MEMORY);
            b.rules("worst(W) :- W = #max { V,S : mem(S,V) }.");
            b.minimize("W@1 : worst(W)");
        },
        &|g, t| {
            vec![
                SCALE
                    .iter()
                    .map(|&k| flat_memory(&Arc::new(scaled(g, k)), t))
                    .max()
                    .unwrap(),
            ]
        },
    );
}
