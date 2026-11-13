// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Replay check of explanations: every step an explanation cites must follow
//! from the program's own facts and the explanation's other steps.
//!
//! The checker runs each fixture of `tests/egg` with proofs on and, for every
//! e-node, takes `explain_deep(node, find(node))`. It then replays the steps in
//! a fresh union-find over node ids, accepting a step only when its premises
//! already hold there:
//!
//! - `Axiom`: the step joins exactly the two terms of the `union` command it
//!   names;
//! - `Assumption`: a leaf, accepted as given;
//! - `Congruence`: the two nodes share an operator, and their original
//!   children agree position by position (ordered operators) or as sets of
//!   classes (commutative, AC and ACI operators) in the replay union-find;
//! - `Rewrite`: every premise pair recorded for the rule instance is already
//!   joined;
//! - a completion step: counted as not replayable, because the step does not
//!   record the rules and law instances it used.
//!
//! An explanation passes when every step is accepted and the replay joins the
//! node with its representative. A step that is never accepted means the
//! explanation dropped a fact the equality depends on, the defect class of
//! Z3 issue 11649.

use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::interpret::Interpreter;
use semi_persistent_egraph::model::{MachineLit, MachineModel};
use semi_persistent_egraph::nodes::DefaultConfig;
use semi_persistent_egraph::union_find::{Justification, ProofBuf};

type Interp = Interpreter<DefaultConfig, MachineLit, MachineModel, true, true>;

/// Nodes explained per fixture: explanations are quadratic in the worst case,
/// and the first nodes of a fixture already reach every kind of step it makes.
const NODES_PER_FIXTURE: usize = 4_000;

fn run(path: &std::path::Path) -> Option<Interp> {
    let src = std::fs::read_to_string(path).ok()?;
    let cmds = semi_persistent_egraph::parser::parse_program_v2(&src).ok()?;
    let mut interp = Interp::new(MachineModel);
    // The completion node budget a fixture states for itself, as `egg_tests.rs`
    // applies it.
    for line in src.lines() {
        if let Some(n) = line.strip_prefix(";; NODE_BUDGET:") {
            interp
                .eg
                .set_completion_node_budget(n.trim().parse().expect("NODE_BUDGET"));
        }
    }
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .ok()?;
    let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        interp.run_checked(&checked).is_ok()
    }))
    .unwrap_or_else(|_| {
        eprintln!("panicked: {}", path.display());
        false
    });
    ok.then_some(interp)
}

struct Uf(Vec<usize>);

impl Uf {
    fn new(n: usize) -> Self {
        Uf((0..n).collect())
    }
    fn find(&mut self, mut x: usize) -> usize {
        while self.0[x] != x {
            self.0[x] = self.0[self.0[x]];
            x = self.0[x];
        }
        x
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        self.0[ra] = rb;
    }
}

#[derive(Default, Debug)]
struct Tally {
    fixtures: usize,
    skipped: usize,
    explanations: usize,
    steps: std::collections::BTreeMap<&'static str, usize>,
    not_replayable: std::collections::BTreeMap<&'static str, usize>,
    rejected: Vec<String>,
}

fn kind(j: &Justification<ENodeId>) -> &'static str {
    match j {
        Justification::Filler => "filler",
        Justification::Rewrite { .. } => "rewrite",
        Justification::Congruence { .. } => "congruence",
        Justification::Axiom { .. } => "axiom",
        Justification::ACSuperposition { .. } => "ac-superposition",
        Justification::ACInterReduction { .. } => "ac-inter-reduction",
        Justification::ACAxiomCP { .. } => "ac-axiom-cp",
        Justification::Cancellative { .. } => "cancellative",
        Justification::InverseCancel { .. } => "inverse-cancel",
        Justification::Assumption { .. } => "assumption",
        Justification::Normalize { .. } => "normalize",
        Justification::Build { .. } => "build",
    }
}

/// Whether `id`'s operator takes its children in order.
fn ordered(interp: &Interp, id: ENodeId) -> bool {
    use semi_persistent_egraph::typed_routing::NodeRef;
    matches!(
        interp.eg.node_ref(id),
        NodeRef::Plain1(_)
            | NodeRef::Plain2(_)
            | NodeRef::Plain3(_)
            | NodeRef::PlainN(_)
            | NodeRef::Seq(_)
    )
}

/// The replay classes of `id`'s original children after the operator's laws
/// that remove children: a child in the unit's class is dropped, and a child
/// cancels against an inverse child whose argument is in its class. Returned
/// with repetitions, sorted.
fn law_classes(interp: &Interp, uf: &mut Uf, id: ENodeId) -> Vec<usize> {
    let op = interp.eg.node_op(id);
    let children = interp.eg.original_children(id);
    law_classes_of(interp, uf, op, &children)
}

/// `id`'s stored children, each repeated as often as its multiplicity, capped at
/// four: enough for the repetition a nilpotent or idempotent law contracts.
fn counted_children(interp: &Interp, id: ENodeId) -> Vec<ENodeId> {
    let mut out = Vec::new();
    interp.eg.for_each_child(id, |c, m| {
        use semi_persistent_egraph::multiplicity::MultiplicityLike;
        for _ in 0..m.to_usize().min(4) {
            out.push(c);
        }
    });
    out
}

/// `law_classes` over an explicit child list of operator `op`.
fn law_classes_of(interp: &Interp, uf: &mut Uf, op: OpId, children: &[ENodeId]) -> Vec<usize> {
    let unit = interp.eg.unit_node(op).map(|u| uf.find(u.to_usize()));
    let inv = interp.eg.inverse_op(op);
    let mut classes: Vec<usize> = Vec::new();
    // (argument class, the inverse child's own class)
    let mut inverted: Vec<(usize, usize)> = Vec::new();
    for &c in children {
        if inv == Some(interp.eg.node_op(c))
            && let Some(&x) = interp.eg.original_children(c).first()
        {
            inverted.push((uf.find(x.to_usize()), uf.find(c.to_usize())));
            continue;
        }
        // A child whose class holds an inverse node, as far as the replay has
        // joined them.
        if let Some(inv) = inv {
            let k = uf.find(c.to_usize());
            let held = (0..interp.eg.node_count()).find_map(|i| {
                let n = ENodeId::new(i as u32);
                (interp.eg.node_op(n) == inv && uf.find(i) == k)
                    .then(|| interp.eg.original_children(n).first().copied())
                    .flatten()
            });
            if let Some(x) = held {
                inverted.push((uf.find(x.to_usize()), k));
                continue;
            }
        }
        let k = uf.find(c.to_usize());
        if Some(k) != unit {
            classes.push(k);
        }
    }
    // An inverse child with no partner in its argument's class is an
    // ordinary child.
    for (x, own) in inverted {
        match classes.iter().position(|&k| k == x) {
            Some(p) => {
                classes.swap_remove(p);
            }
            None if Some(own) != unit => classes.push(own),
            None => {}
        }
    }
    classes.sort_unstable();
    classes
}

/// Replay one explanation; `Err` names the first step never accepted.
fn replay(
    interp: &Interp,
    node: ENodeId,
    rep: ENodeId,
    steps: &[(ENodeId, ENodeId, Justification<ENodeId>)],
    tally: &mut Tally,
) -> Result<(), String> {
    let n = interp.eg.node_count();
    let mut uf = Uf::new(n);
    let mut accepted = vec![false; steps.len()];
    loop {
        let mut progress = false;
        for (i, &(from, to, j)) in steps.iter().enumerate() {
            if accepted[i] {
                continue;
            }
            let ok = match j {
                Justification::Filler => false,
                Justification::Assumption { .. } => true,
                Justification::Axiom { .. } => {
                    let info = interp
                        .eg
                        .axioms()
                        .info(j.axiom_id().expect("an axiom step"));
                    (info.lhs, info.rhs) == (from, to) || (info.lhs, info.rhs) == (to, from)
                }
                Justification::Congruence { node_a, node_b } => {
                    interp.eg.node_op(node_a) == interp.eg.node_op(node_b) && {
                        let ca = interp.eg.original_children(node_a);
                        let cb = interp.eg.original_children(node_b);
                        if ordered(interp, node_a) {
                            ca.len() == cb.len()
                                && ca
                                    .iter()
                                    .zip(&cb)
                                    .all(|(x, y)| uf.find(x.to_usize()) == uf.find(y.to_usize()))
                        } else {
                            let mut sa = law_classes(interp, &mut uf, node_a);
                            let mut sb = law_classes(interp, &mut uf, node_b);
                            sa.dedup();
                            sb.dedup();
                            sa == sb
                        }
                    }
                }
                Justification::Build { node, .. } => {
                    let other = if from == node { to } else { from };
                    let splices = interp.eg.build_premises(j).unwrap_or(&[]);
                    splices
                        .iter()
                        .all(|&(g, m)| uf.find(g.to_usize()) == uf.find(m.to_usize()))
                        && {
                            // The given children, each spliced child replaced in place by
                            // the spliced node's children.
                            let mut list = counted_children(interp, node);
                            for &(g, m) in splices {
                                let kg = uf.find(g.to_usize());
                                if let Some(p) =
                                    list.iter().position(|&c| uf.find(c.to_usize()) == kg)
                                {
                                    // The children the build spliced: the node's
                                    // original ones, which later merges leave in
                                    // its history.
                                    let kids = if interp.eg.node_has_history_pub(m) {
                                        interp.eg.original_children(m)
                                    } else {
                                        counted_children(interp, m)
                                    };
                                    list.splice(p..p + 1, kids);
                                }
                            }
                            let op = interp.eg.node_op(node);
                            let collapsed = interp.eg.build_collapsed(j) != Some(false);
                            if ordered(interp, node) && !collapsed {
                                let target = interp.eg.original_children(other);
                                list.len() == target.len()
                                    && list.iter().zip(&target).all(|(x, y)| {
                                        uf.find(x.to_usize()) == uf.find(y.to_usize())
                                    })
                            } else {
                                let got = law_classes_of(interp, &mut uf, op, &list);
                                let mut target = if !collapsed {
                                    law_classes(interp, &mut uf, other)
                                } else {
                                    let unit =
                                        interp.eg.unit_node(op).map(|u| uf.find(u.to_usize()));
                                    let k = uf.find(other.to_usize());
                                    if Some(k) == unit { vec![] } else { vec![k] }
                                };
                                target.dedup();
                                let mut g2 = got.clone();
                                g2.dedup();
                                g2 == target
                                    || got.iter().all(|&k| {
                                        target.contains(&k)
                                            || got.iter().filter(|&&x| x == k).count() >= 2
                                    })
                            }
                        }
                }
                Justification::Normalize { node, normal } => {
                    // Every class left after the unit and the inverse pairs is the normal
                    // form's class, or repeats (an idempotent or nilpotent contraction).
                    let classes = law_classes(interp, &mut uf, node);
                    let target = uf.find(normal.to_usize());
                    classes
                        .iter()
                        .all(|&k| k == target || classes.iter().filter(|&&x| x == k).count() >= 2)
                }
                Justification::Rewrite { .. } => match interp.eg.rewrite_premises(j) {
                    Some(premises) => premises
                        .iter()
                        .all(|&(x, y)| uf.find(x.to_usize()) == uf.find(y.to_usize())),
                    None => {
                        let why = match j {
                            Justification::Rewrite { inst, .. }
                                if inst == semi_persistent_egraph::union_find::NO_INSTANCE =>
                            {
                                "rewrite-no-instance"
                            }
                            _ => "rewrite-partial-instance",
                        };
                        *tally.not_replayable.entry(why).or_default() += 1;
                        true
                    }
                },
                // A completion step: its recorded premises (the rules and inverse
                // nodes it used) must hold. The checker does not re-derive the AC
                // normal forms from them; it checks that none is missing.
                other => match interp.eg.step_premises(from, to) {
                    Some(premises) => premises
                        .iter()
                        .all(|&(x, y)| uf.find(x.to_usize()) == uf.find(y.to_usize())),
                    None => {
                        *tally.not_replayable.entry(kind(&other)).or_default() += 1;
                        true
                    }
                },
            };
            if ok {
                accepted[i] = true;
                uf.union(from.to_usize(), to.to_usize());
                progress = true;
            }
        }
        if !progress {
            break;
        }
    }
    if let Some(i) = accepted.iter().position(|a| !a) {
        let (from, to, j) = steps[i];
        // `PROOF_REPLAY_DEBUG=1`: print the rejected step's nodes as the replay sees them.
        if std::env::var("PROOF_REPLAY_DEBUG").is_ok() {
            let show = |uf: &mut Uf, n: ENodeId| {
                let kids: Vec<String> = interp
                    .eg
                    .original_children(n)
                    .iter()
                    .map(|c| format!("{}@{}", c.to_usize(), uf.find(c.to_usize())))
                    .collect();
                format!(
                    "{} {} class {} kids [{}]",
                    n.to_usize(),
                    interp.eg.node_op_name(n),
                    uf.find(n.to_usize()),
                    kids.join(" ")
                )
            };
            eprintln!("REJECT {:?}", j);
            for (k, &(f, t, jj)) in steps.iter().enumerate() {
                eprintln!(
                    "  step {k} {} -> {} {:?} accepted {}",
                    f.to_usize(),
                    t.to_usize(),
                    jj,
                    accepted[k]
                );
            }
            eprintln!("  from {}", show(&mut uf, from));
            eprintln!("  to   {}", show(&mut uf, to));
            if let Some(sp) = interp.eg.build_premises(j) {
                for &(g, m) in sp {
                    eprintln!("  splice {} -> {}", show(&mut uf, g), show(&mut uf, m));
                }
            }
            if let Justification::Congruence { node_a, node_b } = j {
                eprintln!("  a {}", show(&mut uf, node_a));
                eprintln!("  b {}", show(&mut uf, node_b));
            }
        }
        return Err(format!(
            "step {} -> {} ({:?}) has a premise no other step establishes",
            from.to_usize(),
            to.to_usize(),
            j
        ));
    }
    if uf.find(node.to_usize()) != uf.find(rep.to_usize()) {
        return Err("the accepted steps do not join the node with its representative".into());
    }
    Ok(())
}

fn check_fixture(path: &std::path::Path, tally: &mut Tally) {
    let Some(mut interp) = run(path) else {
        tally.skipped += 1;
        return;
    };
    tally.fixtures += 1;
    interp.eg.rebuild();
    let mut buf = ProofBuf::new();
    let count = interp.eg.node_count().min(NODES_PER_FIXTURE);
    for i in 0..count {
        let node = ENodeId::new(i as u32);
        let rep = interp.eg.find(node);
        if rep == node {
            continue;
        }
        buf.steps.clear();
        assert!(interp.eg.explain_deep(node, rep, &mut buf));
        tally.explanations += 1;
        for (_, _, j) in &buf.steps {
            *tally.steps.entry(kind(j)).or_default() += 1;
        }
        let steps = buf.steps.clone();
        if let Err(e) = replay(&interp, node, rep, &steps, tally) {
            tally.rejected.push(format!(
                "{}: node {} = {}: {e}",
                path.file_name().unwrap().to_string_lossy(),
                i,
                rep.to_usize()
            ));
        }
    }
}

/// Wall-clock bound for one fixture's run and replay, in a debug build.
const FIXTURE_SECONDS: u64 = 120;
/// Resident-memory bound for one fixture's child process, in MiB.
const FIXTURE_MIB: u64 = 4_096;

/// Resident memory of process `pid` in MiB, read with `ps`; `None` once it
/// has exited.
fn rss_mib(pid: u32) -> Option<u64> {
    let out = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output()
        .ok()?;
    String::from_utf8_lossy(&out.stdout)
        .trim()
        .parse::<u64>()
        .ok()
        .map(|kib| kib / 1024)
}

/// Child entry: with `PROOF_REPLAY_FIXTURE` set, run and replay that one
/// fixture and print its tally as `REPLAY` lines for the parent. Without it,
/// it does nothing, so a plain `cargo test` run passes through it.
#[test]
fn replay_one_fixture() {
    let Ok(path) = std::env::var("PROOF_REPLAY_FIXTURE") else {
        return;
    };
    let mut tally = Tally::default();
    check_fixture(std::path::Path::new(&path), &mut tally);
    println!("REPLAY ran {} skipped {}", tally.fixtures, tally.skipped);
    println!("REPLAY explanations {}", tally.explanations);
    for (k, n) in &tally.steps {
        println!("REPLAY step {k} {n}");
    }
    for (k, n) in &tally.not_replayable {
        println!("REPLAY unreplayable {k} {n}");
    }
    for r in &tally.rejected {
        println!("REPLAY rejected {r}");
    }
}

/// Every explanation over the fixtures replays. Each fixture runs in a child
/// process (this test binary, filtered to `replay_one_fixture`) under a
/// wall-clock and a memory bound, so a fixture that diverges with proofs on
/// is reported as diverged instead of hanging the suite or exhausting
/// memory. Steps the checker cannot replay are counted and printed, not
/// accepted silently.
#[test]
fn explanations_replay_over_fixtures() {
    let mut paths: Vec<_> = std::fs::read_dir("tests/egg")
        .expect("tests/egg")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "egg"))
        .collect();
    paths.sort();
    // `PROOF_REPLAY_ONLY=name` restricts the run to fixtures whose file name
    // contains `name`, for investigating one rejection.
    if let Ok(only) = std::env::var("PROOF_REPLAY_ONLY") {
        paths.retain(|p| p.to_string_lossy().contains(&only));
    }
    let exe = std::env::current_exe().expect("test binary");
    let mut tally = Tally::default();
    let mut diverged: Vec<String> = Vec::new();
    // The child's output goes to a file: a pipe left unread until the child
    // exits would block a child that prints more than the pipe holds, and the
    // block would read as divergence.
    let out_path = std::env::temp_dir().join(format!("proof_replay_{}.out", std::process::id()));
    for p in &paths {
        let out_file = std::fs::File::create(&out_path).expect("child output file");
        let mut child = std::process::Command::new(&exe)
            .args([
                "--exact",
                "replay_one_fixture",
                "--nocapture",
                "--test-threads=1",
            ])
            .env("PROOF_REPLAY_FIXTURE", p)
            .stdout(out_file)
            .stderr(std::process::Stdio::null())
            .spawn()
            .expect("spawn fixture child");
        let start = std::time::Instant::now();
        let bound = loop {
            if child.try_wait().expect("wait").is_some() {
                break None;
            }
            if start.elapsed().as_secs() > FIXTURE_SECONDS {
                break Some(format!("over {FIXTURE_SECONDS} s"));
            }
            if rss_mib(child.id()).is_some_and(|m| m > FIXTURE_MIB) {
                break Some(format!("over {FIXTURE_MIB} MiB"));
            }
            std::thread::sleep(std::time::Duration::from_millis(200));
        };
        let name = p.file_name().unwrap().to_string_lossy().into_owned();
        if let Some(why) = bound {
            let _ = child.kill();
            let _ = child.wait();
            diverged.push(format!("{name}: {why}"));
            continue;
        }
        let out = std::fs::read_to_string(&out_path).unwrap_or_default();
        for line in out.lines() {
            // libtest prints `test replay_one_fixture ... ` before the first line,
            // without a newline.
            let Some(at) = line.find("REPLAY ") else {
                continue;
            };
            let rest = &line[at + "REPLAY ".len()..];
            let w: Vec<&str> = rest.splitn(3, ' ').collect();
            match w.as_slice() {
                ["ran", n, rest] => {
                    tally.fixtures += n.parse::<usize>().unwrap();
                    tally.skipped += rest
                        .trim_start_matches("skipped ")
                        .parse::<usize>()
                        .unwrap();
                }
                ["explanations", n] => tally.explanations += n.parse::<usize>().unwrap(),
                ["step", k, n] => {
                    *tally.steps.entry(leak(k)).or_default() += n.parse::<usize>().unwrap()
                }
                ["unreplayable", k, n] => {
                    *tally.not_replayable.entry(leak(k)).or_default() += n.parse::<usize>().unwrap()
                }
                ["rejected", ..] => tally
                    .rejected
                    .push(rest.trim_start_matches("rejected ").to_string()),
                _ => {}
            }
        }
    }
    let _ = std::fs::remove_file(&out_path);
    eprintln!(
        "fixtures run {} (skipped {}), explanations {}",
        tally.fixtures, tally.skipped, tally.explanations
    );
    eprintln!("steps by justification: {:?}", tally.steps);
    eprintln!("steps not replayable: {:?}", tally.not_replayable);
    for d in &diverged {
        eprintln!("diverged with proofs on: {d}");
    }
    for r in tally.rejected.iter().take(40) {
        eprintln!("rejected: {r}");
    }
    assert!(
        diverged.is_empty(),
        "{} fixtures exceed their bound with proofs on",
        diverged.len()
    );
    assert!(
        tally.rejected.is_empty(),
        "{} explanations dropped a premise",
        tally.rejected.len()
    );
}

/// A tally key read back from a child: the kind names are a small fixed set.
fn leak(s: &str) -> &'static str {
    Box::leak(s.to_string().into_boxed_str())
}

/// Run `src` with proofs on; the run must succeed.
fn run_src(src: &str) -> Interp {
    let cmds = semi_persistent_egraph::parser::parse_program_v2(src).expect("parse");
    let mut interp = Interp::new(MachineModel);
    let mut globals = semi_persistent_egraph::resolve::GlobalCtx::new();
    let checked = semi_persistent_egraph::sortcheck::sortcheck_program(
        cmds,
        &mut interp.eg,
        &interp.model,
        &mut globals,
    )
    .expect("sortcheck");
    interp.run_checked(&checked).expect("run");
    interp.eg.rebuild();
    interp
}

/// The node of the term `(op children...)` as the program built it.
fn term(interp: &mut Interp, op: &str, children: &[ENodeId]) -> ENodeId {
    let op = interp.eg.ops().id_by_name(op).expect(op);
    interp.eg.add(op, children)
}

/// The node a `let` bound: the term as the program built it.
fn global(interp: &mut Interp, name: &str) -> ENodeId {
    interp.globals().get(name).expect(name).2
}

/// `a` and `b` are one class, their deep explanation replays, and it cites
/// the program's `union` command: the one fact the equality depends on.
fn assert_cites_union(interp: &Interp, a: ENodeId, b: ENodeId, what: &str) {
    assert_eq!(
        interp.eg.find_const(a),
        interp.eg.find_const(b),
        "{what}: classes differ"
    );
    let mut buf = ProofBuf::new();
    assert!(
        interp.eg.explain_deep(a, b, &mut buf),
        "{what}: no explanation"
    );
    assert!(
        buf.steps
            .iter()
            .any(|(_, _, j)| matches!(j, Justification::Axiom { .. })),
        "{what}: the explanation drops the union it depends on: {:?}",
        buf.steps
    );
    let mut tally = Tally::default();
    replay(interp, a, interp.eg.find_const(a), &buf.steps, &mut tally)
        .and_then(|()| replay(interp, b, interp.eg.find_const(b), &buf.steps, &mut tally))
        .unwrap_or_else(|e| panic!("{what}: {e}"));
}

/// A rule applied to a node that matches its pattern only through a `union`:
/// `(F (B))` matches `F(A)` after `A = B`. The `Rewrite` step's instance
/// records that `F(A)`'s child must equal `B`, so the explanation of
/// `F(A) = H` cites the union. Before, the step named only the rule.
#[test]
fn rewrite_instance_cites_the_union_its_match_used() {
    let mut interp = run_src(
        "(datatype T (A) (B) (F T) (H))
         (let fa (F (A))) (let h (H))
         (union (A) (B))
         (rewrite (F (B)) (H))
         (run 3)",
    );
    let a = term(&mut interp, "A", &[]);
    let fa = term(&mut interp, "F", &[a]);
    let h = term(&mut interp, "H", &[]);
    assert_cites_union(&interp, fa, h, "F(A) = H");
}

/// AC congruence between `+(a, b)` and `+(a, a)` after `a = b`: pairing one
/// child per class matched `a` with `a` and never explained `a = b`.
#[test]
fn ac_congruence_with_a_repeated_child_cites_the_union() {
    let mut interp = run_src(
        "(sort E)
         (constructor Add (E) E :assoc :comm)
         (constructor a () E) (constructor b () E)
         (let s (Add (a) (b))) (let t (Add (a) (a)))
         (union (a) (b))",
    );
    let (s, t) = (global(&mut interp, "s"), global(&mut interp, "t"));
    assert_cites_union(&interp, s, t, "+(a, b) = +(a, a)");
}

/// ACI congruence between `or(a, b, c)` and `or(a, c)` after `a = b`: `b` had
/// no partner on the other side and was skipped.
#[test]
fn aci_congruence_with_an_absorbed_child_cites_the_union() {
    let mut interp = run_src(
        "(sort E)
         (function Or (E) E :assoc-comm-idem)
         (function a () E) (function b () E) (function c () E)
         (let s (Or (a) (b) (c))) (let t (Or (a) (c)))
         (union (a) (b))",
    );
    let (s, t) = (global(&mut interp, "s"), global(&mut interp, "t"));
    assert_cites_union(&interp, s, t, "or(a, b, c) = or(a, c)");
}

/// `+(x, y)` collapses to `x` once `y` joins the unit's class. The merge was
/// recorded as a congruence step between `+(x, y)` and `x`, whose premises
/// (the children of `x`) are empty, so `y = 0` was never cited. It is now a
/// `Normalize` step whose premises include the child in the unit's class.
#[test]
fn identity_collapse_cites_the_union_with_the_unit() {
    let mut interp = run_src(
        "(sort E)
         (constructor Zero () E)
         (constructor Add (E) E :assoc :comm :identity (Zero))
         (constructor x () E) (constructor y () E)
         (let s (Add (x) (y)))
         (union (y) (Zero))",
    );
    let x = term(&mut interp, "x", &[]);
    let s = global(&mut interp, "s");
    assert_cites_union(&interp, s, x, "+(x, y) = x");
}

/// `xor(a, b)` collapses to the unit once `a = b` (nilpotent of order 2).
#[test]
fn nilpotent_collapse_cites_the_union() {
    let mut interp = run_src(
        "(sort E)
         (constructor Zero () E)
         (constructor Xor (E) E :assoc :comm :nilpotent 2 :identity (Zero))
         (constructor a () E) (constructor b () E)
         (let s (Xor (a) (b)))
         (union (a) (b))",
    );
    let s = global(&mut interp, "s");
    let zero = term(&mut interp, "Zero", &[]);
    assert_cites_union(&interp, s, zero, "xor(a, b) = 0");
}

/// A program with more `union` commands than a 15-bit axiom id can name runs
/// with proofs on, and the last union's explanation cites its own axiom.
/// Every `union` registers an axiom under proofs; the id was 15-bit, so the
/// 32,768th union exhausted the id space.
#[test]
fn proofs_hold_more_than_32767_unions() {
    let n: usize = 40_000;
    let mut src = String::from("(datatype T (K i64))\n");
    for i in 0..n {
        src.push_str(&format!("(union (K {}) (K {}))\n", 2 * i, 2 * i + 1));
    }
    src.push_str(&format!(
        "(let x (K {})) (let y (K {}))\n",
        2 * n - 2,
        2 * n - 1
    ));
    let mut interp = run_src(&src);
    assert_eq!(interp.eg.axioms().len(), n);
    let (x, y) = (global(&mut interp, "x"), global(&mut interp, "y"));
    let mut buf = ProofBuf::new();
    assert!(interp.eg.explain(x, y, &mut buf));
    assert!(
        buf.steps.iter().any(|(_, _, j)| matches!(
            j,
            Justification::Axiom { axiom_id } if *axiom_id as usize == n - 1
        )),
        "the last union's step: {:?}",
        buf.steps
    );
}

/// An AC term built after a merge hash-conses onto the node of another
/// spelling: `(Add (B) (X))` after `B = C` is stored as `Add{C, X}`'s node.
/// The build keeps the client's term as an evidence node, so the explanation
/// of `Add(B, X) = Add(C, X)` cites the union.
#[test]
fn ac_build_onto_another_spelling_cites_the_union() {
    let mut interp = run_src(
        "(sort E)
         (constructor Add (E) E :assoc :comm)
         (constructor B () E) (constructor C () E) (constructor X () E)
         (let s (Add (C) (X)))
         (union (B) (C))
         (let t (Add (B) (X)))",
    );
    let (s, t) = (global(&mut interp, "s"), global(&mut interp, "t"));
    assert_cites_union(&interp, t, s, "Add(B, X) = Add(C, X)");
}

/// Flattening splices a nested same-operator child by its class's minimal
/// monomial. `A` and `B` are created first, so after `Add(C, D) = Add(A, B)`
/// the class's minimal monomial is `{A, B}`, and `(Add s1 (E))` with
/// `s1 = Add(C, D)` is stored as `Add{A, B, E}`: the splice used the union.
#[test]
fn ac_flatten_splice_cites_the_union() {
    let mut interp = run_src(
        "(sort T)
         (constructor A () T) (constructor B () T) (constructor C () T)
         (constructor D () T) (constructor E () T)
         (constructor Add (T) T :assoc :comm)
         (let s2 (Add (A) (B)))
         (let s1 (Add (C) (D)))
         (union s1 s2)
         (let t (Add s1 (E)))
         (let u (Add (A) (B) (E)))",
    );
    let (t, u) = (global(&mut interp, "t"), global(&mut interp, "u"));
    assert_cites_union(&interp, t, u, "Add(s1, E) = Add(A, B, E)");
}

/// An idempotent law applied at build time returns a child's class: `(Or (A)
/// (B))` after `A = B` is `A`. The explanation cites the union.
#[test]
fn aci_build_collapse_cites_the_union() {
    let mut interp = run_src(
        "(sort E)
         (function Or (E) E :assoc-comm-idem)
         (function A () E) (function B () E)
         (union (A) (B))
         (let t (Or (A) (B)))",
    );
    let t = global(&mut interp, "t");
    let a = term(&mut interp, "A", &[]);
    assert_cites_union(&interp, t, a, "Or(A, B) = A");
}

/// An inverse pair cancels at build time: `(Add (A) (Neg (B)))` after `A = B`
/// is the unit, and the explanation cites the union.
#[test]
fn inverse_build_cancellation_cites_the_union() {
    let mut interp = run_src(
        "(sort E)
         (constructor A () E) (constructor B () E) (constructor Zero () E)
         (constructor Neg (E) E)
         (constructor Add (E) E :assoc :comm :identity (Zero) :inverse Neg)
         (union (A) (B))
         (let t (Add (A) (Neg (B))))",
    );
    let t = global(&mut interp, "t");
    let zero = term(&mut interp, "Zero", &[]);
    assert_cites_union(&interp, t, zero, "Add(A, Neg(B)) = 0");
}

/// A completion superposition: the rules `A + B -> P` and `B + C -> Q` overlap
/// on `A + B + C`, and completion merges `P + C` with `A + Q`. The step records
/// the two rules it superposed, so its explanation cites both unions; before,
/// the superposition step was a leaf and cited neither.
#[test]
fn superposition_cites_the_unions_of_its_rules() {
    let mut interp = run_src(
        "(sort E)
         (constructor A () E) (constructor B () E) (constructor C () E)
         (constructor P () E) (constructor Q () E)
         (constructor Add (E) E :assoc :comm)
         (set-option :completion eager)
         (union (Add (A) (B)) (P))
         (union (Add (B) (C)) (Q))
         (let s (Add (P) (C)))
         (let t (Add (A) (Q)))",
    );
    let (s, t) = (global(&mut interp, "s"), global(&mut interp, "t"));
    assert_eq!(
        interp.eg.find_const(s),
        interp.eg.find_const(t),
        "P + C = A + Q"
    );
    let mut buf = ProofBuf::new();
    assert!(interp.eg.explain_deep(s, t, &mut buf));
    let axioms: std::collections::BTreeSet<usize> = buf
        .steps
        .iter()
        .filter_map(|(_, _, j)| match j {
            Justification::Axiom { axiom_id } => Some(*axiom_id as usize),
            _ => None,
        })
        .collect();
    assert_eq!(
        axioms.len(),
        2,
        "the explanation must cite both unions: {:?}",
        buf.steps
    );
    assert!(
        buf.steps
            .iter()
            .any(|(_, _, j)| matches!(j, Justification::ACSuperposition { .. })),
        "the equality comes from the superposition: {:?}",
        buf.steps
    );
    let mut tally = Tally::default();
    replay(&interp, s, interp.eg.find_const(s), &buf.steps, &mut tally)
        .unwrap_or_else(|e| panic!("P + C = A + Q: {e}"));
    assert!(
        tally.not_replayable.is_empty(),
        "every step replays from its recorded premises: {:?}",
        tally.not_replayable
    );
}

/// A match through a flattened view: `t = Add(K, Z)` keeps `K` as a child (a
/// nullary constant's class is atomic, so the build does not splice it), and
/// after `K = Add(A, B)` the `:flatten` rule `(Add (A) (B) x)` matches `t`'s
/// view `{A, B, Z}`. The instance derives `A` and `B` through `K`'s class, so
/// the explanation of `t = H(Z)` cites the union and replays with no partial
/// instance.
#[test]
fn flattened_view_match_cites_the_union() {
    let mut interp = run_src(
        "(sort E)
         (constructor K () E) (constructor Z () E)
         (constructor A () E) (constructor B () E)
         (constructor H (E) E)
         (constructor Add (E) E :assoc :comm)
         (let t (Add (K) (Z)))
         (union (K) (Add (A) (B)))
         (rewrite (Add (A) (B) x) (H x) :flatten)
         (run 2)
         (let h (H (Z)))",
    );
    let (t, h) = (global(&mut interp, "t"), global(&mut interp, "h"));
    assert_cites_union(&interp, t, h, "Add(K, Z) = H(Z)");
    let mut buf = ProofBuf::new();
    assert!(interp.eg.explain_deep(t, h, &mut buf));
    let mut tally = Tally::default();
    replay(&interp, t, interp.eg.find_const(t), &buf.steps, &mut tally)
        .unwrap_or_else(|e| panic!("Add(K, Z) = H(Z): {e}"));
    assert!(
        tally.not_replayable.is_empty(),
        "the view's instance is complete: {:?}",
        tally.not_replayable
    );
}
