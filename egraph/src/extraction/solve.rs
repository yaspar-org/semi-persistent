// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Solving: the internal CNF descent or a third-party OPB solver, with cycle
//! breaking done here for both.
//!
//! Both loops decode each model into a term, exclude it if its selection is cyclic,
//! and score it by interpreting the recorded cost expression on the term. That
//! value, not the solver's objective, is what the outcome reports. A one-directional
//! encoding lets a model's objective exceed the term's true cost, and interpretation
//! is what removes the slack.

use crate::extraction::Lit;
use crate::extraction::cnf::VecSink;
use crate::extraction::cost::Cost;
use crate::extraction::graph::{Graph, Term};
use crate::extraction::oint::{Build, Warning};
use crate::extraction::rung::{Rung, Selection};
use crate::extraction::target::{Cmp, CnfTarget, OpbTarget};
use crate::extraction::totalizer::WindowedSum;
use cadical_sys::{CaDiCal, Status as SatStatus};
use std::collections::BTreeMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

/// Which solver.
#[derive(Clone, Debug)]
pub enum Solver {
    /// CNF, one incremental CaDiCaL descent bounded by the windowed totalizer.
    /// `max_conflicts` limits each solve; a solve that reaches it ends the descent
    /// with the incumbent as an upper bound. A conflict count, unlike a time
    /// limit, gives the same outcome on every run.
    Internal {
        max_solves: usize,
        max_conflicts: Option<i32>,
    },
    /// The same descent with the objective bounded by rustsat's dynamic polynomial
    /// watchdog (Paxian, Reimer, and Becker, SAT 2018), whose size does not grow with
    /// the bound as the totalizer's does: for objectives whose totalizer would not fit.
    Dpw {
        max_solves: usize,
        max_conflicts: Option<i32>,
    },
    /// Native OPB, handed to an installed pseudo-Boolean competition solver.
    Opb(OpbCommand),
    /// An answer-set program, handed to clingo (or a solver with its JSON output).
    Asp(OpbCommand),
    /// A MiniZinc model, handed to `minizinc` with the solver its arguments name:
    /// for cost models written in MiniZinc (`crate::mzn`) only.
    MiniZinc(OpbCommand),
}

/// A command-line OPB solver: the file path is appended to `args`.
#[derive(Clone, Debug)]
pub struct OpbCommand {
    pub program: String,
    pub args: Vec<String>,
    pub timeout: Duration,
    /// Keep a proof of every call in this directory: the solver is given
    /// `--proof-log=FILE` (RoundingSat's flag), and the outcome's certificate names
    /// the last call's instance and proof.
    pub proof_dir: Option<std::path::PathBuf>,
}

/// The integers a solver reads correctly. Measured on the inputs in
/// `tests/data/solver_width/` (2026-10-06), not taken from documentation: RoundingSat is
/// exact at 2^70 and 2^100; clasp reads 2^70 as 0 and clingo 3e9 as -1294967296, with no
/// error; Chuffed picks a 2^40 term over one of cost 5; COIN-BC cannot tell 2^53 + 1 from
/// 2^53. A value outside the range is refused before the solver runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolverRange {
    /// Arbitrary precision (RoundingSat).
    Unbounded,
    /// Signed 64-bit (CP-SAT, and any solver not measured).
    I64,
    /// Integers held in doubles, exact up to 2^53 (the MIP solvers behind MiniZinc).
    Exact53,
    /// Signed 32-bit (clasp, clingo, Chuffed, Gecode).
    I32,
}

impl SolverRange {
    pub fn contains(self, v: Cost) -> bool {
        match self {
            SolverRange::Unbounded => true,
            SolverRange::I64 => v.to_i64().is_some(),
            SolverRange::Exact53 => v.abs() <= Cost::from(1i64 << 53),
            SolverRange::I32 => v.to_i64().is_some_and(|x| i32::try_from(x).is_ok()),
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            SolverRange::Unbounded => "arbitrary-precision",
            SolverRange::I64 => "64-bit",
            SolverRange::Exact53 => "double-precision (exact to 2^53)",
            SolverRange::I32 => "32-bit",
        }
    }

    /// `Ok`, or an error naming the solver, its range, and `what`.
    pub fn check(self, solver: &str, what: &str, v: Cost) -> Result<(), String> {
        if self.contains(v) {
            Ok(())
        } else {
            Err(format!(
                "{what} {v} is outside {solver}'s {} integers; it would be read wrongly, not refused",
                self.name()
            ))
        }
    }
}

impl OpbCommand {
    /// The solver's name, the program's file name.
    pub fn solver_name(&self) -> String {
        std::path::Path::new(&self.program)
            .file_name()
            .map(|f| f.to_string_lossy().to_string())
            .unwrap_or_else(|| self.program.clone())
    }

    /// The range of this command as an OPB solver: RoundingSat is exact at any size, clasp
    /// is 32-bit, and any other solver is taken as 64-bit.
    pub fn opb_range(&self) -> SolverRange {
        let name = self.solver_name().to_lowercase();
        if name.contains("roundingsat") {
            SolverRange::Unbounded
        } else if name.contains("clasp") || name.contains("clingo") {
            SolverRange::I32
        } else {
            SolverRange::I64
        }
    }

    /// The range of the MiniZinc solver this command names with `--solver`: Chuffed and
    /// Gecode are 32-bit, the MIP solvers compute in doubles, and CP-SAT (and any other)
    /// is 64-bit, which is also the MiniZinc compiler's own range.
    pub fn mzn_range(&self) -> SolverRange {
        let solver = self
            .args
            .iter()
            .position(|a| a == "--solver")
            .and_then(|i| self.args.get(i + 1))
            .map(|s| s.to_lowercase())
            .unwrap_or_default();
        if solver.contains("chuffed") || solver.contains("gecode") {
            SolverRange::I32
        } else if [
            "coin", "cbc", "highs", "scip", "gurobi", "cplex", "xpress", "mip",
        ]
        .iter()
        .any(|m| solver.contains(m))
        {
            SolverRange::Exact53
        } else {
            SolverRange::I64
        }
    }

    /// RoundingSat (Elffers and Nordström), found as `$ROUNDINGSAT`, as
    /// `~/.local/bin/roundingsat`, or on the `PATH`, printing its solution; `None`
    /// when it is not installed.
    pub fn roundingsat() -> Option<Self> {
        let home = std::env::var("HOME").unwrap_or_default();
        let candidates = [
            std::env::var("ROUNDINGSAT").unwrap_or_default(),
            format!("{home}/.local/bin/roundingsat"),
            "roundingsat".to_string(),
        ];
        let program = candidates
            .into_iter()
            .filter(|p| !p.is_empty())
            .find(|p| std::process::Command::new(p).arg("--help").output().is_ok())?;
        Some(
            OpbCommand::new(&program)
                .arg("--print-sol=1")
                .arg("--verbosity=0"),
        )
    }

    pub fn new(program: &str) -> Self {
        OpbCommand {
            program: program.into(),
            args: Vec::new(),
            timeout: Duration::from_secs(60),
            proof_dir: None,
        }
    }
    pub fn arg(mut self, a: &str) -> Self {
        self.args.push(a.into());
        self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    /// The final solve was unsatisfiable below the incumbent.
    Proved,
    /// A budget ran out; the incumbent is an upper bound.
    Bounded,
    /// No term exists.
    Infeasible,
}

#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub solves: usize,
    pub cycle_exclusions: usize,
    pub no_goods: usize,
    pub solver_calls: usize,
    pub clauses: usize,
    pub vars: u32,
}

#[derive(Clone, Debug)]
pub struct Outcome {
    pub term: Option<Term>,
    /// The interpreted cost of `term`.
    pub cost: Option<Cost>,
    pub status: Status,
    pub warnings: Vec<Warning>,
    pub stats: Stats,
    /// The solver's optimization values, most important first, when an ASP
    /// extension objective was stated: its value is the solver's to report.
    pub solver_costs: Vec<i64>,
    /// A proof of the final call, when the solver was asked for one.
    pub certificate: Option<Certificate>,
}

/// A pseudo-Boolean proof of the last solver call, for VeriPB.
///
/// What it certifies is the solver's reasoning on the final instance, which is the
/// problem plus the cycle exclusions and the incumbent bound the loop added. With
/// `Bounds`, no model of that instance has objective below `lower`; with `Unsat`, no
/// model has objective below `below`. That every acyclic term has a model whose
/// objective is its cost is the encoding's property, established by the tests of
/// the rungs and operators, not by the certificate.
#[derive(Clone, Debug)]
pub struct Certificate {
    pub instance: std::path::PathBuf,
    pub proof: std::path::PathBuf,
    pub claim: Claim,
    /// The objective's constant, which the OPB file does not carry.
    pub base: Cost,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Claim {
    /// The solver's optimum: objective (without the base) at least `lower`.
    Bounds { lower: Cost },
    /// Unsatisfiable: no model with objective (with the base) below `below`, or no
    /// model at all when `None`.
    Unsat { below: Option<Cost> },
}

/// Check a certificate with VeriPB, and that it proves the claim: `Ok` with the
/// lower bound it establishes on the cost, base included.
pub fn verify(cert: &Certificate, veripb: &str) -> Result<Option<Cost>, String> {
    let out = std::process::Command::new(veripb)
        .arg(&cert.instance)
        .arg(&cert.proof)
        .output()
        .map_err(|e| format!("{veripb}: {e}"))?;
    let text =
        String::from_utf8_lossy(&out.stdout).to_string() + &String::from_utf8_lossy(&out.stderr);
    let line = text
        .lines()
        .find(|l| l.starts_with("s VERIFIED"))
        .ok_or_else(|| format!("not verified:\n{text}"))?;
    match cert.claim {
        Claim::Bounds { lower } => {
            // `s VERIFIED BOUNDS a <= obj <= b`
            let a = line
                .split_whitespace()
                .nth(3)
                .and_then(Cost::parse)
                .ok_or_else(|| format!("unexpected: {line}"))?;
            if a < lower {
                return Err(format!(
                    "the proof establishes {a}, not the claimed {lower}"
                ));
            }
            Ok(Some(a + cert.base))
        }
        Claim::Unsat { below } => {
            if !line.contains("UNSAT") && !line.contains("BOUNDS INF") {
                return Err(format!("expected unsatisfiability: {line}"));
            }
            Ok(below)
        }
    }
}

/// The interpreted cost of `term`: rung literals from the term, recursive
/// attributes from the term, everything else from the model. `Err` when the cost is
/// outside the build's width.
pub fn interpret<R: Rung + ?Sized>(
    b: &crate::extraction::oint::Detached,
    rung: &R,
    term: &Term,
    model: &dyn Fn(u32) -> bool,
) -> Result<Cost, String> {
    let canonical = rung.canonical(term);
    let ext = b.rec_values(rung.graph(), term);
    b.objective_value(
        &|v| canonical.get(&v).copied().unwrap_or_else(|| model(v)),
        &|s| ext[s],
    )
}

/// The true value of `x` on `term`: its expression evaluated with the rung's
/// literals fixed by the term, the recursive attributes computed on the term, and
/// any other literal (a free integer's thresholds, say) read from `model`.
pub fn value_on<P: crate::extraction::oint::Polarity, R: Rung + ?Sized>(
    b: &crate::extraction::oint::Detached,
    rung: &R,
    term: &Term,
    x: &crate::extraction::oint::OInt<P>,
    model: &dyn Fn(u32) -> bool,
) -> Cost {
    let canonical = rung.canonical(term);
    let ext = b.rec_values(rung.graph(), term);
    b.eval(
        x,
        &|v| canonical.get(&v).copied().unwrap_or_else(|| model(v)),
        &|s| ext[s],
    )
}

/// A problem already lowered to a target, ready to solve.
pub enum Prepared {
    Cnf(CnfTarget),
    Opb(OpbTarget),
    Asp(crate::extraction::asp::AspTarget),
}

impl Prepared {
    /// The target a solver needs.
    pub fn for_solver(solver: &Solver) -> Prepared {
        match solver {
            Solver::Internal { .. } | Solver::Dpw { .. } | Solver::MiniZinc(_) => {
                Prepared::Cnf(CnfTarget::default())
            }
            Solver::Opb(_) => Prepared::Opb(OpbTarget::default()),
            Solver::Asp(_) => Prepared::Asp(crate::extraction::asp::AspTarget::default()),
        }
    }

    pub fn target(&mut self) -> &mut dyn crate::extraction::target::Target {
        match self {
            Prepared::Cnf(t) => t,
            Prepared::Opb(t) => t,
            Prepared::Asp(t) => t,
        }
    }
}

/// The build's errors, if any, as one.
pub fn built(recorded: &crate::extraction::oint::Detached) -> Result<(), String> {
    if recorded.errors.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "the cost's build failed: {}",
            recorded.errors.join("; ")
        ))
    }
}

/// Solve a problem built by the caller: `rung` and `recorded` describe it and
/// `prepared` holds its constraints, in the form `solver` needs. `Err` when the build
/// recorded an error, or when a cost is outside the build's width.
pub fn solve_prepared<R: Rung + ?Sized>(
    g: &Graph,
    rung: &R,
    recorded: &crate::extraction::oint::Detached,
    prepared: Prepared,
    solver: &Solver,
) -> Result<Outcome, String> {
    built(recorded)?;
    match (prepared, solver) {
        (
            Prepared::Cnf(cnf),
            Solver::Internal {
                max_solves,
                max_conflicts,
            },
        ) => internal(g, rung, recorded, cnf, *max_solves, *max_conflicts, false),
        (
            Prepared::Cnf(cnf),
            Solver::Dpw {
                max_solves,
                max_conflicts,
            },
        ) => internal(g, rung, recorded, cnf, *max_solves, *max_conflicts, true),
        (Prepared::Opb(opb), Solver::Opb(cmd)) => external(g, rung, recorded, opb, cmd),
        (Prepared::Asp(asp), Solver::Asp(cmd)) => Ok(answer_set(g, rung, recorded, &asp, cmd)?.0),
        _ => Err("the prepared target does not match the solver".into()),
    }
}

/// Build the problem on `graph` with rung `make` and cost `cost`, and solve it, with
/// the default width (no cap). A caller choosing a cap builds with
/// [`Build::with_width`] and calls [`solve_prepared`].
pub fn extract<R, M, F>(
    graph: Arc<Graph>,
    make: M,
    cost: F,
    solver: &Solver,
) -> Result<Outcome, String>
where
    R: Rung,
    M: Fn(Selection, &mut Build) -> R,
    F: Fn(&R, &mut Build),
{
    let mut prepared = Prepared::for_solver(solver);
    let (rung, recorded) = {
        let mut b = Build::new(prepared.target());
        let sel = Selection::build(graph.clone(), &mut b);
        let r = make(sel, &mut b);
        cost(&r, &mut b);
        (r, b.detach())
    };
    solve_prepared(&graph, &rung, &recorded, prepared, solver)
}

/// The cost `cost` gives `term` at rung `make`, with no solving: for comparing two
/// cost functions on the same term. The term need not come from this build.
pub fn cost_of<R, M, F>(graph: Arc<Graph>, make: M, cost: F, term: &Term) -> Result<Cost, String>
where
    R: Rung,
    M: Fn(Selection, &mut Build) -> R,
    F: Fn(&R, &mut Build),
{
    let mut target = CnfTarget::default();
    let mut b = Build::new(&mut target);
    let sel = Selection::build(graph, &mut b);
    let r = make(sel, &mut b);
    cost(&r, &mut b);
    built(&b)?;
    interpret(&b, &r, term, &|_| false)
}

/// CaDiCaL's literal for a variable. Literals are `i32`, so a variable past 2^31 - 1 has
/// none: checked, because `as i32` would wrap it to a negative literal, a different
/// variable of the opposite sign. The formula exhausts memory long before that.
fn cadical_var(var: u32) -> i32 {
    i32::try_from(var).expect("CaDiCaL literals are i32: at most 2^31 - 1 variables")
}

fn dimacs(l: Lit) -> Option<i32> {
    match l {
        Lit::Var { var, sign } => Some(if sign {
            cadical_var(var)
        } else {
            -cadical_var(var)
        }),
        _ => None,
    }
}

fn internal<R: Rung + ?Sized>(
    g: &Graph,
    rung: &R,
    b: &crate::extraction::oint::Detached,
    cnf: CnfTarget,
    max_solves: usize,
    max_conflicts: Option<i32>,
    dpw: bool,
) -> Result<Outcome, String> {
    let CnfTarget {
        sink,
        objective,
        base,
        ..
    } = cnf;
    let mut sink: VecSink = sink;
    let mut s = CaDiCal::new();
    let mut sent = 0usize;
    let feed = |s: &mut CaDiCal, sink: &VecSink, sent: &mut usize| {
        for c in &sink.clauses[*sent..] {
            for &l in c {
                if let Some(d) = dimacs(l) {
                    s.add(d);
                }
            }
            s.add(0);
        }
        *sent = sink.clauses.len();
    };
    feed(&mut s, &sink, &mut sent);
    let mut stats = Stats::default();
    let mut best: Option<(Cost, Term)> = None;
    // The u64 totalizer when the weights and the first bound fit it, so an objective that
    // fits is encoded as it always was; the exact one otherwise, which has no cap.
    enum Sums {
        Small(WindowedSum<u64>),
        Exact(WindowedSum<Cost>),
    }
    let mut sums: Option<Sums> = None;
    let mut watchdog: Option<crate::extraction::dpw::Watchdog> = None;
    let small_objective = crate::extraction::target::weights_u64(&objective);
    if dpw {
        // rustsat's DPW sums `usize` weights; past that it is refused, not wrapped.
        let total = objective.iter().map(|&(_, w)| w).sum::<Cost>();
        if small_objective.is_none() || total.to_u64().is_none() {
            return Err(format!(
                "dpw: the objective's weights total {total}, past the 64-bit integers rustsat's DPW computes in; use :solver internal or roundingsat, which are exact"
            ));
        }
    }
    loop {
        if stats.solves >= max_solves {
            break;
        }
        if let Some((bound, _)) = &best {
            if *bound <= base {
                return Ok(done(best, Status::Proved, b, stats, &sink));
            }
            // The encoded objective is `base` plus a sum of positive weights, so any
            // cost reached is at least `base`, and the bound below it is non-negative.
            let target = *bound - base - Cost::ONE;
            // Literals whose truth enforces `objective <= target`.
            let enforce: Vec<Lit> = if dpw {
                let w = watchdog.get_or_insert_with(|| {
                    crate::extraction::dpw::Watchdog::new(
                        small_objective.as_ref().expect("checked above"),
                    )
                });
                w.at_most(
                    &mut sink,
                    target.to_u64().expect("below the total, which fits u64"),
                )
            } else {
                let w = sums.get_or_insert_with(|| match (&small_objective, target.to_u64()) {
                    (Some(o), Some(t)) if WindowedSum::fits(o, &t).is_ok() => {
                        Sums::Small(WindowedSum::new(o, t))
                    }
                    _ => Sums::Exact(WindowedSum::new(&objective, target)),
                });
                let denied = match w {
                    // The bound only decreases, so a target that fit at the first bound
                    // fits now.
                    Sums::Small(w) => w.deny_above(
                        &mut sink,
                        target.to_u64().expect("decreasing from a u64 bound"),
                    ),
                    Sums::Exact(w) => w.deny_above(&mut sink, target),
                };
                denied.into_iter().map(|l| l.not()).collect()
            };
            feed(&mut s, &sink, &mut sent);
            for l in enforce {
                if let Some(d) = dimacs(l) {
                    s.freeze(d.abs());
                    s.assume(d);
                }
            }
        }
        stats.solves += 1;
        if let Some(c) = max_conflicts {
            s.limit("conflicts".into(), c);
        }
        match s.solve() {
            SatStatus::SATISFIABLE => {}
            SatStatus::UNSATISFIABLE => {
                let status = if best.is_some() {
                    Status::Proved
                } else {
                    Status::Infeasible
                };
                return Ok(done(best, status, b, stats, &sink));
            }
            _ => break,
        }
        let n = sink.num_vars();
        let assign: Vec<bool> = (0..=n)
            .map(|v| v > 0 && s.val(cadical_var(v)) > 0)
            .collect();
        let model = |v: u32| assign.get(v as usize).copied().unwrap_or(false);
        let term = rung.decode(&model);
        if let Err(cycle) = term.order(g) {
            stats.cycle_exclusions += 1;
            for &c in &cycle {
                if let Some(nd) = term.selection[c]
                    && let Some(d) = dimacs(rung.selection().node(nd))
                {
                    s.add(-d);
                }
            }
            s.add(0);
            continue;
        }
        let cost = interpret(b, rung, &term, &model)?;
        if best.as_ref().is_none_or(|(c, _)| cost < *c) {
            best = Some((cost, term));
        } else {
            // Not an improvement: exclude exactly this term.
            stats.no_goods += 1;
            for l in rung.term_literals(&model, &term) {
                if let Some(d) = dimacs(l) {
                    s.add(-d);
                }
            }
            s.add(0);
        }
    }
    Ok(done(best, Status::Bounded, b, stats, &sink))
}

fn done(
    best: Option<(Cost, Term)>,
    status: Status,
    b: &crate::extraction::oint::Detached,
    mut stats: Stats,
    sink: &VecSink,
) -> Outcome {
    stats.clauses = sink.clauses.len();
    stats.vars = sink.num_vars();
    let (cost, term) = match best {
        Some((c, t)) => (Some(c), Some(t)),
        None => (None, None),
    };
    Outcome {
        term,
        cost,
        status: if cost.is_none() && status != Status::Bounded {
            Status::Infeasible
        } else {
            status
        },
        warnings: b.warnings.clone(),
        stats,
        solver_costs: Vec::new(),
        certificate: None,
    }
}

/// A file name no other call in this process uses, so solves on several threads
/// do not overwrite each other's input.
pub(crate) fn temp_path(ext: &str) -> std::path::PathBuf {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    std::env::temp_dir().join(format!("semper_extract_{}_{n}.{ext}", std::process::id()))
}

/// What a competition solver printed.
struct Answer {
    optimum_found: bool,
    unsat: bool,
    model: Option<BTreeMap<u32, bool>>,
}

fn run_opb(
    cmd: &OpbCommand,
    text: &str,
    proof: Option<(&std::path::Path, &std::path::Path)>,
) -> Answer {
    let path = match proof {
        Some((instance, _)) => instance.to_path_buf(),
        None => temp_path("opb"),
    };
    std::fs::write(&path, text).expect("write opb");
    // For inspecting what a solver was given: every file is kept under this directory.
    if let Ok(dir) = std::env::var("EXTRACT_API_KEEP_OPB") {
        let n = std::fs::read_dir(&dir).map(|d| d.count()).unwrap_or(0);
        let _ = std::fs::copy(
            &path,
            std::path::Path::new(&dir).join(format!("call{n:03}.opb")),
        );
    }
    let mut command = std::process::Command::new(&cmd.program);
    command.args(&cmd.args);
    if let Some((_, p)) = proof {
        command.arg(format!("--proof-log={}", p.display()));
    }
    let out = command.arg(&path).output();
    if proof.is_none() {
        let _ = std::fs::remove_file(&path);
    }
    let Ok(out) = out else {
        return Answer {
            optimum_found: false,
            unsat: false,
            model: None,
        };
    };
    let text = String::from_utf8_lossy(&out.stdout);
    let mut model: Option<BTreeMap<u32, bool>> = None;
    let (mut optimum_found, mut unsat) = (false, false);
    for line in text.lines() {
        let line = line.trim();
        if let Some(st) = line.strip_prefix("s ") {
            optimum_found |= st.contains("OPTIMUM FOUND");
            unsat |= st.contains("UNSATISFIABLE");
        }
        if let Some(vs) = line.strip_prefix("v ") {
            let m = model.get_or_insert_with(BTreeMap::new);
            for tok in vs.split_whitespace() {
                let (neg, v) = match tok.strip_prefix('-') {
                    Some(r) => (true, r),
                    None => (false, tok),
                };
                if let Some(Ok(v)) = v.strip_prefix('x').map(str::parse::<u32>) {
                    m.insert(v, !neg);
                }
            }
        }
    }
    Answer {
        optimum_found,
        unsat,
        model,
    }
}

fn external<R: Rung + ?Sized>(
    g: &Graph,
    rung: &R,
    b: &crate::extraction::oint::Detached,
    opb: OpbTarget,
    cmd: &OpbCommand,
) -> Result<Outcome, String> {
    let mut stats = Stats::default();
    let mut extra: Vec<(Vec<(Cost, Lit)>, Cmp, Cost)> = Vec::new();
    let mut best: Option<(Cost, Term)> = None;
    let deadline = Instant::now() + cmd.timeout;
    let empty = VecSink::new(0);
    if let Some(d) = &cmd.proof_dir {
        let _ = std::fs::create_dir_all(d);
    }
    let certify = |out: &mut Outcome, call: usize, claim: Claim| {
        if let Some(d) = &cmd.proof_dir {
            out.certificate = Some(Certificate {
                instance: d.join(format!("call{call:03}.opb")),
                proof: d.join(format!("call{call:03}.pbp")),
                claim,
                base: opb.base,
            });
        }
    };
    loop {
        if Instant::now() > deadline || stats.solver_calls > 200 {
            return Ok(done(best, Status::Bounded, b, stats, &empty));
        }
        let mut lines = extra.clone();
        // Restarting forgets what the solver learned, so the incumbent is restated.
        if let Some((c, _)) = &best {
            let terms: Vec<(Cost, Lit)> = opb.objective.iter().map(|&(l, w)| (w, l)).collect();
            lines.push((terms, Cmp::Le, *c - opb.base - Cost::ONE));
        }
        let call = stats.solver_calls;
        stats.solver_calls += 1;
        let files = cmd.proof_dir.as_ref().map(|d| {
            (
                d.join(format!("call{call:03}.opb")),
                d.join(format!("call{call:03}.pbp")),
            )
        });
        opb_fits(&opb, &lines, cmd)?;
        let ans = run_opb(
            cmd,
            &opb.to_opb_with(&lines, files.is_some()),
            files.as_ref().map(|(i, p)| (i.as_path(), p.as_path())),
        );
        let Some(m) = ans.model else {
            let status = if ans.unsat && best.is_some() {
                Status::Proved
            } else if ans.unsat {
                Status::Infeasible
            } else {
                Status::Bounded
            };
            let below = best.as_ref().map(|(c, _)| *c);
            let mut out = done(best, status, b, stats, &empty);
            if ans.unsat {
                certify(&mut out, call, Claim::Unsat { below });
            }
            return Ok(out);
        };
        let model = |v: u32| m.get(&v).copied().unwrap_or(false);
        let term = rung.decode(&model);
        if let Err(cycle) = term.order(g) {
            stats.cycle_exclusions += 1;
            let cl: Vec<(Cost, Lit)> = cycle
                .iter()
                .filter_map(|&c| term.selection[c])
                .map(|nd| (Cost::ONE, rung.selection().node(nd).not()))
                .collect();
            extra.push((cl, Cmp::Ge, Cost::ONE));
            continue;
        }
        let cost = interpret(b, rung, &term, &model)?;
        if best.as_ref().is_none_or(|(c, _)| cost < *c) {
            best = Some((cost, term.clone()));
        }
        if ans.optimum_found {
            // Proved as it stands. The solver's optimum `o` is the least objective over
            // all models of the current formula. Every term has a model whose
            // objective is its cost (its canonical assignment, which satisfies the
            // cycle exclusions because they only forbid nodes the term does not
            // reach), so no term costs less than `o`; and this model's term costs at
            // most `o`. A further call to confirm it is redundant, and on a hard
            // instance it is the call that times out.
            let o: Cost = opb
                .objective
                .iter()
                .filter(|&&(l, _)| lit_holds(l, &model))
                .map(|&(_, w)| w)
                .sum();
            let mut out = done(best, Status::Proved, b, stats, &empty);
            certify(&mut out, call, Claim::Bounds { lower: o });
            return Ok(out);
        }
    }
}

/// Every coefficient, bound, and objective weight of the instance as written, in the
/// solver's range ([`OpbCommand::opb_range`]).
fn opb_fits(
    opb: &OpbTarget,
    extra: &[(Vec<(Cost, Lit)>, Cmp, Cost)],
    cmd: &OpbCommand,
) -> Result<(), String> {
    let (range, name) = (cmd.opb_range(), cmd.solver_name());
    for (terms, _, k) in opb.constraints.iter().chain(extra.iter()) {
        for &(a, _) in terms {
            range.check(&name, "a constraint coefficient", a)?;
        }
        range.check(&name, "a constraint bound", *k)?;
    }
    for &(_, w) in &opb.objective {
        range.check(&name, "an objective weight", w)?;
    }
    Ok(())
}

fn lit_holds(l: Lit, model: &dyn Fn(u32) -> bool) -> bool {
    match l {
        Lit::True => true,
        Lit::False => false,
        Lit::Var { var, sign } => model(var) == sign,
    }
}

// --- terms in a cost band ------------------------------------------------------------

/// Terms whose interpreted cost lies in `[lo, hi]`, at most `count` of them: the
/// request behind controlled sub-optimality, where the optimum `o` is known and
/// equivalent terms at a chosen gap above it are wanted.
#[derive(Clone, Copy, Debug)]
pub struct Band {
    pub lo: Cost,
    pub hi: Cost,
    pub count: usize,
}

/// Distinct terms with interpreted cost in the band, in the order found, each with
/// its cost.
///
/// The objective is bounded on both sides before solving. Every term has a model
/// whose objective is its cost (its canonical assignment), so neither bound loses a
/// term in the band; the upper bound also excludes every term above it, since a
/// model's objective is at least its term's cost. A model whose term costs less
/// than `lo`, which an over-estimating encoding allows, is skipped. Each term found
/// is excluded exactly by its rung literals, and a cyclic selection by a clause over
/// its selectors, as in the descent.
///
/// `Err` when the build recorded an error, a cost is outside its width, or the
/// band's bounds do not fit the totalizer.
pub fn band_prepared<R: Rung + ?Sized>(
    g: &Graph,
    rung: &R,
    b: &crate::extraction::oint::Detached,
    mut cnf: CnfTarget,
    band: Band,
    max_solves: usize,
) -> Result<(Vec<(Cost, Term)>, Stats), String> {
    use crate::extraction::target::Target;
    built(b)?;
    let terms: Vec<(Cost, Lit)> = cnf.objective.iter().map(|&(l, w)| (w, l)).collect();
    let base = cnf.base;
    cnf.pb(&terms, Cmp::Ge, band.lo - base)?;
    cnf.pb(&terms, Cmp::Le, band.hi - base)?;
    let CnfTarget { sink, .. } = cnf;
    let mut s = CaDiCal::new();
    for c in &sink.clauses {
        for &l in c {
            if let Some(d) = dimacs(l) {
                s.add(d);
            }
        }
        s.add(0);
    }
    let mut stats = Stats::default();
    let mut found = Vec::new();
    while found.len() < band.count && stats.solves < max_solves {
        stats.solves += 1;
        if s.solve() != SatStatus::SATISFIABLE {
            break;
        }
        let n = sink.num_vars();
        let assign: Vec<bool> = (0..=n)
            .map(|v| v > 0 && s.val(cadical_var(v)) > 0)
            .collect();
        let model = |v: u32| assign.get(v as usize).copied().unwrap_or(false);
        let term = rung.decode(&model);
        if let Err(cycle) = term.order(g) {
            stats.cycle_exclusions += 1;
            for &c in &cycle {
                if let Some(nd) = term.selection[c]
                    && let Some(d) = dimacs(rung.selection().node(nd))
                {
                    s.add(-d);
                }
            }
            s.add(0);
            continue;
        }
        let cost = interpret(b, rung, &term, &model)?;
        for l in rung.term_literals(&model, &term) {
            if let Some(d) = dimacs(l) {
                s.add(-d);
            }
        }
        s.add(0);
        if cost >= band.lo && cost <= band.hi {
            found.push((cost, term));
        } else {
            stats.no_goods += 1;
        }
    }
    stats.clauses = sink.clauses.len();
    stats.vars = sink.num_vars();
    Ok((found, stats))
}

// --- answer-set programming ---------------------------------------------------------

/// What an answer-set run measured, beside the outcome.
#[derive(Clone, Debug, Default)]
pub struct AspStats {
    /// The solver's optimization values, most important first.
    pub costs: Vec<i64>,
    pub atoms: u64,
    pub rules: u64,
    pub seconds: f64,
}

/// The acyclicity rules: a class is `ok` through a selected member whose children
/// are all `ok`, and a selected class must be `ok`. Stable models are supported, so
/// no cyclic selection survives.
fn groundedness<R: Rung + ?Sized>(g: &Graph, rung: &R) -> String {
    use crate::extraction::asp::atom;
    let sel = rung.selection();
    let mut out = String::new();
    for &c in &sel.reachable {
        for n in g.candidates(c) {
            let mut body = vec![atom(sel.node(n))];
            let mut kids: Vec<usize> = g.nodes[n].children.clone();
            kids.sort_unstable();
            kids.dedup();
            body.extend(kids.iter().map(|k| format!("ok({k})")));
            out.push_str(&format!("ok({c}) :- {}.\n", body.join(", ")));
        }
        out.push_str(&format!(":- {}, not ok({c}).\n", atom(sel.class(c))));
    }
    out
}

fn run_asp(cmd: &OpbCommand, text: &str) -> (Option<BTreeMap<u32, bool>>, bool, bool, AspStats) {
    let path = temp_path("lp");
    std::fs::write(&path, text).expect("write lp");
    if let Ok(dir) = std::env::var("EXTRACT_API_KEEP_ASP") {
        let n = std::fs::read_dir(&dir).map(|d| d.count()).unwrap_or(0);
        let _ = std::fs::copy(
            &path,
            std::path::Path::new(&dir).join(format!("call{n:03}.lp")),
        );
    }
    let t = Instant::now();
    let out = std::process::Command::new(&cmd.program)
        .args(["--outf=2", "--quiet=1", "--stats"])
        .args(&cmd.args)
        .arg(&path)
        .output();
    let seconds = t.elapsed().as_secs_f64();
    let _ = std::fs::remove_file(&path);
    let mut stats = AspStats {
        seconds,
        ..Default::default()
    };
    let Ok(out) = out else {
        return (None, false, false, stats);
    };
    let Ok(v) = serde_json::from_slice::<serde_json::Value>(&out.stdout) else {
        return (None, false, false, stats);
    };
    let result = v["Result"].as_str().unwrap_or("");
    let optimum = result == "OPTIMUM FOUND"
        || (result == "SATISFIABLE" && v["Models"]["Optimum"].as_str() == Some("yes"));
    let unsat = result == "UNSATISFIABLE";
    let lp = &v["Stats"]["LP"];
    stats.atoms = lp["Atoms"].as_u64().unwrap_or(0);
    stats.rules = lp["Rules"]["Original"].as_u64().unwrap_or(0);
    let witness = v["Call"]
        .as_array()
        .and_then(|c| c.last())
        .and_then(|c| c["Witnesses"].as_array())
        .and_then(|w| w.last());
    let Some(w) = witness else {
        return (None, optimum, unsat, stats);
    };
    stats.costs = w["Costs"]
        .as_array()
        .map(|c| c.iter().filter_map(|x| x.as_i64()).collect())
        .unwrap_or_default();
    let mut m = BTreeMap::new();
    for a in w["Value"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|a| a.as_str())
    {
        if let Some(v) = a
            .strip_prefix("x(")
            .and_then(|r| r.strip_suffix(')'))
            .and_then(|r| r.parse::<u32>().ok())
        {
            m.insert(v, true);
        }
    }
    (Some(m), optimum, unsat, stats)
}

/// Solve an answer-set program once. The acyclicity rules make every model
/// acyclic, so there is no exclusion loop, and an `OPTIMUM FOUND` is a proof: every
/// term has a model whose objective is its cost (its canonical assignment, extended
/// by the `ok` atoms of its classes), so no term costs less than the optimum.
pub fn answer_set<R: Rung + ?Sized>(
    g: &Graph,
    rung: &R,
    b: &crate::extraction::oint::Detached,
    asp: &crate::extraction::asp::AspTarget,
    cmd: &OpbCommand,
) -> Result<(Outcome, AspStats), String> {
    built(b)?;
    let text = asp.to_asp(&groundedness(g, rung));
    let (model, optimum, unsat, stats) = run_asp(cmd, &text);
    let mut out_stats = Stats {
        solver_calls: 1,
        vars: crate::extraction::target::Target::num_vars(asp),
        ..Default::default()
    };
    let empty = VecSink::new(0);
    let Some(m) = model else {
        let status = if unsat {
            Status::Infeasible
        } else {
            Status::Bounded
        };
        return Ok((done(None, status, b, out_stats, &empty), stats));
    };
    let model = |v: u32| m.get(&v).copied().unwrap_or(false);
    let term = rung.decode(&model);
    assert!(
        term.order(g).is_ok(),
        "an answer set with a cyclic selection: the acyclicity rules are wrong"
    );
    let cost = interpret(b, rung, &term, &model)?;
    out_stats.solves = 1;
    let status = if optimum {
        Status::Proved
    } else {
        Status::Bounded
    };
    let mut out = done(Some((cost, term)), status, b, out_stats, &empty);
    if asp.extended_objective {
        out.solver_costs = stats.costs.clone();
    }
    Ok((out, stats))
}

/// Build on an [`crate::extraction::asp::AspTarget`] with a cost that may use the ASP
/// extension, and solve it. `interpret_ext` gives the term's cost vector, most
/// important first, from the term and the interpreted common objective; it is what
/// the outcome reports, since the extension's objectives are the solver's.
pub fn extract_asp<R, M, F>(
    graph: Arc<Graph>,
    make: M,
    cost: F,
    cmd: &OpbCommand,
) -> Result<(Outcome, AspStats), String>
where
    R: Rung,
    M: Fn(Selection, &mut Build) -> R,
    F: Fn(&R, &mut crate::extraction::asp::AspBuild),
{
    let mut asp = crate::extraction::asp::AspTarget::default();
    let (rung, recorded) = {
        let mut b = Build::new(&mut asp);
        let sel = Selection::build(graph.clone(), &mut b);
        let r = make(sel, &mut b);
        {
            let mut ab = crate::extraction::asp::AspBuild::new(&mut b).expect("an ASP target");
            cost(&r, &mut ab);
        }
        (r, b.detach())
    };
    answer_set(&graph, &rung, &recorded, &asp, cmd)
}
