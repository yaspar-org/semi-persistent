// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Scaling crossover between the exact anti-unification solver and MCGS.
//!
//! The exact solver (`eager_with_memo`, exact.rs) is a DP over OR states
//! keyed `(l, r, ctx_l, ctx_r)` (space.rs `get_or_insert_or_node`) with no
//! internal budget or deadline: it enumerates every reachable state. MCGS
//! does bounded work per playout, so its runtime is capped by the playout
//! budget regardless of how large the reachable state space is. This file
//! constructs an instance family whose exact-solver state count grows
//! roughly exponentially in one knob while the MCGS cost stays flat, and
//! measures where the exact solver stops terminating within a 30 s guard.
//!
//! Instance family `build_instance(depth, width, cycles)`:
//!
//! * `cycles` = number of classes `W_0..W_{c-1}`, each made cyclic by a
//!   shared-operator self-wrap `merge(h(W_i), W_i)` and made mutually
//!   reachable through the width members below. Cyclic classes feed the
//!   dominant cost driver: OR states are keyed by the pair of cycle
//!   contexts, and a context here is the set of W classes visited so far on
//!   the current path (every W is reachable from every other, so
//!   `derive_child_context` never drops one). Paths can visit the W classes
//!   in many different orders, so the reachable `(ctx_l, ctx_r)` pairs grow
//!   combinatorially in `cycles`, and the per-OR-id memo cannot collapse
//!   them.
//! * `width` = members with the SAME binary operator `b` merged into each
//!   W class: `merge(b(W_target, t_i), W_i)` for `width` distinct targets.
//!   Because both classes of an OR node carry `width` same-op members, the
//!   positional-zip action generator (actions.rs
//!   `generate_ordered_actions`) emits `width x width` actions per state:
//!   the branching factor that lets paths reach all those context subsets.
//!   The per-class tag constant `t_i` keeps the `b` nodes distinct, so
//!   congruence closure cannot collapse two W classes.
//! * `depth` = a complete binary backbone tree over a shared operator `f`
//!   with `2^depth` leaves. It feeds baseline lgg size, not the blowup: the
//!   two roots share the whole `f` spine, most leaves are a shared constant
//!   `p`, and the remaining leaves differ in two ways, mirroring the
//!   metamorphic mutations: "hot" leaves pair two DISTINCT cyclic classes
//!   (left `W_i`, right `W_j`, i != j), igniting the W state space, and
//!   "diff" leaves pair two side-local fresh constants, forcing plain
//!   `Variants` leaves. The lgg therefore keeps the full backbone and is
//!   much larger than a single variable.
//!
//! The exact solver runs on a worker thread with an `mpsc::recv_timeout`
//! guard (pattern from au_metamorphic.rs `run_case_guarded`); on timeout
//! the worker is leaked, detached and still burning CPU/RAM, which is the
//! accepted pattern. Each sweep stops escalating after the FIRST exact
//! timeout so at most one worker leaks, and the process exits shortly
//! after (MCGS finishes in seconds), which reclaims it.
//!
//! Two additional `#[ignore]` families isolate single cost drivers without
//! cycles:
//!
//! * `sweep_width_only` (`build_width_instance`): acyclic, no self-wraps.
//!   A depth-d spine where at every level both sides hold `width` members
//!   of the same binary operator (distinguished by per-level tag constants
//!   shared between the sides), so every level-pair OR state fans out
//!   `width x width` zip actions. Contexts stay empty (no cycles), so the
//!   per-OR memo can collapse the `width^(2 depth)` path product to about
//!   `depth * width^2` work; the sweep measures whether it does.
//!
//! * `sweep_ac_members` (`build_ac_instance`): one AC (MSet) class pair,
//!   acyclic. Each side holds `members` distinct AC members — sliding
//!   windows of `children` constants over a shared ring, plus a side
//!   marker — so the representation-pair product (ac_repr.rs
//!   `representation_pairs`, built on `monomials_of`) is `members^2`, each
//!   pair with a `(children+1)^2` transport cell matrix, for both solvers
//!   (exact.rs transport path; mcgs.rs expansion enumerates the same
//!   pairs).
//!
//! `print_crossover_instance` renders the crossover-level instance (both
//! roots, the full merge list) and the MCGS generalization with its
//! variables' class-pair bindings, for reconstruction on paper.

use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{
    AuAlgorithm, AuConfig, AuResult, Completion, anti_unify,
};
use semi_persistent_egraph::au::space::CycleMode;
use semi_persistent_egraph::au::terms::{TermId, TermOp, TermPool};
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::nodes::LitValId;

type Eg = EGraph31<NiraLitVal, false, false>;

// ---------------------------------------------------------------------------
// Instance family.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
struct Params {
    /// Backbone binary-tree depth: 2^depth leaves. Baseline lgg size.
    depth: usize,
    /// Same-op `b` members per cyclic class: width^2 actions per OR state.
    width: usize,
    /// Cyclic, mutually reachable classes: pair actions and member
    /// combinations grow in this knob.
    cycles: usize,
}

struct Instance {
    eg: Eg,
    left: ENodeId,
    right: ENodeId,
}

/// A readable s-expression mirroring one constructed e-node. Recorded by
/// `build_instance_traced` alongside the real construction so the printed
/// instance cannot drift from the built one.
#[derive(Clone)]
struct Sx {
    head: String,
    args: Vec<Sx>,
}

impl Sx {
    fn leaf(head: impl Into<String>) -> Self {
        Sx {
            head: head.into(),
            args: Vec::new(),
        }
    }

    fn app(head: &str, args: Vec<Sx>) -> Self {
        Sx {
            head: head.to_owned(),
            args,
        }
    }

    fn flat(&self) -> String {
        if self.args.is_empty() {
            return self.head.clone();
        }
        let args: Vec<String> = self.args.iter().map(Sx::flat).collect();
        format!("({} {})", self.head, args.join(" "))
    }

    /// Fits-inline-or-break rendering (same rule as au/pretty.rs). Recursion
    /// depth equals term depth, which is small for every instance here.
    fn pretty(&self, col_limit: usize) -> String {
        let mut out = String::new();
        self.pretty_into(0, col_limit, &mut out);
        out
    }

    fn pretty_into(&self, indent: usize, col_limit: usize, out: &mut String) {
        let flat = self.flat();
        if indent + flat.len() <= col_limit || self.args.is_empty() {
            out.push_str(&flat);
            return;
        }
        out.push('(');
        out.push_str(&self.head);
        for arg in &self.args {
            out.push('\n');
            for _ in 0..indent + 2 {
                out.push(' ');
            }
            arg.pretty_into(indent + 2, col_limit, out);
        }
        out.push(')');
    }
}

/// Symbolic trace of a `build_instance` run: the two roots and every merge,
/// in application order.
struct InstanceTrace {
    left: Sx,
    right: Sx,
    merges: Vec<(Sx, Sx)>,
}

fn build_instance(p: Params) -> Instance {
    build_instance_traced(p).0
}

fn build_instance_traced(p: Params) -> (Instance, InstanceTrace) {
    assert!(p.cycles >= 2, "hot leaves need two distinct W classes");
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let f = eg.register_op2("f", sort, sort, sort); // shared backbone
    let b = eg.register_op2("b", sort, sort, sort); // shared width op
    let h = eg.register_op1("h", sort, sort); // shared self-wrap op
    let p_op = eg.register_op0("p", sort); // shared filler leaf
    let dl_op = eg.register_op0("dl", sort); // left-only fresh leaf
    let dr_op = eg.register_op0("dr", sort); // right-only fresh leaf
    let w_ops: Vec<OpId> = (0..p.cycles)
        .map(|i| eg.register_op0(&format!("w{i}"), sort))
        .collect();
    let tag_ops: Vec<OpId> = (0..p.cycles)
        .map(|i| eg.register_op0(&format!("t{i}"), sort))
        .collect();

    // W classes: finite base constant, then the cycle driver, then the
    // width driver. `b(W_target, t_i)` is unique per (target, i), so no two
    // W classes ever share a member and congruence keeps them distinct.
    let w: Vec<ENodeId> = w_ops.iter().map(|&op| eg.add(op, &[])).collect();
    let tags: Vec<ENodeId> = tag_ops.iter().map(|&op| eg.add(op, &[])).collect();
    let w_sx: Vec<Sx> = (0..p.cycles).map(|i| Sx::leaf(format!("w{i}"))).collect();
    let tag_sx: Vec<Sx> = (0..p.cycles).map(|i| Sx::leaf(format!("t{i}"))).collect();
    let mut merges: Vec<(Sx, Sx)> = Vec::new();
    for (i, &wi) in w.iter().enumerate() {
        let hw = eg.add(h, &[wi]);
        eg.merge(hw, wi);
        merges.push((Sx::app("h", vec![w_sx[i].clone()]), w_sx[i].clone()));
    }
    let fan = p.width.min(p.cycles - 1);
    for (i, &tag) in tags.iter().enumerate() {
        for j in 1..=fan {
            let ti = (i + j) % p.cycles;
            let target = w[ti];
            let member = eg.add(b, &[target, tag]);
            eg.merge(member, w[i]);
            merges.push((
                Sx::app("b", vec![w_sx[ti].clone(), tag_sx[i].clone()]),
                w_sx[i].clone(),
            ));
        }
    }
    eg.rebuild();

    // Backbone: identical f-tree shape on both sides, leaves scattered
    // between shared, hot (distinct W pair), and diff (fresh constants).
    let shared = eg.add(p_op, &[]);
    let dl = eg.add(dl_op, &[]);
    let dr = eg.add(dr_op, &[]);
    let n_leaves = 1usize << p.depth;
    let mut left_level: Vec<ENodeId> = Vec::with_capacity(n_leaves);
    let mut right_level: Vec<ENodeId> = Vec::with_capacity(n_leaves);
    let mut left_sx: Vec<Sx> = Vec::with_capacity(n_leaves);
    let mut right_sx: Vec<Sx> = Vec::with_capacity(n_leaves);
    for t in 0..n_leaves {
        match t % 4 {
            0 => {
                left_level.push(w[t % p.cycles]);
                right_level.push(w[(t + 1) % p.cycles]);
                left_sx.push(w_sx[t % p.cycles].clone());
                right_sx.push(w_sx[(t + 1) % p.cycles].clone());
            }
            2 => {
                left_level.push(dl);
                right_level.push(dr);
                left_sx.push(Sx::leaf("dl"));
                right_sx.push(Sx::leaf("dr"));
            }
            _ => {
                left_level.push(shared);
                right_level.push(shared);
                left_sx.push(Sx::leaf("p"));
                right_sx.push(Sx::leaf("p"));
            }
        }
    }
    while left_level.len() > 1 {
        left_level = left_level.chunks(2).map(|c| eg.add(f, c)).collect();
        right_level = right_level.chunks(2).map(|c| eg.add(f, c)).collect();
        left_sx = left_sx
            .chunks(2)
            .map(|c| Sx::app("f", c.to_vec()))
            .collect();
        right_sx = right_sx
            .chunks(2)
            .map(|c| Sx::app("f", c.to_vec()))
            .collect();
    }
    eg.rebuild();

    (
        Instance {
            eg,
            left: left_level[0],
            right: right_level[0],
        },
        InstanceTrace {
            left: left_sx.remove(0),
            right: right_sx.remove(0),
            merges,
        },
    )
}

// ---------------------------------------------------------------------------
// Width-only family: acyclic, no self-wraps. `width` same-op members per
// side per level over a depth-`depth` spine; the only pressure is the
// per-level member cross product.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
struct WidthParams {
    /// Spine levels.
    depth: usize,
    /// Same-op `b` members per class per side per level: `width^2` zip
    /// actions per level-pair OR state.
    width: usize,
}

fn build_width_instance(p: WidthParams) -> Instance {
    assert!(p.depth >= 1 && p.width >= 1);
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let b = eg.register_op2("b", sort, sort, sort); // shared width op
    let cl_op = eg.register_op0("cl", sort); // left-only base leaf
    let cr_op = eg.register_op0("cr", sort); // right-only base leaf
    let mut left = eg.add(cl_op, &[]);
    let mut right = eg.add(cr_op, &[]);
    for level in 0..p.depth {
        // Per-level tag constants, SHARED between the sides: member j on the
        // left is `b(L_{level-1}, t_{level}_{j})` and member j on the right is
        // `b(R_{level-1}, t_{level}_{j})`. The spines differ (cl vs cr at the
        // bottom), so congruence never merges left and right classes, while
        // the shared tags keep the optimal zip (j paired with j) cheap.
        let tags: Vec<ENodeId> = (0..p.width)
            .map(|j| {
                let op = eg.register_op0(&format!("t{level}_{j}"), sort);
                eg.add(op, &[])
            })
            .collect();
        let l_members: Vec<ENodeId> = tags.iter().map(|&t| eg.add(b, &[left, t])).collect();
        let r_members: Vec<ENodeId> = tags.iter().map(|&t| eg.add(b, &[right, t])).collect();
        for &m in &l_members[1..] {
            eg.merge(m, l_members[0]);
        }
        for &m in &r_members[1..] {
            eg.merge(m, r_members[0]);
        }
        left = l_members[0];
        right = r_members[0];
    }
    eg.rebuild();
    Instance { eg, left, right }
}

// ---------------------------------------------------------------------------
// AC-members family: one MSet class pair, acyclic. `members` monomial
// representations per side, `children` distinct child constants per member.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
struct AcParams {
    /// Distinct AC members merged into each side's class: the
    /// representation-pair product is `members^2`.
    members: usize,
    /// Distinct child constants per member: each representation pair gets a
    /// `(children+1) x (children+1)` transport cell matrix.
    children: usize,
}

fn build_ac_instance(p: AcParams) -> Instance {
    assert!(p.members >= 1 && p.children >= 1);
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let m = eg.register_mset("m", sort, sort);
    let lmark_op = eg.register_op0("lmark", sort); // left-only marker
    let rmark_op = eg.register_op0("rmark", sort); // right-only marker
    let lmark = eg.add(lmark_op, &[]);
    let rmark = eg.add(rmark_op, &[]);
    // Shared ring of child constants; member i is the window of `children`
    // consecutive constants starting at i, so all `members` windows are
    // distinct (ring size > members) and adjacent windows overlap, giving
    // the transport real matching work.
    let ring = p.members + p.children;
    let cs: Vec<ENodeId> = (0..ring)
        .map(|i| {
            let op = eg.register_op0(&format!("c{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    let left = add_ac_side(&mut eg, m, lmark, &cs, p);
    let right = add_ac_side(&mut eg, m, rmark, &cs, p);
    eg.rebuild();
    Instance { eg, left, right }
}

/// Add one side's `members` AC members (side marker + sliding window) and
/// merge them into a single class; returns a member of that class.
fn add_ac_side(eg: &mut Eg, m: OpId, mark: ENodeId, cs: &[ENodeId], p: AcParams) -> ENodeId {
    let members: Vec<ENodeId> = (0..p.members)
        .map(|i| {
            let mut kids = Vec::with_capacity(p.children + 1);
            kids.push(mark);
            for j in 0..p.children {
                kids.push(cs[(i + j) % cs.len()]);
            }
            eg.add(m, &kids)
        })
        .collect();
    for &member in &members[1..] {
        eg.merge(member, members[0]);
    }
    members[0]
}

// ---------------------------------------------------------------------------
// Projection helpers (pattern from au_metamorphic.rs; instances are shallow,
// so the recursive form is fine).
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum OwnedTerm {
    App(OpId, Vec<OwnedTerm>),
    Lit(OpId, LitValId),
}

fn own_projected(pool: &TermPool<OpId, LitValId>, id: TermId) -> OwnedTerm {
    match pool.op(id) {
        TermOp::EGraph(op) => OwnedTerm::App(
            *op,
            pool.children(id)
                .iter()
                .map(|&child| own_projected(pool, child))
                .collect(),
        ),
        TermOp::Literal(op, value) => OwnedTerm::Lit(*op, *value),
        TermOp::Variants => panic!("projection still contains Variants"),
    }
}

fn materialize(eg: &mut Eg, term: &OwnedTerm) -> ENodeId {
    match term {
        OwnedTerm::App(op, children) => {
            let child_ids: Vec<ENodeId> = children.iter().map(|c| materialize(eg, c)).collect();
            eg.add(*op, &child_ids)
        }
        OwnedTerm::Lit(op, value) => eg.add_lit(*op, *value),
    }
}

fn projected_terms(
    mut result: AuResult<semi_persistent_egraph::nodes::DefaultConfig>,
) -> (OwnedTerm, OwnedTerm) {
    let left = result.pool.project(result.term_id, 0);
    let right = result.pool.project(result.term_id, 1);
    (
        own_projected(&result.pool, left),
        own_projected(&result.pool, right),
    )
}

// ---------------------------------------------------------------------------
// Result-term rendering (for the instance printer): Variants nodes are the
// variables of the generalization; each stands for one (left class, right
// class) pair, its two children being the classes' best representatives.
// ---------------------------------------------------------------------------

/// Distinct `Variants` nodes of the term, in first-visit DFS preorder
/// (left-to-right), i.e. reading order of the rendered term.
fn collect_variant_nodes(pool: &TermPool<OpId, LitValId>, root: TermId) -> Vec<TermId> {
    let mut vars: Vec<TermId> = Vec::new();
    let mut visited: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = vec![root];
    while let Some(id) = stack.pop() {
        if visited.contains(&id) {
            continue;
        }
        visited.push(id);
        if matches!(pool.op(id), TermOp::Variants) {
            vars.push(id);
        }
        for &child in pool.children(id).iter().rev() {
            stack.push(child);
        }
    }
    vars
}

/// Render a pool term as an `Sx`, naming each `Variants` node `x<i>` by its
/// position in `vars`. Recursion depth equals term depth (small here).
fn term_to_sx(eg: &Eg, pool: &TermPool<OpId, LitValId>, id: TermId, vars: &[TermId]) -> Sx {
    match pool.op(id) {
        TermOp::Variants => {
            let i = vars
                .iter()
                .position(|&v| v == id)
                .expect("every Variants node was collected");
            Sx::leaf(format!("x{i}"))
        }
        TermOp::EGraph(op) => Sx {
            head: eg.ops().info(*op).name.clone(),
            args: pool
                .children(id)
                .iter()
                .map(|&child| term_to_sx(eg, pool, child, vars))
                .collect(),
        },
        TermOp::Literal(op, value) => Sx::leaf(format!("{}#{value:?}", eg.ops().info(*op).name)),
    }
}

// ---------------------------------------------------------------------------
// Solver runners.
// ---------------------------------------------------------------------------

enum ExactOutcome {
    Done { size: u32, elapsed: Duration },
    Timeout,
}

/// Run the exact solver on a worker thread with a receive timeout (pattern
/// from au_metamorphic.rs `run_case_guarded`): the solver has no internal
/// budget, so this guard is the only bound. On timeout the worker thread is
/// leaked (detached, still running) — accepted, and the sweep stops
/// escalating after the first timeout so at most one worker leaks.
fn run_exact_guarded(p: Params, timeout: Duration) -> ExactOutcome {
    run_exact_guarded_with(
        &format!("c{}k{}d{}", p.cycles, p.width, p.depth),
        move || build_instance(p),
        timeout,
        false,
    )
}

/// Generic form of the guard for the other instance families: the builder
/// runs on the worker thread so a timeout abandons the build too. `pruning`
/// sets `AuConfig::exact_pruning`; the sweeps pass false to measure the
/// unpruned cycle-complete reference search.
fn run_exact_guarded_with<F>(
    label: &str,
    build: F,
    timeout: Duration,
    pruning: bool,
) -> ExactOutcome
where
    F: FnOnce() -> Instance + Send + 'static,
{
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .name(format!("au-exact-{label}"))
        .spawn(move || {
            let inst = build();
            let snap = AuSnapshot::new(&inst.eg).unwrap();
            let start = Instant::now();
            let result = anti_unify(
                &snap,
                inst.left,
                inst.right,
                &AuConfig {
                    algorithm: AuAlgorithm::Exact,
                    cycle_mode: CycleMode::Pair,
                    exact_pruning: pruning,
                    ..Default::default()
                },
            )
            .unwrap();
            let _ = tx.send((result.size, start.elapsed()));
        })
        .unwrap();
    match rx.recv_timeout(timeout) {
        Ok((size, elapsed)) => ExactOutcome::Done { size, elapsed },
        Err(mpsc::RecvTimeoutError::Timeout) => ExactOutcome::Timeout,
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("exact worker panicked for {label}; its message is above")
        }
    }
}

struct McgsRun {
    size: u32,
    certified: bool,
    elapsed: Duration,
    projections: (OwnedTerm, OwnedTerm),
}

fn run_mcgs(inst: &Instance, playouts: u64) -> McgsRun {
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let start = Instant::now();
    let result = anti_unify(
        &snap,
        inst.left,
        inst.right,
        &AuConfig {
            algorithm: AuAlgorithm::Uct,
            playouts,
            ..Default::default()
        },
    )
    .unwrap();
    let elapsed = start.elapsed();
    McgsRun {
        size: result.size,
        certified: result.completion == Completion::Exact,
        elapsed,
        projections: projected_terms(result),
    }
}

/// Materialize both projections back into the e-graph and check they land in
/// their source classes; also reject the trivial single-variable lgg.
fn assert_mcgs_answer_sane(inst: &mut Instance, run: &McgsRun, label: &str) {
    assert!(
        run.size > 1,
        "{label}: MCGS returned the trivial single-variable generalization \
         (size {}); the sides should share the whole backbone",
        run.size
    );
    let (lp, rp) = &run.projections;
    let pl = materialize(&mut inst.eg, lp);
    let pr = materialize(&mut inst.eg, rp);
    inst.eg.rebuild();
    assert_eq!(
        inst.eg.find_const(pl),
        inst.eg.find_const(inst.left),
        "{label}: MCGS left projection does not re-evaluate into the left class"
    );
    assert_eq!(
        inst.eg.find_const(pr),
        inst.eg.find_const(inst.right),
        "{label}: MCGS right projection does not re-evaluate into the right class"
    );
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

const MCGS_PLAYOUTS: u64 = 256;
const EXACT_TIMEOUT: Duration = Duration::from_secs(30);

/// Modest scale: both solvers terminate quickly, so CI stays green. The
/// state space at cycles=3 is a few hundred OR states.
#[test]
fn default_scale_exact_and_mcgs_terminate() {
    let p = Params {
        depth: 4,
        width: 2,
        cycles: 3,
    };
    let exact = match run_exact_guarded(p, EXACT_TIMEOUT) {
        ExactOutcome::Done { size, elapsed } => {
            println!("exact: size={size} elapsed={elapsed:?}");
            size
        }
        ExactOutcome::Timeout => panic!("exact timed out at the default scale {p:?}"),
    };

    let mut inst = build_instance(p);
    let mcgs = run_mcgs(&inst, MCGS_PLAYOUTS);
    println!(
        "mcgs: size={} certified={} elapsed={:?}",
        mcgs.size, mcgs.certified, mcgs.elapsed
    );
    assert!(
        mcgs.elapsed < Duration::from_secs(10),
        "MCGS at {MCGS_PLAYOUTS} playouts should be well under its guard, took {:?}",
        mcgs.elapsed
    );
    assert!(
        mcgs.size >= exact,
        "MCGS size {} beats the exact optimum {exact}; exact optimality is broken",
        mcgs.size
    );
    assert_mcgs_answer_sane(&mut inst, &mcgs, "default scale");
}

/// Escalating sweep: run both solvers per level, print a table row, stop
/// after the first exact timeout (one leaked worker max — see module doc).
/// Run with:
/// `cargo test -p semi-persistent-egraph --release --test au_scaling_crossover -- --ignored --nocapture`
///
/// Measured 2026-08-15 (release, Apple Silicon), depth=4, width=cycles-1:
/// exact grows about 7x per added cycle class — 22.6 ms at cycles=6,
/// 662 ms at cycles=8, 7.81 s at cycles=9, TIMEOUT(30 s) at cycles=10 —
/// while MCGS at 256 playouts stays at 1-4 ms with size 39 at every level.
/// Measured unguarded completion at cycles=10: 49.2 s release, size 39 — a
/// guard artifact, not divergence.
#[test]
#[ignore = "manual sweep: escalates until the exact solver exceeds a 30 s guard"]
fn scaling_sweep_exact_vs_mcgs() {
    // width = cycles - 1 gives every W class a member referencing every
    // other W class, maximizing both the action cross product and the
    // reachable context subsets per added cycle class.
    let levels: Vec<Params> = (3..=14)
        .map(|c| Params {
            depth: 4,
            width: c - 1,
            cycles: c,
        })
        .collect();

    println!(
        "{:<6} {:<6} {:<6} {:>14} {:>12} {:>12} {:>10} {:>10}",
        "depth", "width", "cycles", "exact", "exact_size", "mcgs", "mcgs_size", "certified"
    );
    let mut crossed = false;
    for p in levels {
        let exact = run_exact_guarded(p, EXACT_TIMEOUT);
        let mut inst = build_instance(p);
        let mcgs = run_mcgs(&inst, MCGS_PLAYOUTS);
        let (exact_col, exact_size_col, timed_out) = match exact {
            ExactOutcome::Done { size, elapsed } => {
                (format!("{elapsed:.2?}"), size.to_string(), false)
            }
            ExactOutcome::Timeout => ("TIMEOUT(30s)".to_owned(), "-".to_owned(), true),
        };
        println!(
            "{:<6} {:<6} {:<6} {:>14} {:>12} {:>12.2?} {:>10} {:>10}",
            p.depth,
            p.width,
            p.cycles,
            exact_col,
            exact_size_col,
            mcgs.elapsed,
            mcgs.size,
            mcgs.certified
        );
        if let ExactOutcome::Done { size, .. } = exact {
            assert!(
                mcgs.size >= size,
                "level {p:?}: MCGS size {} beats the exact optimum {size}",
                mcgs.size
            );
        }
        assert_mcgs_answer_sane(&mut inst, &mcgs, &format!("level {p:?}"));
        if timed_out {
            crossed = true;
            break;
        }
    }
    if !crossed {
        println!(
            "no crossover: the exact solver finished every level within {EXACT_TIMEOUT:?}; \
             escalate `cycles` further to find the wall"
        );
    }
}

/// Cycle-complete root-Exact parity at cycles=10. Both the reference and
/// projection-pruned runs must complete at the same quality; predecessor
/// contextual-Exact timing and timeout thresholds are intentionally not part
/// of this contract. Run
/// with:
/// `cargo test -p semi-persistent-egraph --release --test au_scaling_crossover -- --ignored --nocapture root_exact_crossover_c10_pruning_parity`
#[test]
#[ignore = "manual acceptance measurement: run in release"]
fn root_exact_crossover_c10_pruning_parity() {
    let p = Params {
        depth: 4,
        width: 9,
        cycles: 10,
    };
    let reference = run_exact_guarded(p, EXACT_TIMEOUT);
    let pruned = run_exact_guarded_with(
        &format!("pruned-c{}k{}d{}", p.cycles, p.width, p.depth),
        move || build_instance(p),
        EXACT_TIMEOUT,
        true,
    );
    let ExactOutcome::Done {
        size: reference_size,
        elapsed: reference_elapsed,
    } = reference
    else {
        panic!("reference root Exact exceeded the {EXACT_TIMEOUT:?} guard");
    };
    let ExactOutcome::Done {
        size: pruned_size,
        elapsed: pruned_elapsed,
    } = pruned
    else {
        panic!("pruned root Exact exceeded the {EXACT_TIMEOUT:?} guard");
    };
    println!(
        "root Exact c10: reference size={reference_size} elapsed={reference_elapsed:.2?}; \
         pruned size={pruned_size} elapsed={pruned_elapsed:.2?}"
    );
    assert_eq!(pruned_size, reference_size);
}

/// Shared table columns for an exact outcome: (elapsed-or-TIMEOUT, size, timed_out).
fn exact_cols(outcome: &ExactOutcome) -> (String, String, bool) {
    match outcome {
        ExactOutcome::Done { size, elapsed } => (format!("{elapsed:.2?}"), size.to_string(), false),
        ExactOutcome::Timeout => ("TIMEOUT(30s)".to_owned(), "-".to_owned(), true),
    }
}

/// Render the crossover-level instance (depth=4, width=9, cycles=10 — the
/// first level where the exact solver exceeds the 30 s guard) in full: both
/// root terms as constructed, every merge applied, and the MCGS answer with
/// its variables' class-pair bindings. Run with:
/// `cargo test -p semi-persistent-egraph --release --test au_scaling_crossover -- --ignored --nocapture print_crossover_instance`
#[test]
#[ignore = "manual printer: renders the crossover instance and the MCGS answer"]
fn print_crossover_instance() {
    let p = Params {
        depth: 4,
        width: 9,
        cycles: 10,
    };
    let (mut inst, trace) = build_instance_traced(p);
    println!("crossover instance: {p:?}");
    println!(
        "left root class {} / right root class {}",
        inst.eg.find_const(inst.left),
        inst.eg.find_const(inst.right)
    );
    println!();
    println!("t1 (left root):");
    println!("{}", trace.left.pretty(72));
    println!();
    println!("t2 (right root):");
    println!("{}", trace.right.pretty(72));
    println!();
    println!("merges applied ({}):", trace.merges.len());
    for (a, b) in &trace.merges {
        println!("  merge({}, {})", a.flat(), b.flat());
    }
    println!();

    let result = {
        let snap = AuSnapshot::new(&inst.eg).unwrap();
        let start = Instant::now();
        let result = anti_unify(
            &snap,
            inst.left,
            inst.right,
            &AuConfig {
                algorithm: AuAlgorithm::Uct,
                playouts: MCGS_PLAYOUTS,
                ..Default::default()
            },
        )
        .unwrap();
        println!(
            "mcgs ({MCGS_PLAYOUTS} playouts): size={} certified={} elapsed={:?}",
            result.size,
            result.completion == Completion::Exact,
            start.elapsed()
        );
        result
    };

    let vars = collect_variant_nodes(&result.pool, result.term_id);
    println!();
    println!("generalization:");
    println!(
        "{}",
        term_to_sx(&inst.eg, &result.pool, result.term_id, &vars).pretty(72)
    );
    println!();
    println!("variables (left class / right class, repr = smallest member):");
    for (i, &var) in vars.iter().enumerate() {
        let arms = result.pool.children(var).to_vec();
        assert_eq!(arms.len(), 2, "Variants nodes are binary");
        let mut sides: Vec<String> = Vec::with_capacity(2);
        for &arm in &arms {
            let repr = term_to_sx(&inst.eg, &result.pool, arm, &vars).flat();
            // The arm is the class's smallest concrete representative
            // (terms.rs build_best_term); materialize it to name the class.
            let class = if result.pool.has_variants(arm) {
                "<non-concrete arm>".to_owned()
            } else {
                let owned = own_projected(&result.pool, arm);
                let node = materialize(&mut inst.eg, &owned);
                inst.eg.rebuild();
                inst.eg.find_const(node).to_string()
            };
            sides.push(format!("{class} repr {repr}"));
        }
        println!("  x{i}: left {} | right {}", sides[0], sides[1]);
    }
}

/// Escalating width-only sweep (acyclic, no self-wraps): only the per-level
/// same-op member cross product grows. Table format and stop rule follow
/// `scaling_sweep_exact_vs_mcgs` (stop after the first exact timeout, one
/// leaked worker max).
///
/// Measured 2026-08-15 (release, Apple Silicon): no crossover. With empty
/// contexts the per-OR memo collapses the path product as predicted; exact
/// grows about quadratically in `width` (11.8 ms at depth=4 width=64,
/// 2.18 s at depth=8 width=512) and MCGS tracks it slightly slower (2.35 s
/// at the top level), both dominated by the same `width^2` action
/// generation. Width alone does not separate the solvers. Run with:
/// `cargo test -p semi-persistent-egraph --release --test au_scaling_crossover -- --ignored --nocapture sweep_width_only`
#[test]
#[ignore = "manual sweep: escalates width until the exact solver exceeds a 30 s guard"]
fn sweep_width_only() {
    let levels: Vec<WidthParams> = [
        (4, 4),
        (4, 8),
        (4, 16),
        (4, 32),
        (4, 64),
        (6, 64),
        (8, 64),
        (8, 128),
        (8, 256),
        (8, 512),
    ]
    .into_iter()
    .map(|(depth, width)| WidthParams { depth, width })
    .collect();

    println!(
        "{:<6} {:<6} {:>14} {:>12} {:>12} {:>10} {:>10}",
        "depth", "width", "exact", "exact_size", "mcgs", "mcgs_size", "certified"
    );
    let mut crossed = false;
    for p in levels {
        let exact = run_exact_guarded_with(
            &format!("w-d{}k{}", p.depth, p.width),
            move || build_width_instance(p),
            EXACT_TIMEOUT,
            false,
        );
        let mut inst = build_width_instance(p);
        let mcgs = run_mcgs(&inst, MCGS_PLAYOUTS);
        let (exact_col, exact_size_col, timed_out) = exact_cols(&exact);
        println!(
            "{:<6} {:<6} {:>14} {:>12} {:>12.2?} {:>10} {:>10}",
            p.depth, p.width, exact_col, exact_size_col, mcgs.elapsed, mcgs.size, mcgs.certified
        );
        if let ExactOutcome::Done { size, .. } = exact {
            assert!(
                mcgs.size >= size,
                "level {p:?}: MCGS size {} beats the exact optimum {size}",
                mcgs.size
            );
        }
        assert_mcgs_answer_sane(&mut inst, &mcgs, &format!("level {p:?}"));
        if timed_out {
            crossed = true;
            break;
        }
    }
    if !crossed {
        println!(
            "no crossover: the exact solver finished every level within {EXACT_TIMEOUT:?}; \
             width alone does not blow the memoized state space up — this is the honest \
             ceiling of the family, not an under-escalated sweep"
        );
    }
}

/// Escalating AC-members sweep (one MSet class pair, acyclic): the
/// representation-pair product `members^2` and the per-pair transport matrix
/// `(children+1)^2` grow. Table format and stop rule follow
/// `scaling_sweep_exact_vs_mcgs`.
///
/// Measured 2026-08-15 (release, Apple Silicon): no crossover within the
/// ladder, and no separation. Exact stays under the guard through the top
/// level (28.3 s at members=256 children=32) while MCGS is consistently the
/// SLOWER solver (61.7 s at that level): MCGS enumerates the same
/// `members^2` representation pairs on expansion (mcgs.rs), so the product
/// hits both solvers alike. One rung further, (512, 32), was measured once
/// and dropped from the ladder as impractical for BOTH solvers: exact
/// exceeded the 30 s guard and MCGS did not finish within 25 minutes. Run
/// with:
/// `cargo test -p semi-persistent-egraph --release --test au_scaling_crossover -- --ignored --nocapture sweep_ac_members`
#[test]
#[ignore = "manual sweep: escalates AC member count until the exact solver exceeds a 30 s guard"]
fn sweep_ac_members() {
    let levels: Vec<AcParams> = [
        (4, 4),
        (8, 4),
        (16, 8),
        (32, 8),
        (64, 8),
        (64, 16),
        (128, 16),
        (256, 16),
        (256, 32),
    ]
    .into_iter()
    .map(|(members, children)| AcParams { members, children })
    .collect();

    println!(
        "{:<8} {:<8} {:>14} {:>12} {:>12} {:>10} {:>10}",
        "members", "children", "exact", "exact_size", "mcgs", "mcgs_size", "certified"
    );
    let mut crossed = false;
    for p in levels {
        let exact = run_exact_guarded_with(
            &format!("ac-m{}c{}", p.members, p.children),
            move || build_ac_instance(p),
            EXACT_TIMEOUT,
            false,
        );
        let mut inst = build_ac_instance(p);
        let mcgs = run_mcgs(&inst, MCGS_PLAYOUTS);
        let (exact_col, exact_size_col, timed_out) = exact_cols(&exact);
        println!(
            "{:<8} {:<8} {:>14} {:>12} {:>12.2?} {:>10} {:>10}",
            p.members,
            p.children,
            exact_col,
            exact_size_col,
            mcgs.elapsed,
            mcgs.size,
            mcgs.certified
        );
        if let ExactOutcome::Done { size, .. } = exact {
            assert!(
                mcgs.size >= size,
                "level {p:?}: MCGS size {} beats the exact optimum {size}",
                mcgs.size
            );
        }
        assert_mcgs_answer_sane(&mut inst, &mcgs, &format!("level {p:?}"));
        if timed_out {
            crossed = true;
            break;
        }
    }
    if !crossed {
        println!(
            "no crossover: the exact solver finished every level within {EXACT_TIMEOUT:?}, \
             and MCGS was the slower solver at every level — the members^2 \
             representation-pair product hits both solvers alike, so escalating further \
             (measured once at members=512 children=32: exact past the guard, MCGS still \
             running after 25 min) starves both and separates neither"
        );
    }
}
