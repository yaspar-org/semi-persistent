// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Anytime optimality-gap measurement of MCGS against the exact solver.
//!
//! One pilot run (`anytime_gap_pilot`, `#[ignore]`) generates instances in
//! three strata, obtains the exact optimum as ground truth, then runs MCGS
//! at an escalating playout ladder and records the (size, variant-mass) gap
//! and wall time per budget. Output: one CSV at
//! `$AU_BENCH_DIR/anytime_pilot.csv` (one row per kept instance x budget)
//! and a per-budget summary table on stdout.
//!
//! Strata:
//!
//! * `width` — `build_width_instance` from au_scaling_crossover.rs: acyclic
//!   spine, `width` same-op members per side per level, so every level-pair
//!   OR state fans out `width^2` zip actions. Exact cost grows about
//!   quadratically in `width`; MCGS pays the same action generation, so the
//!   gap-vs-budget curve is nontrivial for both. Levels: width in
//!   {64, 128, 256, 512} x depth in {4, 8, 12}, minus (12, 512) — cut for
//!   run-time budget: its MCGS ladder alone was projected past a minute.
//! * `ac` — `build_ac_instance` from au_scaling_crossover.rs: one MSet
//!   class pair with `members` monomial representations per side and
//!   `children` constants per member; both solvers enumerate the
//!   `members^2` representation-pair product. Mid params only
//!   (members <= 128, children <= 16): the measured 2026-08-15 sweep shows
//!   MCGS is SLOWER than exact above that, so higher rungs starve the
//!   ladder without adding gap information.
//! * `rand` — randomized mixed-amplification family, 30 seeded instances.
//!   A random backbone tree (leaves, unary, binary, one AC operator; the
//!   metamorphic generator's distribution from au_metamorphic.rs) has 2-4
//!   disjoint non-root positions replaced: "hot" positions pair two
//!   DISTINCT cyclic W classes left vs right, "diff" positions pair two
//!   side-local fresh constants. The W classes are the crossover family's
//!   shared-operator machinery (`merge(h(W_i), W_i)` self-wraps plus
//!   `merge(b(W_j, t_i), W_i)` cross links), so hot pairings ignite the
//!   cycle-context state space of the exact solver and give MCGS genuinely
//!   competitive same-operator pairings. Amplification is MIXED: those
//!   shared-op merges, plus metamorphic-style merges through per-merge
//!   fresh (rule-inert) unary operators — one self-wrap, two leaf merges.
//!
//! Skip rules (applied after the guarded exact run, before any MCGS run):
//!
//! * exact wall time < 200 ms — too easy; the anytime question is
//!   uninteresting where exact is effectively free;
//! * exact exceeds the 120 s guard — no ground truth. The worker thread is
//!   leaked (detached, still burning CPU) per the accepted pattern from
//!   au_scaling_crossover.rs; subsequent timings share the machine with it,
//!   which is one more reason the instance parameters above are tuned to
//!   make timeouts rare.
//!
//! Run-time containment (all documented at the consts below): each MCGS
//! budget run is guarded too (`MCGS_GUARD`) because a first pilot stalled
//! inside one MCGS call; on an MCGS timeout the instance's ladder stops and
//! its lower-budget rows are kept, so per-budget row counts can differ.
//! Instances are interleaved round-robin across the strata, no new instance
//! starts after `NEW_INSTANCE_CUTOFF`, and no new budget run after
//! `LADDER_CUTOFF`, so one pilot fits a 600 s foreground window; cut
//! instances are reported on stdout. The CSV is written incrementally (one
//! flushed line per row), so even a killed run leaves usable data.
//!
//! Determinism: MCGS has no random number generator — `McgsConfig` carries
//! no seed and mcgs.rs uses none outside its own tests — so one run per
//! (instance, budget) is the complete picture. Per-instance variation comes
//! entirely from instance generation (the `rand` stratum's seeds).
//!
//! Ground truth is the full lexicographic quality (size, variant_mass) from
//! `pool.quality`. The harness asserts MCGS never beats exact on that order
//! and that a `Completion::Exact` certificate implies quality equality.
//!
//! Measured 2026-08-15 (release, Apple Silicon), 206 s wall: 38 of 48
//! instances kept (width 4, ac 4, rand 30), 10 skipped as too easy, no
//! exact timeouts, no deadline cuts. MCGS returned the exact optimal
//! quality at EVERY budget on every kept instance — including a single
//! playout — while never certifying it (0/263 rows `Completion::Exact`),
//! and its median cost stayed 1e-4 to 4e-2 of the exact solver's. Three
//! ladders hit the 20 s MCGS guard at 4096 playouts (ac m64c16, width
//! d4w512, d8w512) after sub-second runs at 1024, reproducing the D1-style
//! stall that motivated the guard.
//!
//! Run with:
//! `cargo test -p semi-persistent-egraph --release --test au_anytime_bench -- --ignored --nocapture`

use std::fs;
use std::io::Write as _;
use std::path::PathBuf;
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;

type Eg = EGraph31<NiraLitVal, false, false>;

const EXACT_GUARD: Duration = Duration::from_secs(120);
const MIN_EXACT_MS: f64 = 200.0;
const BUDGETS: [u64; 7] = [1, 4, 16, 64, 256, 1024, 4096];
/// Per-budget MCGS guard. A first pilot run stalled inside ONE MCGS call
/// (ac m64c16 at 4096 playouts ran 60+ s where 1024 playouts took 0.56 s,
/// with a 1.7 GB peak footprint — the D1 hang signature, au-review.md
/// 2026-08-14), so MCGS runs get the same worker + recv_timeout guard as
/// exact. On timeout the instance's ladder stops (higher budgets are at
/// least as expensive) and the rows already collected are kept.
const MCGS_GUARD: Duration = Duration::from_secs(20);
/// Soft deadline: no NEW instance starts after this much pilot wall time,
/// so the run fits a bounded foreground window even if the random stratum
/// draws several exact timeouts. Instances cut this way are reported.
const NEW_INSTANCE_CUTOFF: Duration = Duration::from_secs(350);
/// Hard ladder cutoff: no new MCGS budget run starts after this.
const LADDER_CUTOFF: Duration = Duration::from_secs(520);

struct Instance {
    eg: Eg,
    left: ENodeId,
    right: ENodeId,
}

// ---------------------------------------------------------------------------
// Width family (au_scaling_crossover.rs `build_width_instance`): acyclic,
// `width` same-op members per class per side per level of a depth-`depth`
// spine, distinguished by per-level tag constants shared between the sides.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
struct WidthParams {
    depth: usize,
    width: usize,
}

fn build_width_instance(p: WidthParams) -> Instance {
    assert!(p.depth >= 1 && p.width >= 1);
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let b = eg.register_op2("b", sort, sort, sort);
    let cl_op = eg.register_op0("cl", sort);
    let cr_op = eg.register_op0("cr", sort);
    let mut left = eg.add(cl_op, &[]);
    let mut right = eg.add(cr_op, &[]);
    for level in 0..p.depth {
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
// AC family (au_scaling_crossover.rs `build_ac_instance`): one MSet class
// pair, `members` sliding-window monomials per side over a shared constant
// ring, plus a side marker.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
struct AcParams {
    members: usize,
    children: usize,
}

fn build_ac_instance(p: AcParams) -> Instance {
    assert!(p.members >= 1 && p.children >= 1);
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let m = eg.register_mset("m", sort, sort);
    let lmark_op = eg.register_op0("lmark", sort);
    let rmark_op = eg.register_op0("rmark", sort);
    let lmark = eg.add(lmark_op, &[]);
    let rmark = eg.add(rmark_op, &[]);
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
// Deterministic RNG (xorshift64*, from au_metamorphic.rs) and the random
// backbone generator.
// ---------------------------------------------------------------------------

struct XorShift64(u64);

impl XorShift64 {
    fn new(seed: u64) -> Self {
        XorShift64(seed | 1)
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

/// splitmix64: decorrelates consecutive loop indices into case seeds.
fn case_seed(base: u64, i: u64) -> u64 {
    let mut z = base.wrapping_add(i.wrapping_mul(0x9E3779B97F4A7C15));
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}

const N_LEAVES: usize = 6;
const N_UNARY: usize = 2;
const N_BINARY: usize = 2;
const MAX_DEPTH: usize = 5;

#[derive(Clone, PartialEq, Debug)]
enum Node {
    Leaf(usize),
    Unary(usize, Box<Node>),
    Binary(usize, Box<Node>, Box<Node>),
    MSet(Vec<Node>),
    /// Planted by mutation: the W class with this index. Never generated.
    Hub(usize),
    /// Planted by mutation: index into the per-instance fresh-constant
    /// table (left and right sides use disjoint indices). Never generated.
    Fresh(usize),
}

fn gen_tree(rng: &mut XorShift64, depth: usize) -> Node {
    let leaf_percent = [0, 15, 35, 55, 80, 100][depth.min(5)];
    if depth >= MAX_DEPTH || rng.below(100) < leaf_percent {
        return Node::Leaf(rng.below(N_LEAVES));
    }
    match rng.below(4) {
        0 => Node::Unary(rng.below(N_UNARY), Box::new(gen_tree(rng, depth + 1))),
        1 | 2 => Node::Binary(
            rng.below(N_BINARY),
            Box::new(gen_tree(rng, depth + 1)),
            Box::new(gen_tree(rng, depth + 1)),
        ),
        _ => Node::MSet(gen_distinct_children(rng, depth + 1)),
    }
}

fn gen_distinct_children(rng: &mut XorShift64, depth: usize) -> Vec<Node> {
    let target = 2 + rng.below(3);
    let mut out: Vec<Node> = Vec::new();
    for _ in 0..10 {
        if out.len() == target {
            break;
        }
        let c = gen_tree(rng, depth);
        if !out.contains(&c) {
            out.push(c);
        }
    }
    let mut li = 0;
    while out.len() < 2 {
        let c = Node::Leaf(li);
        li += 1;
        if !out.contains(&c) {
            out.push(c);
        }
    }
    out
}

/// Every position as a path of child indices, root included.
fn positions(node: &Node, prefix: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
    out.push(prefix.clone());
    let children: Vec<&Node> = match node {
        Node::Leaf(_) | Node::Hub(_) | Node::Fresh(_) => Vec::new(),
        Node::Unary(_, c) => vec![c.as_ref()],
        Node::Binary(_, a, b) => vec![a.as_ref(), b.as_ref()],
        Node::MSet(cs) => cs.iter().collect(),
    };
    for (i, c) in children.iter().enumerate() {
        prefix.push(i);
        positions(c, prefix, out);
        prefix.pop();
    }
}

fn replace_at(node: &Node, path: &[usize], replacement: &Node) -> Node {
    if path.is_empty() {
        return replacement.clone();
    }
    let (i, rest) = (path[0], &path[1..]);
    match node {
        Node::Leaf(_) | Node::Hub(_) | Node::Fresh(_) => {
            unreachable!("path descends below a leaf")
        }
        Node::Unary(op, c) => Node::Unary(*op, Box::new(replace_at(c, rest, replacement))),
        Node::Binary(op, a, b) => {
            if i == 0 {
                Node::Binary(*op, Box::new(replace_at(a, rest, replacement)), b.clone())
            } else {
                Node::Binary(*op, a.clone(), Box::new(replace_at(b, rest, replacement)))
            }
        }
        Node::MSet(cs) => Node::MSet(
            cs.iter()
                .enumerate()
                .map(|(j, c)| {
                    if j == i {
                        replace_at(c, rest, replacement)
                    } else {
                        c.clone()
                    }
                })
                .collect(),
        ),
    }
}

/// Non-root positions, shuffled, greedily filtered to pairwise
/// non-overlapping (no chosen position an ancestor of another).
fn choose_mutation_paths(rng: &mut XorShift64, tree: &Node, want: usize) -> Vec<Vec<usize>> {
    let mut all = Vec::new();
    positions(tree, &mut Vec::new(), &mut all);
    let mut candidates: Vec<Vec<usize>> = all.into_iter().filter(|p| !p.is_empty()).collect();
    for i in (1..candidates.len()).rev() {
        candidates.swap(i, rng.below(i + 1));
    }
    let mut chosen: Vec<Vec<usize>> = Vec::new();
    for p in candidates {
        if chosen.len() == want {
            break;
        }
        let overlaps = chosen.iter().any(|q| p.starts_with(q) || q.starts_with(&p));
        if !overlaps {
            chosen.push(p);
        }
    }
    chosen
}

// ---------------------------------------------------------------------------
// Random mixed-amplification builder.
// ---------------------------------------------------------------------------

struct RandSig {
    sort: semi_persistent_egraph::id::SortId,
    leaves: Vec<OpId>,
    unary: Vec<OpId>,
    binary: Vec<OpId>,
    mset: OpId,
    fresh: Vec<OpId>,
}

struct Built {
    nodes: Vec<ENodeId>,
    leaf_nodes: Vec<ENodeId>,
}

fn build_node(
    eg: &mut Eg,
    sig: &RandSig,
    hubs: &[ENodeId],
    node: &Node,
    acc: &mut Built,
) -> ENodeId {
    let id = match node {
        Node::Leaf(i) => eg.add(sig.leaves[*i], &[]),
        Node::Hub(i) => hubs[*i],
        Node::Fresh(i) => eg.add(sig.fresh[*i], &[]),
        Node::Unary(op, c) => {
            let cid = build_node(eg, sig, hubs, c, acc);
            eg.add(sig.unary[*op], &[cid])
        }
        Node::Binary(op, a, b) => {
            let aid = build_node(eg, sig, hubs, a, acc);
            let bid = build_node(eg, sig, hubs, b, acc);
            eg.add(sig.binary[*op], &[aid, bid])
        }
        Node::MSet(cs) => {
            let cids: Vec<ENodeId> = cs
                .iter()
                .map(|c| build_node(eg, sig, hubs, c, acc))
                .collect();
            eg.add(sig.mset, &cids)
        }
    };
    if matches!(node, Node::Leaf(_)) {
        acc.leaf_nodes.push(id);
    }
    if !matches!(node, Node::Hub(_)) {
        acc.nodes.push(id);
    }
    id
}

/// Human-readable parameters of one random instance, for the CSV.
struct RandDescr {
    cycles: usize,
    muts: usize,
    hot: usize,
}

fn build_random_instance(seed: u64) -> (Instance, RandDescr) {
    let mut rng = XorShift64::new(seed);
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let mut sig = RandSig {
        sort,
        leaves: (0..N_LEAVES)
            .map(|i| eg.register_op0(&format!("l{i}"), sort))
            .collect(),
        unary: (0..N_UNARY)
            .map(|i| eg.register_op1(&format!("u{i}"), sort, sort))
            .collect(),
        binary: (0..N_BINARY)
            .map(|i| eg.register_op2(&format!("f{i}"), sort, sort, sort))
            .collect(),
        mset: eg.register_mset("mplus", sort, sort),
        fresh: Vec::new(),
    };

    // Shared-op amplification: the crossover family's cyclic W classes.
    // `b(W_target, t_i)` is unique per (target, i), so congruence keeps the
    // classes distinct; every W reaches every other, so hot pairings drive
    // the exact solver's cycle-context product.
    let cycles = 8 + rng.below(2); // 8 or 9
    let b = eg.register_op2("b", sort, sort, sort);
    let h = eg.register_op1("h", sort, sort);
    let w: Vec<ENodeId> = (0..cycles)
        .map(|i| {
            let op = eg.register_op0(&format!("w{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    let tags: Vec<ENodeId> = (0..cycles)
        .map(|i| {
            let op = eg.register_op0(&format!("t{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    for &wi in &w {
        let hw = eg.add(h, &[wi]);
        eg.merge(hw, wi);
    }
    for (i, &tag) in tags.iter().enumerate() {
        for j in 1..cycles {
            let member = eg.add(b, &[w[(i + j) % cycles], tag]);
            eg.merge(member, w[i]);
        }
    }

    // Random backbone with 2-4 disjoint mutations, at most 3 of them hot
    // and at least one hot (a purely diff instance never ignites the W
    // state space and would only be skipped as too easy).
    let t = gen_tree(&mut rng, 0);
    let want = 2 + rng.below(3);
    let paths = choose_mutation_paths(&mut rng, &t, want);
    assert!(!paths.is_empty(), "seed {seed:#018x}: no mutable position");
    let mut left_t = t.clone();
    let mut right_t = t;
    let mut hot = 0usize;
    for (idx, p) in paths.iter().enumerate() {
        let make_hot = hot < 3 && (idx == 0 || rng.below(2) == 0);
        if make_hot {
            hot += 1;
            let i = rng.below(cycles);
            let j = (i + 1 + rng.below(cycles - 1)) % cycles;
            left_t = replace_at(&left_t, p, &Node::Hub(i));
            right_t = replace_at(&right_t, p, &Node::Hub(j));
        } else {
            let kl = eg.register_op0(&format!("kl{idx}"), sort);
            let kr = eg.register_op0(&format!("kr{idx}"), sort);
            let li = sig.fresh.len();
            sig.fresh.push(kl);
            sig.fresh.push(kr);
            left_t = replace_at(&left_t, p, &Node::Fresh(li));
            right_t = replace_at(&right_t, p, &Node::Fresh(li + 1));
        }
    }

    let mut acc = Built {
        nodes: Vec::new(),
        leaf_nodes: Vec::new(),
    };
    let left = build_node(&mut eg, &sig, &w, &left_t, &mut acc);
    let right = build_node(&mut eg, &sig, &w, &right_t, &mut acc);

    // Fresh-op (rule-inert) amplification, metamorphic style: one
    // self-wrap and two leaf merges through per-merge fresh unary
    // operators, so no two classes gain a shared operator from these.
    let mut amp_tag = 0usize;
    let fresh_unary = |eg: &mut Eg, amp_tag: &mut usize| {
        let op = eg.register_op1(&format!("amp{amp_tag}"), sig.sort, sig.sort);
        *amp_tag += 1;
        op
    };
    if !acc.nodes.is_empty() {
        let target = acc.nodes[rng.below(acc.nodes.len())];
        let op = fresh_unary(&mut eg, &mut amp_tag);
        let wrapped = eg.add(op, &[target]);
        eg.merge(wrapped, target);
        for _ in 0..2 {
            if acc.leaf_nodes.is_empty() {
                break;
            }
            let src = acc.nodes[rng.below(acc.nodes.len())];
            let leaf = acc.leaf_nodes[rng.below(acc.leaf_nodes.len())];
            let op = fresh_unary(&mut eg, &mut amp_tag);
            let member = eg.add(op, &[src]);
            eg.merge(member, leaf);
        }
    }
    eg.rebuild();

    (
        Instance { eg, left, right },
        RandDescr {
            cycles,
            muts: paths.len(),
            hot,
        },
    )
}

// ---------------------------------------------------------------------------
// Solver runners.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct ExactMeasurement {
    size: u32,
    vmass: u32,
    ms: f64,
}

enum ExactOutcome {
    Done(ExactMeasurement),
    Timeout,
}

/// Run the exact solver on a worker thread with a receive timeout (pattern
/// from au_scaling_crossover.rs `run_exact_guarded_with`); the builder runs
/// on the worker so a timeout abandons the build too. On timeout the worker
/// is leaked, detached and still running — the accepted pattern.
fn run_exact_guarded_with<F>(label: &str, build: F, timeout: Duration) -> ExactOutcome
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
                    ..Default::default()
                },
            )
            .unwrap();
            let elapsed = start.elapsed();
            let (size, vmass) = result.pool.quality(result.term_id);
            let _ = tx.send(ExactMeasurement {
                size,
                vmass,
                ms: elapsed.as_secs_f64() * 1e3,
            });
        })
        .unwrap();
    match rx.recv_timeout(timeout) {
        Ok(m) => ExactOutcome::Done(m),
        Err(mpsc::RecvTimeoutError::Timeout) => ExactOutcome::Timeout,
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("exact worker panicked for {label}; its message is above")
        }
    }
}

struct McgsMeasurement {
    size: u32,
    vmass: u32,
    certified: bool,
    ms: f64,
}

/// Run MCGS at one playout budget on a worker thread with a receive
/// timeout, same pattern as the exact guard: the builder runs on the worker
/// (deterministic, so every run sees the identical instance) and only the
/// `anti_unify` call is timed. `None` = guard expired; the worker is leaked.
fn run_mcgs_guarded(
    label: &str,
    build: std::sync::Arc<dyn Fn() -> Instance + Send + Sync>,
    playouts: u64,
    timeout: Duration,
) -> Option<McgsMeasurement> {
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .name(format!("au-mcgs-{label}-p{playouts}"))
        .spawn(move || {
            let inst = build();
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
            let (size, vmass) = result.pool.quality(result.term_id);
            let _ = tx.send(McgsMeasurement {
                size,
                vmass,
                certified: matches!(result.completion, Completion::Exact),
                ms: elapsed.as_secs_f64() * 1e3,
            });
        })
        .unwrap();
    match rx.recv_timeout(timeout) {
        Ok(m) => Some(m),
        Err(mpsc::RecvTimeoutError::Timeout) => None,
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("MCGS worker panicked for {label} p={playouts}; its message is above")
        }
    }
}

// ---------------------------------------------------------------------------
// The pilot.
// ---------------------------------------------------------------------------

/// One CSV row: a kept instance at one playout budget.
struct Row {
    instance_id: String,
    family: &'static str,
    params: String,
    exact: ExactMeasurement,
    playouts: u64,
    mcgs: McgsMeasurement,
}

/// One instance to measure: id, family, params string, and a shared builder
/// (called once on the exact worker thread and once on the main thread for
/// the MCGS ladder; every builder is deterministic).
struct Spec {
    id: String,
    family: &'static str,
    params: String,
    build: std::sync::Arc<dyn Fn() -> Instance + Send + Sync>,
}

/// All instances, interleaved round-robin across the three strata so a
/// deadline cut still leaves every stratum represented.
fn specs() -> Vec<Spec> {
    let mut width_specs: Vec<Spec> = Vec::new();
    let mut ac_specs: Vec<Spec> = Vec::new();
    let mut rand_specs: Vec<Spec> = Vec::new();
    let width_levels: &[(usize, usize)] = &[
        (4, 64),
        (8, 64),
        (12, 64),
        (4, 128),
        (8, 128),
        (12, 128),
        (4, 256),
        (8, 256),
        (12, 256),
        (4, 512),
        (8, 512),
    ];
    for (i, &(depth, width)) in width_levels.iter().enumerate() {
        width_specs.push(Spec {
            id: format!("width-{i:02}"),
            family: "width",
            params: format!("d{depth}w{width}"),
            build: std::sync::Arc::new(move || build_width_instance(WidthParams { depth, width })),
        });
    }
    let ac_levels: &[(usize, usize)] = &[
        (48, 8),
        (64, 8),
        (96, 8),
        (128, 8),
        (64, 12),
        (96, 12),
        (64, 16),
    ];
    for (i, &(members, children)) in ac_levels.iter().enumerate() {
        ac_specs.push(Spec {
            id: format!("ac-{i:02}"),
            family: "ac",
            params: format!("m{members}c{children}"),
            build: std::sync::Arc::new(move || build_ac_instance(AcParams { members, children })),
        });
    }
    const RAND_BASE: u64 = 0xA11F_00D5_EED0_2026;
    for i in 0..30u64 {
        let seed = case_seed(RAND_BASE, i);
        let (_, d) = build_random_instance(seed);
        rand_specs.push(Spec {
            id: format!("rand-{i:02}"),
            family: "rand",
            params: format!(
                "seed={seed:#018x};cycles={};muts={};hot={}",
                d.cycles, d.muts, d.hot
            ),
            build: std::sync::Arc::new(move || build_random_instance(seed).0),
        });
    }
    let mut out: Vec<Spec> = Vec::new();
    let mut iters = [
        width_specs.into_iter(),
        ac_specs.into_iter(),
        rand_specs.into_iter(),
    ];
    loop {
        let mut any = false;
        for it in &mut iters {
            if let Some(s) = it.next() {
                out.push(s);
                any = true;
            }
        }
        if !any {
            break;
        }
    }
    out
}

fn median(sorted: &[f64]) -> f64 {
    let n = sorted.len();
    if n % 2 == 1 {
        sorted[n / 2]
    } else {
        (sorted[n / 2 - 1] + sorted[n / 2]) / 2.0
    }
}

#[test]
#[ignore = "manual pilot: ~10 min of release-mode measurement, writes $AU_BENCH_DIR/anytime_pilot.csv"]
fn anytime_gap_pilot() {
    let bench_dir = std::env::var("AU_BENCH_DIR")
        .expect("set AU_BENCH_DIR to the directory that receives anytime_pilot.csv");
    fs::create_dir_all(&bench_dir).unwrap();
    let csv_path = PathBuf::from(&bench_dir).join("anytime_pilot.csv");

    // Incremental CSV: header now, one flushed line per row, so a killed
    // run still leaves a usable file.
    let mut csv = fs::File::create(&csv_path).unwrap();
    csv.write_all(
        b"instance_id,family,params,exact_ms,exact_size,exact_vmass,playouts,mcgs_ms,mcgs_size,mcgs_vmass,certified\n",
    )
    .unwrap();

    let pilot_start = Instant::now();
    let mut rows: Vec<Row> = Vec::new();
    let mut kept: Vec<(String, &'static str, f64)> = Vec::new();
    let mut skipped_easy = 0usize;
    let mut skipped_timeout = 0usize;
    let mut mcgs_timeouts = 0usize;
    let mut deadline_cut = 0usize;

    for spec in specs() {
        let Spec {
            id,
            family,
            params,
            build,
        } = spec;
        if pilot_start.elapsed() > NEW_INSTANCE_CUTOFF {
            deadline_cut += 1;
            println!("{id} [{family} {params}]: CUT (past the {NEW_INSTANCE_CUTOFF:?} deadline)");
            continue;
        }
        let b_worker = std::sync::Arc::clone(&build);
        let exact_m = match run_exact_guarded_with(&id, move || b_worker(), EXACT_GUARD) {
            ExactOutcome::Done(m) => {
                if m.ms < MIN_EXACT_MS {
                    println!(
                        "{id} [{family} {params}]: exact {:.1} ms — SKIP (too easy)",
                        m.ms
                    );
                    skipped_easy += 1;
                    continue;
                }
                println!(
                    "{id} [{family} {params}]: exact {:.1} ms, optimum ({}, {})",
                    m.ms, m.size, m.vmass
                );
                m
            }
            ExactOutcome::Timeout => {
                println!(
                    "{id} [{family} {params}]: exact TIMEOUT({EXACT_GUARD:?}) — SKIP \
                     (no ground truth; worker leaked)"
                );
                skipped_timeout += 1;
                continue;
            }
        };
        kept.push((id.clone(), family, exact_m.ms));

        for &playouts in &BUDGETS {
            if pilot_start.elapsed() > LADDER_CUTOFF {
                println!(
                    "  {id}: ladder stopped at p={playouts} (past the {LADDER_CUTOFF:?} cutoff)"
                );
                break;
            }
            let Some(mcgs) =
                run_mcgs_guarded(&id, std::sync::Arc::clone(&build), playouts, MCGS_GUARD)
            else {
                mcgs_timeouts += 1;
                println!(
                    "  {id} p={playouts}: MCGS TIMEOUT({MCGS_GUARD:?}) — ladder stopped \
                     (worker leaked; rows below this budget kept)"
                );
                break;
            };
            assert!(
                (mcgs.size, mcgs.vmass) >= (exact_m.size, exact_m.vmass),
                "{id}: MCGS quality ({}, {}) beats the exact optimum ({}, {}); \
                 exact optimality is broken",
                mcgs.size,
                mcgs.vmass,
                exact_m.size,
                exact_m.vmass
            );
            if mcgs.certified {
                assert_eq!(
                    (mcgs.size, mcgs.vmass),
                    (exact_m.size, exact_m.vmass),
                    "{id}: MCGS reports Completion::Exact away from the optimum; \
                     the certificate is unsound"
                );
            }
            println!(
                "  {id} p={playouts}: {:.1} ms, ({}, {}), certified={}",
                mcgs.ms, mcgs.size, mcgs.vmass, mcgs.certified
            );
            let row = Row {
                instance_id: id.clone(),
                family,
                params: params.clone(),
                exact: exact_m,
                playouts,
                mcgs,
            };
            csv.write_all(
                format!(
                    "{},{},{},{:.3},{},{},{},{:.3},{},{},{}\n",
                    row.instance_id,
                    row.family,
                    row.params,
                    row.exact.ms,
                    row.exact.size,
                    row.exact.vmass,
                    row.playouts,
                    row.mcgs.ms,
                    row.mcgs.size,
                    row.mcgs.vmass,
                    row.mcgs.certified
                )
                .as_bytes(),
            )
            .unwrap();
            csv.flush().unwrap();
            rows.push(row);
        }
    }

    println!();
    println!("wrote {} data rows to {}", rows.len(), csv_path.display());
    println!(
        "instances: kept {}, skipped {} too-easy, {} exact-timeout, {} deadline-cut; \
         {} MCGS budget timeouts",
        kept.len(),
        skipped_easy,
        skipped_timeout,
        deadline_cut,
        mcgs_timeouts
    );
    if !kept.is_empty() {
        let mut times: Vec<f64> = kept.iter().map(|k| k.2).collect();
        times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!(
            "exact ms over kept instances: min {:.1}, median {:.1}, max {:.1}",
            times[0],
            median(&times),
            times[times.len() - 1]
        );
    }

    // Per-budget summary.
    println!();
    println!(
        "{:>8} {:>4} {:>10} {:>14} {:>10} {:>16}",
        "playouts", "n", "gap0_frac", "mean_rel_gap>0", "cert_frac", "med_ms_ratio"
    );
    for &playouts in &BUDGETS {
        let at: Vec<&Row> = rows.iter().filter(|r| r.playouts == playouts).collect();
        if at.is_empty() {
            continue;
        }
        let n = at.len();
        let zero = at.iter().filter(|r| r.mcgs.size == r.exact.size).count();
        let nonzero_gaps: Vec<f64> = at
            .iter()
            .filter(|r| r.mcgs.size > r.exact.size)
            .map(|r| f64::from(r.mcgs.size - r.exact.size) / f64::from(r.exact.size))
            .collect();
        let mean_rel = if nonzero_gaps.is_empty() {
            f64::NAN
        } else {
            nonzero_gaps.iter().sum::<f64>() / nonzero_gaps.len() as f64
        };
        let certified = at.iter().filter(|r| r.mcgs.certified).count();
        let mut ratios: Vec<f64> = at.iter().map(|r| r.mcgs.ms / r.exact.ms).collect();
        ratios.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!(
            "{:>8} {:>4} {:>10.3} {:>14.3} {:>10.3} {:>16.4}",
            playouts,
            n,
            zero as f64 / n as f64,
            mean_rel,
            certified as f64 / n as f64,
            median(&ratios)
        );
    }
}
