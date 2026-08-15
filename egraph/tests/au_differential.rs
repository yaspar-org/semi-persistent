// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Differential gate for the AU solver work plan (doc/au-solver-plan.md).
//!
//! Every solver change on the plan (A0-A7) is compared against the current
//! solvers: the exhaustive uninformed exact search (no pruning, no ordering)
//! and the current MCGS. This harness pins their outputs on a deterministic
//! corpus as a committed golden fixture,
//! `tests/au_golden/differential.txt`; a change re-runs the harness and
//! accounts for every fixture line it moves.
//!
//! Corpus (stable order, one entry per instance and solver run):
//!
//! * `meta-NNN`: seeded metamorphic instances — random ground term,
//!   fresh-constant mutations at disjoint positions, amplification merges —
//!   the generator of au_metamorphic.rs with base seed
//!   `0xD1FF_E4E7_0000_0001` (this file's own constant, distinct from the
//!   metamorphic suite's, so the two corpora stay independent).
//! * `xover cN`: the cyclic-class family of au_scaling_crossover.rs at
//!   depth 4, width N-1, cycles 2..=6.
//! * `width dD wW`: the acyclic width family at depth 4, width 4/16/64.
//! * `ac mM cC`: the AC-members family at (8,4), (16,8), (32,8).
//!
//! Per instance, one snapshot serves three runs: exact, MCGS at 16 playouts,
//! MCGS at 256. Each run yields one fixture line with the quality tuple —
//! `size` and `vmass` (the lexicographic key the solvers minimize), plus
//! `certified` for MCGS. The harness additionally asserts, per instance:
//! the exact term's two projections materialize back into the source
//! classes; MCGS never beats the exact size; a `Completion::Exact`
//! certificate implies the exact quality tuple.
//!
//! Modes:
//!
//! * default (check): `differential_matches_golden` regenerates the full
//!   corpus and asserts it byte-identical to the committed fixture. No
//!   debug/release split is needed: the whole corpus runs in about 10 s
//!   debug and 1 s release (measured 2026-08-15, Apple Silicon), so the
//!   full check is non-ignored and part of the normal debug suite.
//! * `AU_GOLDEN=write` regenerates the fixture from the full corpus
//!   (generated twice in-process and asserted identical first):
//!   `AU_GOLDEN=write cargo test -p semi-persistent-egraph --release --test au_differential differential_matches_golden -- --nocapture`
//!
//! Protocol for solver changes gated on this fixture:
//!
//! * Pure data-structure or representation changes (e.g. A0's descriptor
//!   clone) keep the fixture bit-identical.
//! * Ordering and heuristic changes (A3) keep every `exact` line identical
//!   — the exact value is a min, and a min is order-invariant; changed
//!   `mcgs` lines require explicit review and a regenerated fixture in the
//!   same commit.
//! * Pruning changes (A2, A5, A6) additionally run flag-off vs flag-on in
//!   their own suites and assert equal exact quality tuples; this fixture
//!   then pins the flag-on outputs.
//!
//! `determinism_self_check` builds the corpus twice in-process and asserts
//! the generated fixture text is identical; the write path performs the
//! same double build before writing.

use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};
use std::{env, fs};

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{
    AuAlgorithm, AuConfig, AuResult, Completion, anti_unify,
};
use semi_persistent_egraph::au::terms::{TermId, TermOp, TermPool};
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::nodes::LitValId;

type Eg = EGraph31<NiraLitVal, false, false>;

// ---------------------------------------------------------------------------
// Corpus knobs.
// ---------------------------------------------------------------------------

/// Base seed of the metamorphic stratum. Documented in the module doc; the
/// fixture depends on it, so changing it regenerates every `meta` line.
const BASE_SEED: u64 = 0xD1FF_E4E7_0000_0001;
/// Metamorphic instances in the corpus.
const META_FULL: u64 = 200;
/// MCGS playout budgets run per instance, in fixture order.
const PLAYOUT_BUDGETS: [u64; 2] = [16, 256];
/// Per-instance guard (worker thread + recv_timeout, pattern from
/// au_metamorphic.rs `run_case_guarded`): a hang fails the test naming the
/// instance instead of wedging the harness; the worker leaks.
const INSTANCE_TIMEOUT: Duration = Duration::from_secs(120);

fn golden_path() -> std::path::PathBuf {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/au_golden/differential.txt")
}

fn write_mode() -> bool {
    env::var("AU_GOLDEN").as_deref() == Ok("write")
}

const REGEN_HINT: &str = "regenerate with: AU_GOLDEN=write cargo test -p semi-persistent-egraph \
     --release --test au_differential differential_matches_golden -- --nocapture";

// ---------------------------------------------------------------------------
// Deterministic RNG (xorshift64*), as in au_metamorphic.rs.
// ---------------------------------------------------------------------------

struct XorShift64(u64);

impl XorShift64 {
    fn new(seed: u64) -> Self {
        // xorshift has no fixed point other than 0; keep the state nonzero.
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

// ---------------------------------------------------------------------------
// Metamorphic generator (au_metamorphic.rs, unchanged semantics): ground
// trees over leaves, unary/binary free operators, one mset and one set
// operator; canonical AC normalization; disjoint fresh-constant mutations;
// amplification merges through per-merge fresh unary operators.
// ---------------------------------------------------------------------------

const N_LEAVES: usize = 6;
const N_UNARY: usize = 2;
const N_BINARY: usize = 2;
const MAX_DEPTH: usize = 5;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Node {
    Leaf(usize),
    Fresh(usize),
    Unary(usize, Box<Node>),
    Binary(usize, Box<Node>, Box<Node>),
    MSet(Vec<Node>),
    Set(Vec<Node>),
}

fn gen_tree(rng: &mut XorShift64, depth: usize) -> Node {
    let leaf_percent = [0, 15, 35, 55, 80, 100][depth.min(5)];
    if depth >= MAX_DEPTH || rng.below(100) < leaf_percent {
        return Node::Leaf(rng.below(N_LEAVES));
    }
    match rng.below(4) {
        0 => Node::Unary(rng.below(N_UNARY), Box::new(gen_tree(rng, depth + 1))),
        1 => Node::Binary(
            rng.below(N_BINARY),
            Box::new(gen_tree(rng, depth + 1)),
            Box::new(gen_tree(rng, depth + 1)),
        ),
        2 => Node::MSet(gen_distinct_children(rng, depth + 1)),
        _ => Node::Set(gen_distinct_children(rng, depth + 1)),
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

/// Canonical AC form on trees: flatten nested same-operator occurrences,
/// dedupe set children, collapse singleton variadics, sort children.
fn normalize(node: &Node) -> Node {
    match node {
        Node::Leaf(_) | Node::Fresh(_) => node.clone(),
        Node::Unary(op, c) => Node::Unary(*op, Box::new(normalize(c))),
        Node::Binary(op, a, b) => Node::Binary(*op, Box::new(normalize(a)), Box::new(normalize(b))),
        Node::MSet(cs) => {
            let mut out = Vec::new();
            for c in cs {
                match normalize(c) {
                    Node::MSet(inner) => out.extend(inner),
                    other => out.push(other),
                }
            }
            out.sort();
            if out.len() == 1 {
                out.pop().unwrap()
            } else {
                Node::MSet(out)
            }
        }
        Node::Set(cs) => {
            let mut out: Vec<Node> = Vec::new();
            for c in cs {
                match normalize(c) {
                    Node::Set(inner) => out.extend(inner),
                    other => out.push(other),
                }
            }
            out.sort();
            out.dedup();
            if out.len() == 1 {
                out.pop().unwrap()
            } else {
                Node::Set(out)
            }
        }
    }
}

fn positions(node: &Node, prefix: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
    out.push(prefix.clone());
    let children: Vec<&Node> = match node {
        Node::Leaf(_) | Node::Fresh(_) => Vec::new(),
        Node::Unary(_, c) => vec![c.as_ref()],
        Node::Binary(_, a, b) => vec![a.as_ref(), b.as_ref()],
        Node::MSet(cs) | Node::Set(cs) => cs.iter().collect(),
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
        Node::Leaf(_) | Node::Fresh(_) => unreachable!("path descends below a leaf"),
        Node::Unary(op, c) => Node::Unary(*op, Box::new(replace_at(c, rest, replacement))),
        Node::Binary(op, a, b) => {
            if i == 0 {
                Node::Binary(*op, Box::new(replace_at(a, rest, replacement)), b.clone())
            } else {
                Node::Binary(*op, a.clone(), Box::new(replace_at(b, rest, replacement)))
            }
        }
        Node::MSet(cs) => Node::MSet(replace_child(cs, i, rest, replacement)),
        Node::Set(cs) => Node::Set(replace_child(cs, i, rest, replacement)),
    }
}

fn replace_child(cs: &[Node], i: usize, rest: &[usize], replacement: &Node) -> Vec<Node> {
    cs.iter()
        .enumerate()
        .map(|(j, c)| {
            if j == i {
                replace_at(c, rest, replacement)
            } else {
                c.clone()
            }
        })
        .collect()
}

/// Non-root positions, shuffled, greedily filtered to pairwise disjoint.
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

struct Sig {
    sort: semi_persistent_egraph::id::SortId,
    leaves: Vec<OpId>,
    unary: Vec<OpId>,
    binary: Vec<OpId>,
    mset: OpId,
    set: OpId,
    fresh: Vec<OpId>,
}

fn register_signature(eg: &mut Eg) -> Sig {
    let sort = eg.intern_sort("S");
    Sig {
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
        set: eg.register_set("sand", sort, sort),
        fresh: Vec::new(),
    }
}

struct Built {
    nodes: Vec<ENodeId>,
    leaf_nodes: Vec<ENodeId>,
    unary_edges: Vec<(ENodeId, ENodeId)>,
}

fn build_tree(eg: &mut Eg, sig: &Sig, node: &Node, acc: &mut Built) -> ENodeId {
    let id = match node {
        Node::Leaf(i) => eg.add(sig.leaves[*i], &[]),
        Node::Fresh(i) => eg.add(sig.fresh[*i], &[]),
        Node::Unary(op, c) => {
            let cid = build_tree(eg, sig, c, acc);
            let id = eg.add(sig.unary[*op], &[cid]);
            acc.unary_edges.push((id, cid));
            id
        }
        Node::Binary(op, a, b) => {
            let aid = build_tree(eg, sig, a, acc);
            let bid = build_tree(eg, sig, b, acc);
            eg.add(sig.binary[*op], &[aid, bid])
        }
        Node::MSet(cs) => {
            let cids: Vec<ENodeId> = cs.iter().map(|c| build_tree(eg, sig, c, acc)).collect();
            eg.add(sig.mset, &cids)
        }
        Node::Set(cs) => {
            let cids: Vec<ENodeId> = cs.iter().map(|c| build_tree(eg, sig, c, acc)).collect();
            eg.add(sig.set, &cids)
        }
    };
    if matches!(node, Node::Leaf(_)) {
        acc.leaf_nodes.push(id);
    }
    acc.nodes.push(id);
    id
}

/// Amplification merges through per-merge fresh unary operators; none lowers
/// a class's minimal term size (argument in au_metamorphic.rs).
fn amplify(eg: &mut Eg, sig: &Sig, rng: &mut XorShift64, acc: &Built, tag: &mut usize) {
    let fresh_unary = |eg: &mut Eg, tag: &mut usize| {
        let op = eg.register_op1(&format!("amp{tag}"), sig.sort, sig.sort);
        *tag += 1;
        op
    };

    for _ in 0..(1 + acc.nodes.len() / 6) {
        let w = acc.nodes[rng.below(acc.nodes.len())];
        let h = fresh_unary(eg, tag);
        let hw = eg.add(h, &[w]);
        eg.merge(hw, w);
    }

    for _ in 0..2 {
        let w = acc.nodes[rng.below(acc.nodes.len())];
        let leaf = acc.leaf_nodes[rng.below(acc.leaf_nodes.len())];
        let h = fresh_unary(eg, tag);
        let hw = eg.add(h, &[w]);
        eg.merge(hw, leaf);
    }

    if !acc.unary_edges.is_empty() {
        let (p, c) = acc.unary_edges[rng.below(acc.unary_edges.len())];
        let h = fresh_unary(eg, tag);
        let hc = eg.add(h, &[c]);
        eg.merge(hc, p);
    }
}

// ---------------------------------------------------------------------------
// Instances.
// ---------------------------------------------------------------------------

struct Instance {
    eg: Eg,
    left: ENodeId,
    right: ENodeId,
}

/// One metamorphic instance: the seed drives generation exactly as in
/// au_metamorphic.rs `run_case`, minus the oracle assertions (the
/// metamorphic suite owns those; here the fixture pins the outputs).
fn build_meta(seed: u64) -> Instance {
    let mut rng = XorShift64::new(seed);
    let mut eg = Eg::new();
    let mut sig = register_signature(&mut eg);

    let t = normalize(&gen_tree(&mut rng, 0));
    let want = 1 + rng.below(4);
    let paths = choose_mutation_paths(&mut rng, &t, want);
    assert!(!paths.is_empty(), "seed {seed:#018x}: no mutable position");

    sig.fresh = (0..paths.len())
        .map(|i| eg.register_op0(&format!("km{i}"), sig.sort))
        .collect();
    let mut mutant = t.clone();
    for (i, p) in paths.iter().enumerate() {
        mutant = replace_at(&mutant, p, &Node::Fresh(i));
    }

    let mut acc = Built {
        nodes: Vec::new(),
        leaf_nodes: Vec::new(),
        unary_edges: Vec::new(),
    };
    let left = build_tree(&mut eg, &sig, &t, &mut acc);
    let right = build_tree(&mut eg, &sig, &mutant, &mut acc);
    let mut amp_tag = 0;
    amplify(&mut eg, &sig, &mut rng, &acc, &mut amp_tag);
    eg.rebuild();
    Instance { eg, left, right }
}

/// Cyclic-class family of au_scaling_crossover.rs `build_instance` at
/// depth 4, width cycles-1 (the sweep's shape), tracing stripped.
fn build_crossover(cycles: usize) -> Instance {
    assert!(cycles >= 2, "hot leaves need two distinct W classes");
    let depth = 4usize;
    let width = cycles - 1;
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let f = eg.register_op2("f", sort, sort, sort);
    let b = eg.register_op2("b", sort, sort, sort);
    let h = eg.register_op1("h", sort, sort);
    let p_op = eg.register_op0("p", sort);
    let dl_op = eg.register_op0("dl", sort);
    let dr_op = eg.register_op0("dr", sort);
    let w_ops: Vec<OpId> = (0..cycles)
        .map(|i| eg.register_op0(&format!("w{i}"), sort))
        .collect();
    let tag_ops: Vec<OpId> = (0..cycles)
        .map(|i| eg.register_op0(&format!("t{i}"), sort))
        .collect();

    let w: Vec<ENodeId> = w_ops.iter().map(|&op| eg.add(op, &[])).collect();
    let tags: Vec<ENodeId> = tag_ops.iter().map(|&op| eg.add(op, &[])).collect();
    for &wi in &w {
        let hw = eg.add(h, &[wi]);
        eg.merge(hw, wi);
    }
    let fan = width.min(cycles - 1);
    for (i, &tag) in tags.iter().enumerate() {
        for j in 1..=fan {
            let target = w[(i + j) % cycles];
            let member = eg.add(b, &[target, tag]);
            eg.merge(member, w[i]);
        }
    }
    eg.rebuild();

    let shared = eg.add(p_op, &[]);
    let dl = eg.add(dl_op, &[]);
    let dr = eg.add(dr_op, &[]);
    let n_leaves = 1usize << depth;
    let mut left_level: Vec<ENodeId> = Vec::with_capacity(n_leaves);
    let mut right_level: Vec<ENodeId> = Vec::with_capacity(n_leaves);
    for t in 0..n_leaves {
        match t % 4 {
            0 => {
                left_level.push(w[t % cycles]);
                right_level.push(w[(t + 1) % cycles]);
            }
            2 => {
                left_level.push(dl);
                right_level.push(dr);
            }
            _ => {
                left_level.push(shared);
                right_level.push(shared);
            }
        }
    }
    while left_level.len() > 1 {
        left_level = left_level.chunks(2).map(|c| eg.add(f, c)).collect();
        right_level = right_level.chunks(2).map(|c| eg.add(f, c)).collect();
    }
    eg.rebuild();
    Instance {
        eg,
        left: left_level[0],
        right: right_level[0],
    }
}

/// Acyclic width family of au_scaling_crossover.rs `build_width_instance`.
fn build_width(depth: usize, width: usize) -> Instance {
    assert!(depth >= 1 && width >= 1);
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let b = eg.register_op2("b", sort, sort, sort);
    let cl_op = eg.register_op0("cl", sort);
    let cr_op = eg.register_op0("cr", sort);
    let mut left = eg.add(cl_op, &[]);
    let mut right = eg.add(cr_op, &[]);
    for level in 0..depth {
        let tags: Vec<ENodeId> = (0..width)
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

/// AC-members family of au_scaling_crossover.rs `build_ac_instance`.
fn build_ac(members: usize, children: usize) -> Instance {
    assert!(members >= 1 && children >= 1);
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let m = eg.register_mset("m", sort, sort);
    let lmark_op = eg.register_op0("lmark", sort);
    let rmark_op = eg.register_op0("rmark", sort);
    let lmark = eg.add(lmark_op, &[]);
    let rmark = eg.add(rmark_op, &[]);
    let ring = members + children;
    let cs: Vec<ENodeId> = (0..ring)
        .map(|i| {
            let op = eg.register_op0(&format!("c{i}"), sort);
            eg.add(op, &[])
        })
        .collect();
    let left = add_ac_side(&mut eg, m, lmark, &cs, members, children);
    let right = add_ac_side(&mut eg, m, rmark, &cs, members, children);
    eg.rebuild();
    Instance { eg, left, right }
}

fn add_ac_side(
    eg: &mut Eg,
    m: OpId,
    mark: ENodeId,
    cs: &[ENodeId],
    members: usize,
    children: usize,
) -> ENodeId {
    let mems: Vec<ENodeId> = (0..members)
        .map(|i| {
            let mut kids = Vec::with_capacity(children + 1);
            kids.push(mark);
            for j in 0..children {
                kids.push(cs[(i + j) % cs.len()]);
            }
            eg.add(m, &kids)
        })
        .collect();
    for &member in &mems[1..] {
        eg.merge(member, mems[0]);
    }
    mems[0]
}

// ---------------------------------------------------------------------------
// Corpus specification.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
enum Spec {
    Meta { index: u64, seed: u64 },
    Crossover { cycles: usize },
    Width { depth: usize, width: usize },
    Ac { members: usize, children: usize },
}

impl Spec {
    /// Fixture key prefix: identifies the instance, stable across runs.
    fn id(self) -> String {
        match self {
            Spec::Meta { index, seed } => format!("meta-{index:03} seed={seed:#018x}"),
            Spec::Crossover { cycles } => format!("xover c{cycles} d4 w{}", cycles - 1),
            Spec::Width { depth, width } => format!("width d{depth} w{width}"),
            Spec::Ac { members, children } => format!("ac m{members} c{children}"),
        }
    }

    fn build(self) -> Instance {
        match self {
            Spec::Meta { seed, .. } => build_meta(seed),
            Spec::Crossover { cycles } => build_crossover(cycles),
            Spec::Width { depth, width } => build_width(depth, width),
            Spec::Ac { members, children } => build_ac(members, children),
        }
    }
}

fn meta_specs(n: u64) -> Vec<Spec> {
    (0..n)
        .map(|i| Spec::Meta {
            index: i,
            seed: case_seed(BASE_SEED, i),
        })
        .collect()
}

fn family_specs() -> Vec<Spec> {
    let mut out: Vec<Spec> = (2..=6).map(|cycles| Spec::Crossover { cycles }).collect();
    out.extend([4, 16, 64].map(|width| Spec::Width { depth: 4, width }));
    out.extend(
        [(8, 4), (16, 8), (32, 8)].map(|(members, children)| Spec::Ac { members, children }),
    );
    out
}

fn full_specs() -> Vec<Spec> {
    let mut out = meta_specs(META_FULL);
    out.extend(family_specs());
    out
}

// ---------------------------------------------------------------------------
// Projection helpers (pattern from au_metamorphic.rs check_pair).
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
// Running one instance: exact + MCGS per budget on one snapshot, projection
// validity on the exact term, cross-solver soundness assertions, fixture
// lines as (key, value) pairs.
// ---------------------------------------------------------------------------

fn run_spec(spec: Spec) -> Vec<(String, String)> {
    let id = spec.id();
    let mut inst = spec.build();

    let (exact_quality, exact_projs, mcgs_rows) = {
        let snap = AuSnapshot::new(&inst.eg).unwrap();

        let exact = anti_unify(
            &snap,
            inst.left,
            inst.right,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
        )
        .unwrap();
        let exact_quality = (exact.size, exact.pool.variant_mass(exact.term_id));
        let exact_projs = projected_terms(exact);

        let mcgs_rows: Vec<(u64, u32, u32, bool)> = PLAYOUT_BUDGETS
            .iter()
            .map(|&playouts| {
                let mcgs = anti_unify(
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
                (
                    playouts,
                    mcgs.size,
                    mcgs.pool.variant_mass(mcgs.term_id),
                    mcgs.completion == Completion::Exact,
                )
            })
            .collect();

        (exact_quality, exact_projs, mcgs_rows)
    };

    // Projection validity on the exact term: both projections materialize
    // back into their source classes (au_metamorphic.rs check_pair).
    let (lp, rp) = &exact_projs;
    let pl = materialize(&mut inst.eg, lp);
    let pr = materialize(&mut inst.eg, rp);
    inst.eg.rebuild();
    assert_eq!(
        inst.eg.find_const(pl),
        inst.eg.find_const(inst.left),
        "{id}: exact left projection does not re-evaluate into the left class"
    );
    assert_eq!(
        inst.eg.find_const(pr),
        inst.eg.find_const(inst.right),
        "{id}: exact right projection does not re-evaluate into the right class"
    );

    let mut out = vec![(
        format!("{id} exact"),
        format!("size={} vmass={}", exact_quality.0, exact_quality.1),
    )];
    for (playouts, size, vmass, certified) in mcgs_rows {
        assert!(
            size >= exact_quality.0,
            "{id}: MCGS at {playouts} playouts reports size {size}, beating the exact optimum \
             {}; exact optimality is broken",
            exact_quality.0
        );
        if certified {
            assert_eq!(
                (size, vmass),
                exact_quality,
                "{id}: MCGS at {playouts} playouts reports Completion::Exact at quality \
                 ({size}, {vmass}) but the optimum is {exact_quality:?}; the certificate is \
                 unsound"
            );
        }
        out.push((
            format!("{id} mcgs p{playouts}"),
            format!(
                "size={size} vmass={vmass} certified={}",
                if certified { "yes" } else { "no" }
            ),
        ));
    }
    out
}

/// Worker-thread guard (au_metamorphic.rs `run_case_guarded`): a hang fails
/// the test naming the instance; the worker thread leaks, still spinning.
fn run_spec_guarded(spec: Spec) -> Vec<(String, String)> {
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .name(format!("au-diff-{}", spec.id().replace(' ', "-")))
        .spawn(move || {
            let _ = tx.send(run_spec(spec));
        })
        .unwrap();
    match rx.recv_timeout(INSTANCE_TIMEOUT) {
        Ok(lines) => lines,
        Err(mpsc::RecvTimeoutError::Timeout) => panic!(
            "{}: instance exceeded {INSTANCE_TIMEOUT:?}; the worker thread is leaked",
            spec.id()
        ),
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!(
                "{}: instance worker panicked, its message is above",
                spec.id()
            )
        }
    }
}

fn corpus_pairs(specs: &[Spec]) -> Vec<(String, String)> {
    specs.iter().flat_map(|&s| run_spec_guarded(s)).collect()
}

fn render(pairs: &[(String, String)]) -> String {
    pairs
        .iter()
        .map(|(key, value)| format!("{key} :: {value}\n"))
        .collect()
}

fn read_golden() -> String {
    let path = golden_path();
    fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "cannot read the golden fixture {}: {e}; {REGEN_HINT}",
            path.display()
        )
    })
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

/// The gate. Check mode (default) regenerates the full corpus and asserts
/// it byte-identical to the committed fixture, line by line for a usable
/// message; `AU_GOLDEN=write` regenerates the corpus twice (in-process
/// determinism check) and writes the fixture. See the module doc for the
/// regeneration command and the per-change protocol.
#[test]
fn differential_matches_golden() {
    let specs = full_specs();
    let text = render(&corpus_pairs(&specs));
    if write_mode() {
        let again = render(&corpus_pairs(&specs));
        assert_eq!(
            text, again,
            "full-corpus generation is not deterministic; refusing to write the fixture"
        );
        let path = golden_path();
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, &text).unwrap();
        println!("wrote {} ({} lines)", path.display(), text.lines().count());
        return;
    }
    let golden = read_golden();
    for (i, (got, want)) in text.lines().zip(golden.lines()).enumerate() {
        assert_eq!(
            got,
            want,
            "fixture line {} diverged; if the change is intended, review per the module-doc \
             protocol and {REGEN_HINT}",
            i + 1
        );
    }
    assert_eq!(
        text.lines().count(),
        golden.lines().count(),
        "fixture line count changed; the corpus definition moved; {REGEN_HINT}"
    );
}

/// A2's flag-on check per the module-doc protocol for pruning changes: the
/// exact solver with `exact_pruning: true` must report, on every corpus
/// instance, the same quality tuple the committed fixture's `exact` line
/// pins — the fixture was captured with the flag off, so equality here is
/// the claim that pruning discards only provably non-optimal candidates.
/// Also times the exact-only corpus with the flag off and on and prints
/// both totals (visible under `--nocapture`) as the broad-speedup signal.
#[test]
fn pruned_exact_matches_reference() {
    let golden = read_golden();
    let mut checked = 0usize;
    let mut reference_total = Duration::ZERO;
    let mut pruned_total = Duration::ZERO;
    for spec in full_specs() {
        let id = spec.id();
        let inst = spec.build();
        let snap = AuSnapshot::new(&inst.eg).unwrap();

        let start = Instant::now();
        let reference = anti_unify(
            &snap,
            inst.left,
            inst.right,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
        )
        .unwrap();
        reference_total += start.elapsed();

        let start = Instant::now();
        let pruned = anti_unify(
            &snap,
            inst.left,
            inst.right,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                exact_pruning: true,
                ..Default::default()
            },
        )
        .unwrap();
        pruned_total += start.elapsed();

        let key = format!("{id} exact");
        let want = golden
            .lines()
            .find_map(|line| line.strip_prefix(&format!("{key} :: ")))
            .unwrap_or_else(|| panic!("{key}: no exact line in the golden fixture; {REGEN_HINT}"));
        let got = format!(
            "size={} vmass={}",
            pruned.size,
            pruned.pool.variant_mass(pruned.term_id)
        );
        assert_eq!(
            got, want,
            "{id}: pruned exact quality diverges from the fixture's exact line; \
             exact_pruning discarded an optimal candidate"
        );
        assert_eq!(
            (
                reference.size,
                reference.pool.variant_mass(reference.term_id)
            ),
            (pruned.size, pruned.pool.variant_mass(pruned.term_id)),
            "{id}: flag-off and flag-on exact qualities diverge in-process"
        );
        checked += 1;
    }
    println!(
        "pruned_exact_matches_reference: {checked} instances, exact corpus wall time \
         flag-off {reference_total:.2?} -> flag-on {pruned_total:.2?}"
    );
}

/// Builds the corpus twice in-process and asserts the generated fixture
/// text is identical, so a fixture mismatch in the gate above can always be
/// attributed to a code change rather than harness nondeterminism.
#[test]
fn determinism_self_check() {
    let specs = full_specs();
    let first = render(&corpus_pairs(&specs));
    let second = render(&corpus_pairs(&specs));
    assert_eq!(
        first, second,
        "two in-process corpus builds produced different fixture text; the harness or a solver \
         is nondeterministic"
    );
}
