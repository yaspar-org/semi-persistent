// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Metamorphic anti-unification tests against a constructed ground-truth oracle.
//!
//! Each case generates a random ground term `t` over leaves, unary and binary
//! free operators, one mset (AC) operator, and one set (ACI) operator,
//! normalizes it to the canonical AC form (see `normalize`), then replaces
//! one to four disjoint subterm positions with fresh nullary operators. The
//! fresh operators appear in no merge, so no equation can bridge a
//! replacement and the planted difference survives congruence closure. The
//! least general generalization of the pair is known by construction: `t`
//! with each replaced position rewritten to a `Variants` pair. The oracle
//! values are therefore `tree_size(t) + m` for the result size and exactly
//! `m` `Variants` nodes, where `m` is the replacement count.
//!
//! Why the constructed term is the optimum:
//! - At a replaced position the right class contains only the fresh constant,
//!   so the only candidate is `Variants(best member of the left class, k)`,
//!   at cost `best_size(left) + 1`.
//! - At a shared position both sides are the same class, whose optimum is the
//!   class's minimal member at cost `best_size`.
//! - At a spine position (an ancestor of a replacement) the classes share
//!   exactly the original operator, and descending costs
//!   `tree_size + replacements below`, which beats the whole-pair `Variants`
//!   alternative by `tree_size - sum(replaced subterm sizes) >= 1`.
//! - Under an AC operator the child multisets differ by one occurrence per
//!   replacement; the diagonal matching is optimal because every transport
//!   cell costs at least the larger of the two classes' minimal sizes.
//!
//! Amplification merges enlarge classes without invalidating the oracle: each
//! merge adds one member built from a per-merge fresh unary operator, and each
//! target class is chosen so the new member's size is at least the class's
//! minimal size. Minimal sizes and cross-class operator sharing are therefore
//! unchanged, which is all the argument above uses.
//!
//! Unit (identity) declarations stay out of the random corpus because its
//! expected-lgg model is not unit-aware. The regression for an AC identity
//! class that also contains an AC member runs in the default suite; unit
//! declarations stay out of the random corpus pending a
//! units-aware expected-lgg model.
//!
//! MCGS can take an unbounded time in the f64 transport solve. Every generated
//! case therefore runs on a worker thread
//! with a receive timeout; a timeout fails the test naming D1 instead of
//! hanging the harness.

use std::sync::mpsc;
use std::thread;
use std::time::Duration;

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
// Deterministic RNG (xorshift64*), no external dependency.
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
// Ground terms as trees over the case signature.
// ---------------------------------------------------------------------------

const N_LEAVES: usize = 6;
const N_UNARY: usize = 2;
const N_BINARY: usize = 2;
const MAX_DEPTH: usize = 5;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Node {
    Leaf(usize),
    /// A fresh nullary operator planted by mutation; index into the per-case
    /// fresh-constant table. Never produced by the generator.
    Fresh(usize),
    Unary(usize, Box<Node>),
    Binary(usize, Box<Node>, Box<Node>),
    /// Children are a multiset. The generator emits pairwise distinct
    /// siblings; duplicates enter through `normalize` flattening and through
    /// the multiplicity tests, which build them directly.
    MSet(Vec<Node>),
    /// Children are a set; they must be pairwise distinct or the canonical
    /// node collapses duplicates and the tree size stops matching the class's
    /// minimal term size.
    Set(Vec<Node>),
}

/// Term size with AC multiplicity counted per occurrence, matching
/// `AuSnapshot::best_size` on a graph where every class's minimal member is
/// its as-built node.
fn tree_size(node: &Node) -> u32 {
    match node {
        Node::Leaf(_) | Node::Fresh(_) => 1,
        Node::Unary(_, c) => 1 + tree_size(c),
        Node::Binary(_, a, b) => 1 + tree_size(a) + tree_size(b),
        Node::MSet(cs) | Node::Set(cs) => 1 + cs.iter().map(tree_size).sum::<u32>(),
    }
}

fn gen_tree(rng: &mut XorShift64, depth: usize) -> Node {
    // Leaf probability grows with depth; depth 0 never yields a bare leaf so
    // every seed term has at least one non-root position to mutate.
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

/// Two to four pairwise distinct children. Sibling distinctness keeps raw set
/// nodes out of trivial idempotence collapse; `normalize` still introduces
/// duplicates across levels when it flattens nested mset occurrences.
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

/// The canonical form the e-graph stores for the variadic operators,
/// mirrored on trees: nested occurrences of the same operator flatten into
/// one child multiset, set children dedupe after flattening (idempotence),
/// and a variadic node left with one child collapses to that child
/// (`sand{a,a}` and `mplus{a}` both intern into `a`'s class). Children are
/// sorted so structural equality on normalized trees coincides with class
/// equality; without the sort, two orderings of one multiset read as
/// distinct subtrees while the e-graph interns one node. The generator's raw
/// trees are normalized before sizing, mutation, and building, so
/// `tree_size` matches the class's minimal term size; any canonization step
/// this mirror missed fails the corpus's size oracle. Flattening an mset can
/// raise child multiplicities above one; the oracle's diagonal-matching
/// argument covers that.
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

/// Every position in the tree as a path of child indices, root included.
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

/// Non-root positions, shuffled, then greedily filtered so no chosen position
/// is an ancestor of another. Overlapping mutations would compose instead of
/// planting independent differences.
fn choose_mutation_paths(rng: &mut XorShift64, tree: &Node, want: usize) -> Vec<Vec<usize>> {
    let mut all = Vec::new();
    positions(tree, &mut Vec::new(), &mut all);
    let mut candidates: Vec<Vec<usize>> = all.into_iter().filter(|p| !p.is_empty()).collect();
    // Fisher-Yates.
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
// Building trees into the e-graph.
// ---------------------------------------------------------------------------

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

/// Builds a tree bottom-up, recording every built node id and every
/// (parent, child) pair whose parent is unary. The unary pairs are the safe
/// targets for the tie-size amplification merge below.
struct Built {
    nodes: Vec<ENodeId>,
    leaf_nodes: Vec<ENodeId>,
    unary_edges: Vec<(ENodeId, ENodeId)>,
}

fn build(eg: &mut Eg, sig: &Sig, node: &Node, acc: &mut Built) -> ENodeId {
    let id = match node {
        Node::Leaf(i) => eg.add(sig.leaves[*i], &[]),
        Node::Fresh(i) => eg.add(sig.fresh[*i], &[]),
        Node::Unary(op, c) => {
            let cid = build(eg, sig, c, acc);
            let id = eg.add(sig.unary[*op], &[cid]);
            acc.unary_edges.push((id, cid));
            id
        }
        Node::Binary(op, a, b) => {
            let aid = build(eg, sig, a, acc);
            let bid = build(eg, sig, b, acc);
            eg.add(sig.binary[*op], &[aid, bid])
        }
        Node::MSet(cs) => {
            let cids: Vec<ENodeId> = cs.iter().map(|c| build(eg, sig, c, acc)).collect();
            eg.add(sig.mset, &cids)
        }
        Node::Set(cs) => {
            let cids: Vec<ENodeId> = cs.iter().map(|c| build(eg, sig, c, acc)).collect();
            eg.add(sig.set, &cids)
        }
    };
    if matches!(node, Node::Leaf(_)) {
        acc.leaf_nodes.push(id);
    }
    acc.nodes.push(id);
    id
}

/// Amplification merges, each through a per-merge fresh unary operator so no
/// two classes gain a shared operator. None lowers a class's minimal term
/// size:
/// - `merge(h(w), w)` adds a member of size `1 + best(w)` to `class(w)` and
///   makes the class graph cyclic;
/// - `merge(h(w), leaf)` adds a member of size at least 2 to a class whose
///   minimal size is 1;
/// - `merge(h(c), p)` for a unary parent `p` of child `c` adds a member of
///   size exactly `best(p)`.
fn amplify(eg: &mut Eg, sig: &Sig, rng: &mut XorShift64, acc: &Built, tag: &mut usize) {
    let fresh_unary = |eg: &mut Eg, tag: &mut usize| {
        let op = eg.register_op1(&format!("amp{tag}"), sig.sort, sig.sort);
        *tag += 1;
        op
    };

    // Self wraps scale with the graph so larger cases also carry multi-member
    // classes throughout, which multiplies the action space per OR node.
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
// Result inspection: variable count, projections, class membership.
// ---------------------------------------------------------------------------

/// Occurrences of `Variants` in the result, counted per tree position. Each
/// planted mutation pairs a distinct fresh constant, so occurrences cannot
/// coincide through pool sharing.
fn count_variants(pool: &TermPool<OpId, LitValId>, id: TermId) -> u32 {
    let own = u32::from(matches!(pool.op(id), TermOp::Variants));
    own + pool
        .children(id)
        .iter()
        .map(|&c| count_variants(pool, c))
        .sum::<u32>()
}

/// Own a projected result so the snapshot and result borrows can end before
/// the projection is materialized back into the mutable e-graph.
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
// The per-pair oracle check.
// ---------------------------------------------------------------------------

struct PairOutcome {
    /// Equal to the oracle size by the assertion in `check_pair`; kept for
    /// gap accounting only.
    exact_size: u32,
    mcgs_size: u32,
    mcgs_certified: bool,
}

/// Runs both solvers on one class pair and checks:
/// - the exact result size and Variants count equal the constructed oracle;
/// - all four projections re-evaluate into their source classes;
/// - MCGS never reports a better size than the exact optimum, and a
///   `Completion::Exact` certificate implies the optimal size.
///
/// The MCGS size is returned for gap accounting; it is deliberately not
/// asserted equal to the optimum, because at a finite playout budget the gap
/// is a measurement, not a defect.
fn check_pair(
    eg: &mut Eg,
    left: ENodeId,
    right: ENodeId,
    expected_size: u32,
    expected_vars: u32,
    playouts: u64,
    label: &str,
) -> PairOutcome {
    let (exact_size, exact_vars, exact_projs, mcgs_size, mcgs_certified, mcgs_projs) = {
        let snap = AuSnapshot::new(eg).unwrap();

        let exact = anti_unify(
            &snap,
            left,
            right,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
        )
        .unwrap();
        let exact_size = exact.size;
        let exact_vars = count_variants(&exact.pool, exact.term_id);
        let exact_projs = projected_terms(exact);

        let mcgs = anti_unify(
            &snap,
            left,
            right,
            &AuConfig {
                algorithm: AuAlgorithm::Uct,
                playouts,
                ..Default::default()
            },
        )
        .unwrap();
        let mcgs_size = mcgs.size;
        let mcgs_certified = mcgs.completion == Completion::Exact;
        let mcgs_projs = projected_terms(mcgs);

        (
            exact_size,
            exact_vars,
            exact_projs,
            mcgs_size,
            mcgs_certified,
            mcgs_projs,
        )
    };

    assert_eq!(
        exact_size, expected_size,
        "{label}: exact size {exact_size} differs from the constructed oracle {expected_size}; \
         larger means missed sharing, smaller means a planted mutation was bridged"
    );
    assert_eq!(
        exact_vars, expected_vars,
        "{label}: exact result has {exact_vars} generalization variables, oracle expects \
         {expected_vars}; extra variables mean missed sharing, missing variables mean a planted \
         mutation was illegally bridged"
    );

    for (alg, (lp, rp)) in [("exact", &exact_projs), ("mcgs", &mcgs_projs)] {
        let pl = materialize(eg, lp);
        let pr = materialize(eg, rp);
        eg.rebuild();
        assert_eq!(
            eg.find_const(pl),
            eg.find_const(left),
            "{label}: {alg} left projection does not re-evaluate into the left class"
        );
        assert_eq!(
            eg.find_const(pr),
            eg.find_const(right),
            "{label}: {alg} right projection does not re-evaluate into the right class"
        );
    }

    assert!(
        mcgs_size >= exact_size,
        "{label}: MCGS size {mcgs_size} beats the exact solver's {exact_size}; \
         the exact solver's optimality is broken"
    );
    if mcgs_certified {
        assert_eq!(
            mcgs_size, exact_size,
            "{label}: MCGS reports Completion::Exact at size {mcgs_size} but the optimum \
             is {exact_size}; the completion certificate is unsound"
        );
    }

    PairOutcome {
        exact_size,
        mcgs_size,
        mcgs_certified,
    }
}

// ---------------------------------------------------------------------------
// One generated case, end to end.
// ---------------------------------------------------------------------------

fn run_case(seed: u64, playouts: u64) -> PairOutcome {
    let mut rng = XorShift64::new(seed);
    let mut eg = Eg::new();
    let mut sig = register_signature(&mut eg);

    let t = normalize(&gen_tree(&mut rng, 0));
    let want = 1 + rng.below(4);
    let paths = choose_mutation_paths(&mut rng, &t, want);
    assert!(!paths.is_empty(), "seed {seed:#018x}: no mutable position");
    let m = paths.len() as u32;

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
    let left = build(&mut eg, &sig, &t, &mut acc);
    let right = build(&mut eg, &sig, &mutant, &mut acc);
    let mut amp_tag = 0;
    amplify(&mut eg, &sig, &mut rng, &acc, &mut amp_tag);
    eg.rebuild();

    let expected_size = tree_size(&t) + m;
    let label = format!("seed {seed:#018x} (m={m})");
    check_pair(&mut eg, left, right, expected_size, m, playouts, &label)
}

/// Runs one case on a worker thread with a receive timeout, because MCGS can
/// hang in the f64 transport solve. On
/// timeout the worker thread is leaked, still spinning, and the test fails
/// with the seed instead of hanging the harness.
fn run_case_guarded(seed: u64, playouts: u64, timeout: Duration) -> PairOutcome {
    let (tx, rx) = mpsc::channel();
    thread::Builder::new()
        .name(format!("au-meta-{seed:x}"))
        .spawn(move || {
            let _ = tx.send(run_case(seed, playouts));
        })
        .unwrap();
    match rx.recv_timeout(timeout) {
        Ok(outcome) => outcome,
        Err(mpsc::RecvTimeoutError::Timeout) => panic!(
            "seed {seed:#018x}: case exceeded {timeout:?}; matches the guarded MCGS \
             transport hang; the worker thread is leaked"
        ),
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("seed {seed:#018x}: case worker panicked, its message is above")
        }
    }
}

// ---------------------------------------------------------------------------
// Gap accounting for the exact-vs-MCGS comparison.
// ---------------------------------------------------------------------------

#[derive(Default)]
struct GapStats {
    cases: usize,
    zero: usize,
    certified: usize,
    sum: u64,
    max: u32,
    max_seed: u64,
}

impl GapStats {
    fn record(&mut self, seed: u64, outcome: &PairOutcome) {
        let gap = outcome.mcgs_size - outcome.exact_size;
        self.cases += 1;
        if gap == 0 {
            self.zero += 1;
        }
        if outcome.mcgs_certified {
            self.certified += 1;
        }
        self.sum += u64::from(gap);
        if gap > self.max {
            self.max = gap;
            self.max_seed = seed;
        }
    }

    fn print(&self, header: &str) {
        println!(
            "{header}: {} cases, gap==0 {}/{} ({:.1}%), certified exact {}/{}, mean gap {:.3}, \
             max gap {} at seed {:#018x}",
            self.cases,
            self.zero,
            self.cases,
            100.0 * self.zero as f64 / self.cases as f64,
            self.certified,
            self.cases,
            self.sum as f64 / self.cases as f64,
            self.max,
            self.max_seed,
        );
    }
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

const DEFAULT_BASE_SEED: u64 = 0xA5A5_5A5A_0000_0001;
const DEFAULT_CASES: u64 = 300;
/// 128 playouts: measured on 2026-08-14, every default-corpus case reaches
/// gap 0 by 8 playouts and 128 already certifies structural completion on
/// all 300 cases, keeping the certificate-soundness assertion engaged at
/// about 4 s debug runtime for the corpus.
const DEFAULT_PLAYOUTS: u64 = 128;
const CASE_TIMEOUT: Duration = Duration::from_secs(60);

/// The default corpus: seeded cases with the exact solver hard-asserted
/// against the constructed oracle and MCGS measured as an optimality gap,
/// summarized at the end of the run (visible with `--nocapture`).
#[test]
fn metamorphic_default_corpus() {
    let mut stats = GapStats::default();
    for i in 0..DEFAULT_CASES {
        let seed = case_seed(DEFAULT_BASE_SEED, i);
        let outcome = run_case_guarded(seed, DEFAULT_PLAYOUTS, CASE_TIMEOUT);
        stats.record(seed, &outcome);
    }
    stats.print(&format!(
        "au_metamorphic default corpus (playouts={DEFAULT_PLAYOUTS})"
    ));
}

/// Multiplicity delta under the mset operator: the mutated child occurs with
/// multiplicity above one and the expected generalization pairs exactly one
/// occurrence, leaving the remaining occurrences shared.
#[test]
fn metamorphic_mset_multiplicity_delta() {
    // Multiplicity 2, leaf child: f0(mplus{a, a, b}, c) vs f0(mplus{a, k, b}, c).
    {
        let mut eg = Eg::new();
        let mut sig = register_signature(&mut eg);
        sig.fresh = vec![eg.register_op0("km0", sig.sort)];
        let t = Node::Binary(
            0,
            Box::new(Node::MSet(vec![
                Node::Leaf(0),
                Node::Leaf(0),
                Node::Leaf(1),
            ])),
            Box::new(Node::Leaf(2)),
        );
        let mutant = replace_at(&t, &[0, 1], &Node::Fresh(0));
        let mut acc = Built {
            nodes: Vec::new(),
            leaf_nodes: Vec::new(),
            unary_edges: Vec::new(),
        };
        let left = build(&mut eg, &sig, &t, &mut acc);
        let right = build(&mut eg, &sig, &mutant, &mut acc);
        eg.rebuild();
        let expected = tree_size(&t) + 1;
        check_pair(
            &mut eg,
            left,
            right,
            expected,
            1,
            2000,
            "mset multiplicity 2, leaf child",
        );
    }

    // Multiplicity 3, compound child: f1(mplus{u0(a), u0(a), u0(a)}, b) with
    // one occurrence replaced. The diagonal matching keeps two occurrences
    // shared and pairs the third against the fresh constant.
    {
        let mut eg = Eg::new();
        let mut sig = register_signature(&mut eg);
        sig.fresh = vec![eg.register_op0("km0", sig.sort)];
        let u0a = Node::Unary(0, Box::new(Node::Leaf(0)));
        let t = Node::Binary(
            1,
            Box::new(Node::MSet(vec![u0a.clone(), u0a.clone(), u0a.clone()])),
            Box::new(Node::Leaf(1)),
        );
        let mutant = replace_at(&t, &[0, 2], &Node::Fresh(0));
        let mut acc = Built {
            nodes: Vec::new(),
            leaf_nodes: Vec::new(),
            unary_edges: Vec::new(),
        };
        let left = build(&mut eg, &sig, &t, &mut acc);
        let right = build(&mut eg, &sig, &mutant, &mut acc);
        eg.rebuild();
        let expected = tree_size(&t) + 1;
        check_pair(
            &mut eg,
            left,
            right,
            expected,
            1,
            2000,
            "mset multiplicity 3, compound child",
        );
    }
}

/// Regression test: an AC identity class that
/// contains an AC member must not panic the exact solver. Reproduces the
/// minimal trigger: declare unit `e` for the mset operator, merge `e` with
/// `mplus{a, b}`, rebuild, then run exact AU(c, e). The D2 fix (padded
/// identity classes extend the cycle context) makes this a regression test.
#[test]
fn units_identity_degenerate_exact_returns() {
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let e_op = eg.register_op0("e", sort);
    let a_op = eg.register_op0("a", sort);
    let b_op = eg.register_op0("b", sort);
    let c_op = eg.register_op0("c", sort);
    let plus = eg.register_mset("mplus", sort, sort);
    let e = eg.add(e_op, &[]);
    eg.set_unit_node(plus, e);
    let a = eg.add(a_op, &[]);
    let b = eg.add(b_op, &[]);
    let c = eg.add(c_op, &[]);
    let ab = eg.add(plus, &[a, b]);
    eg.merge(e, ab);
    eg.rebuild();

    let snap = AuSnapshot::new(&eg).unwrap();
    let result = anti_unify(
        &snap,
        c,
        e,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            ..Default::default()
        },
    );
    assert!(
        result.is_ok(),
        "exact AU over an identity-degenerate graph must return, not panic"
    );
}

/// Larger sweep for manual runs: ten times the default corpus at the same
/// playout budget. Run with
/// `cargo test -p semi-persistent-egraph --test au_metamorphic -- --ignored --nocapture`.
#[test]
#[ignore = "manual sweep: ~10x the default corpus runtime"]
fn metamorphic_large_sweep() {
    let mut stats = GapStats::default();
    for i in 0..2000u64 {
        let seed = case_seed(0xC0FF_EE00_0000_0002, i);
        let outcome = run_case_guarded(seed, DEFAULT_PLAYOUTS, CASE_TIMEOUT);
        stats.record(seed, &outcome);
    }
    stats.print(&format!(
        "au_metamorphic large sweep (playouts={DEFAULT_PLAYOUTS})"
    ));
}

/// Gap convergence: MCGS at four playout budgets on a fixed subsample,
/// printing the gap distribution per budget. Establishes the quality baseline
/// for completion-check performance: a geometric-schedule completion check
/// must not regress these
/// distributions. The budgets bracket the measured convergence: on this
/// corpus every case reaches gap 0 by 8 playouts (measured 2026-08-14), so
/// budgets in the thousands add certification headroom, not quality.
#[test]
#[ignore = "manual sweep: four MCGS budgets over a fixed subsample"]
fn mcgs_gap_convergence() {
    const SUBSAMPLE: u64 = 40;
    for playouts in [0u64, 8, 64, 512] {
        let mut stats = GapStats::default();
        for i in 0..SUBSAMPLE {
            let seed = case_seed(DEFAULT_BASE_SEED, i);
            let outcome = run_case_guarded(seed, playouts, Duration::from_secs(300));
            stats.record(seed, &outcome);
        }
        stats.print(&format!("au_metamorphic convergence (playouts={playouts})"));
    }
}
