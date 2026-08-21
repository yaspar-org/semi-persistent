// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Randomized test of the projection identity and projection lower bound
//! against the exact solver.
//!
//! On seeded metamorphic instances (the generator pattern of
//! au_differential.rs with its own base seed, so the corpora stay
//! independent), the exact solver's returned term must satisfy, per instance:
//!
//! * the projection identity
//!   `size(t) = size(proj_L) + size(proj_R) - #backbone`, where `#backbone`
//!   counts the concrete nodes not under any `Variants` node (the structure
//!   both projections share) and the projections come from
//!   `TermPool::project`;
//! * the bound `size(t) >= lb_pair(l_root, r_root).0`, the exact solver's
//!   branch-and-bound prunes with (`au::estimates::lb_pair`).
//!
//! The identity is what makes `lb_pair` admissible, so pinning both against the
//! real solver checks the theorem and the implementation together.

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::estimates::lb_pair;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, anti_unify};
use semi_persistent_egraph::au::terms::{TermId, TermOp, TermPool};
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::nodes::LitValId;

type Eg = EGraph31<NiraLitVal, false, false>;

/// Base seed of this suite's corpus, distinct from au_differential.rs's and
/// au_metamorphic.rs's so the three corpora stay independent.
const BASE_SEED: u64 = 0xA1B0_0000_0000_0001;
/// Seeded instances per run.
const N_CASES: u64 = 200;

// ---------------------------------------------------------------------------
// Deterministic RNG (xorshift64*), as in au_differential.rs.
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
// Metamorphic generator (au_differential.rs, unchanged semantics): ground
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

/// One metamorphic instance, as in au_differential.rs `build_meta`.
fn build_meta(seed: u64) -> (Eg, ENodeId, ENodeId) {
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
    (eg, left, right)
}

// ---------------------------------------------------------------------------
// The checks.
// ---------------------------------------------------------------------------

/// Tree-expanded count of the backbone: concrete nodes reachable from the
/// root without passing through a `Variants` node. `Variants` nodes count
/// zero and are not entered (each arm belongs to one projection only).
/// Matches the tree-expansion semantics of `TermPool::size`, which counts a
/// hash-consed child once per occurrence.
fn backbone_count(pool: &TermPool<OpId, LitValId>, root: TermId) -> u64 {
    let mut count: u64 = 0;
    let mut stack: Vec<TermId> = vec![root];
    while let Some(t) = stack.pop() {
        if matches!(pool.op(t), TermOp::Variants) {
            continue;
        }
        count += 1;
        stack.extend_from_slice(pool.children(t));
    }
    count
}

/// Per instance: exact solve, then the projection identity and the bound.
#[test]
fn projection_identity_and_bound_hold_on_exact_terms() {
    for i in 0..N_CASES {
        let seed = case_seed(BASE_SEED, i);
        let (eg, left, right) = build_meta(seed);
        let snap = AuSnapshot::new(&eg).unwrap();
        let l_root = snap.class_of(left).unwrap();
        let r_root = snap.class_of(right).unwrap();

        let mut result = anti_unify(
            &snap,
            left,
            right,
            &AuConfig {
                algorithm: AuAlgorithm::Exact,
                ..Default::default()
            },
        )
        .unwrap();

        let size = u64::from(result.pool.size(result.term_id));
        let backbone = backbone_count(&result.pool, result.term_id);
        let proj_l = result.pool.project(result.term_id, 0);
        let proj_r = result.pool.project(result.term_id, 1);
        let size_l = u64::from(result.pool.size(proj_l));
        let size_r = u64::from(result.pool.size(proj_r));

        assert_eq!(
            size,
            size_l + size_r - backbone,
            "meta-{i:03} seed={seed:#018x}: projection identity violated \
             (size={size} proj_L={size_l} proj_R={size_r} backbone={backbone})"
        );

        let (lb_size, lb_vmass) = lb_pair(&snap, l_root, r_root);
        assert!(
            size >= u64::from(lb_size),
            "meta-{i:03} seed={seed:#018x}: exact size {size} below the projection \
             lower bound {lb_size}"
        );
        assert!(
            u64::from(result.pool.variant_mass(result.term_id)) >= u64::from(lb_vmass),
            "meta-{i:03} seed={seed:#018x}: variant mass below its lower bound"
        );
    }
}
