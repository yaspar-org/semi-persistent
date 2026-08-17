// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The deceptive AU instance family (plan item B2, doc/au-solver-plan.md) and
//! the generators the anytime corpus (`au_corpus_bench.rs`) shares with it.
//!
//! MCGS ranks actions by the lazy-completion estimate: an action costs
//! `1 + sum over its child pairs of (bs(left) + bs(right))`, the price of
//! turning every child pair into a variable. The estimate is exact for a child
//! pair whose classes share no operator (a variable is all one can do there)
//! and strictly pessimistic for a pair that factors through shared structure.
//! This family builds instances where that difference misranks the root
//! actions, so the greedy answer — MCGS at one playout, the initial rollout —
//! is provably suboptimal and the quality-vs-budget curve is not flat.
//!
//! # The gadget
//!
//! One class pair `(L_i, R_i)` per level, `i = 1..=burial_depth`, over a base
//! pair of distinct constants (`T_0 = 2`, `bs = 1` per side). Level `i` has
//! `decoys + 1` members per side:
//!
//! * `decoys` decoy members `dec_ij(x)` whose children are ground-distinct
//!   chains of size `s` over per-decoy operators, disjoint left from right.
//!   The child pair shares no operator, so the decoy's true value equals its
//!   estimate, `1 + 2s`.
//! * one winner member `c_i(L_{i-1}, sh)` (`c_i(L_{i-1})` when `shared = 0`),
//!   where `sh` is one class occurring on both sides, of size `shared`. The
//!   shared child pair is an `l == r` terminal, which the estimate prices
//!   exactly at `shared`; the estimate's whole error is on the buried child
//!   pair, which it prices at `2*bs(L_{i-1})` where the truth is `T_{i-1}`.
//!
//! Writing `q = shared` and `s = decoy_bs`, the closed form is
//!
//! ```text
//! bs(L_i) = min(i*(1+q) + 1, 1 + s)      T_i = i*(1+q) + 2
//! estimate(winner at level i) = 1 + 2*bs(L_{i-1}) + q
//! estimate(decoy  at level i) = 1 + 2s = true value of the decoy
//! ```
//!
//! and the level-`i` misranking `estimate(decoy) <= estimate(winner)` holds
//! exactly when `2s <= 2*bs(L_{i-1}) + q`, i.e. for every level at or above
//! `first_deceptive_level`. Once `bs` saturates at `1 + s` the estimate margin
//! is `2 + q`, which is why the margin knob is the size of the shared child:
//! an action whose children are ground-distinct has estimate `2m - 1` in its
//! own member size `m`, so a decoy that also sets the class's `bs` can never
//! be misranked by more than 2.
//!
//! [`DeceptiveParams::plan`] solves the arithmetic for the requested knobs:
//! `burial_depth` (levels), `margin` (`>= 2`, equal to `2 + shared`), `gap`
//! (how much worse the greedy answer is), and `decoys` (actions the search
//! must step past at every level, all tied at the same estimate and all
//! ordered before the winner, since operators are registered per level with
//! the winner last and actions are enumerated in operator order). The
//! predictions are
//!
//! ```text
//! optimum = burial_depth*(1 + q) + 2      greedy = optimum + gap
//! ```
//!
//! and both are asserted per instance against the exact solver and against
//! MCGS at one playout — the family is verified, not assumed.
//!
//! # Mixing
//!
//! [`build_mixed`] plants gadget pairs at non-overlapping positions of a
//! random backbone that also carries the cyclic shared-operator amplification
//! of the crossover family (`au_anytime_bench.rs`'s `rand` stratum): the
//! gadget supplies the misranking, the cyclic classes supply the exact
//! solver's context product, so exact stays slow enough to be worth measuring
//! against.
//!
//! Tests: `deceptive_family_smoke` runs in the default suite (~2 s release);
//! `deceptive_family_grid` is `#[ignore]`d and sweeps the full knob grid
//! (~3 min release), reporting the fraction of instances on which greedy is
//! wrong and the playouts each instance needs to close the gap.

use std::time::{Duration, Instant};

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::id::{ENodeId, OpId, SortId};
use semi_persistent_egraph::literal::NiraLitVal;

pub type Eg = EGraph31<NiraLitVal, false, false>;

/// One anti-unification instance: the frozen-to-be e-graph and the root pair.
pub struct Instance {
    pub eg: Eg,
    pub left: ENodeId,
    pub right: ENodeId,
}

// ---------------------------------------------------------------------------
// The deceptive family.
// ---------------------------------------------------------------------------

/// Knobs of one deceptive instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeceptiveParams {
    /// Levels between the root and the base pair. The winner's payoff is
    /// visible only after descending all of them.
    pub burial_depth: usize,
    /// Estimate margin by which the decoys beat the winner once `bs`
    /// saturates. At least 2; `margin = 2 + shared`.
    pub margin: usize,
    /// How much worse the greedy answer is than the optimum, in size units.
    pub gap: usize,
    /// Decoy members per level.
    pub decoys: usize,
}

/// The arithmetic of one deceptive instance: derived sizes and the
/// predictions the tests assert.
#[derive(Clone, Copy, Debug)]
pub struct DeceptivePlan {
    pub params: DeceptiveParams,
    /// `q`: size of the shared child of every winner member.
    pub shared: usize,
    /// `s`: `bs` of each decoy child.
    pub decoy_bs: usize,
    /// `gap` after the parity adjustment; the asserted greedy - optimum.
    pub gap_eff: usize,
    /// Optimal size, `burial_depth*(1 + shared) + 2`.
    pub optimum: u32,
    /// Size the greedy (one-playout) answer returns, `optimum + gap_eff`.
    pub greedy: u32,
    /// Lowest level whose decoys outrank the winner on the estimate.
    pub first_deceptive_level: usize,
    /// Estimate of a decoy action at a saturated level, `1 + 2s`.
    pub est_decoy: u32,
    /// Estimate of the winner action at a saturated level,
    /// `1 + 2*(1 + s) + q`.
    pub est_winner: u32,
}

impl DeceptiveParams {
    /// `gap` after the parity adjustment: `2s = span + 1 + gap` must be even.
    fn gap_eff(&self) -> usize {
        let span = self.burial_depth * (self.margin - 1);
        if (span + 1 + self.gap).is_multiple_of(2) {
            self.gap
        } else {
            self.gap + 1
        }
    }

    /// Whether level `i`'s decoys outrank its winner. The estimate is the full
    /// lexicographic quality `(size, variant_mass)`: a decoy's is `(1 + 2s, 2s)`
    /// and the winner's is `(1 + 2*bs(L_{i-1}) + q, 2*bs(L_{i-1}))`, because
    /// the shared child pair is an `l == r` terminal — the estimate prices it
    /// at `q` exactly, with no variant mass. Ties go to the decoys, which are
    /// enumerated first (their operators are registered first).
    fn deceptive_at(&self, level: usize) -> bool {
        let q = self.margin - 2;
        let s = (self.burial_depth * (1 + q) + 1 + self.gap_eff()) / 2;
        let bs_below = ((level - 1) * (1 + q) + 1).min(1 + s);
        (1 + 2 * s, 2 * s) <= (1 + 2 * bs_below + q, 2 * bs_below)
    }

    /// Whether the knobs admit a deceptive instance: the decoys must outrank
    /// the winner at the root, which caps the achievable gap at
    /// `burial_depth*(margin - 1) - margin + 1`. A larger regret has to be
    /// bought with a deeper burial or a wider shared child.
    pub fn is_feasible(&self) -> bool {
        self.burial_depth >= 1
            && self.margin >= 2
            && self.gap >= 1
            && self.decoys >= 1
            && self.deceptive_at(self.burial_depth)
    }

    /// Solve the family arithmetic. Panics on infeasible knobs
    /// ([`DeceptiveParams::is_feasible`]); `gap` is raised by one when the
    /// parity of `2s = d*(1+q) + 1 + gap` demands it.
    pub fn plan(&self) -> DeceptivePlan {
        assert!(
            self.is_feasible(),
            "{self:?}: infeasible knobs (need margin >= 2, decoys >= 1, and a \
             gap the burial depth can pay for)"
        );
        let q = self.margin - 2;
        let span = self.burial_depth * (1 + q);
        // 2s = span + 1 + gap, so the decoy's true value 1 + 2s sits exactly
        // `gap` above the optimum span + 2.
        let gap_eff = self.gap_eff();
        let s = (span + 1 + gap_eff) / 2;
        assert!(s >= 1, "decoy_bs >= 1");
        let first = (1..=self.burial_depth)
            .find(|&i| self.deceptive_at(i))
            .expect("feasible knobs have a deceptive root level");
        DeceptivePlan {
            params: *self,
            shared: q,
            decoy_bs: s,
            gap_eff,
            optimum: (span + 2) as u32,
            greedy: (span + 2 + gap_eff) as u32,
            first_deceptive_level: first,
            est_decoy: (1 + 2 * s) as u32,
            est_winner: (1 + 2 * (1 + s) + q) as u32,
        }
    }
}

/// Add one deceptive gadget to `eg` under the operator-name prefix `tag`.
/// Returns the root class pair `(L_d, R_d)`.
pub fn add_deceptive_gadget(
    eg: &mut Eg,
    sort: SortId,
    tag: &str,
    plan: &DeceptivePlan,
) -> (ENodeId, ENodeId) {
    let q = plan.shared;
    let s = plan.decoy_bs;

    // The shared child: one class of size q, reached from both sides.
    let shared = if q == 0 {
        None
    } else {
        let leaf_op = eg.register_op0(&format!("{tag}sh0"), sort);
        let mut node = eg.add(leaf_op, &[]);
        for w in 1..q {
            let op = eg.register_op1(&format!("{tag}shw{w}"), sort, sort);
            node = eg.add(op, &[node]);
        }
        Some(node)
    };

    // The base pair: distinct constants, no shared operator, T_0 = 2.
    let zl_op = eg.register_op0(&format!("{tag}zl"), sort);
    let zr_op = eg.register_op0(&format!("{tag}zr"), sort);
    let mut left = eg.add(zl_op, &[]);
    let mut right = eg.add(zr_op, &[]);

    for level in 1..=plan.params.burial_depth {
        // Decoys first, so their operators sort before the winner's and MCGS
        // expands every one of them before it reaches the winner.
        let mut l_members: Vec<ENodeId> = Vec::with_capacity(plan.params.decoys + 1);
        let mut r_members: Vec<ENodeId> = Vec::with_capacity(plan.params.decoys + 1);
        for j in 0..plan.params.decoys {
            let dec = eg.register_op1(&format!("{tag}d{level}_{j}"), sort, sort);
            let xl_op = eg.register_op0(&format!("{tag}xl{level}_{j}"), sort);
            let xr_op = eg.register_op0(&format!("{tag}xr{level}_{j}"), sort);
            let mut xl = eg.add(xl_op, &[]);
            let mut xr = eg.add(xr_op, &[]);
            for w in 1..s {
                let al = eg.register_op1(&format!("{tag}al{level}_{j}_{w}"), sort, sort);
                let ar = eg.register_op1(&format!("{tag}ar{level}_{j}_{w}"), sort, sort);
                xl = eg.add(al, &[xl]);
                xr = eg.add(ar, &[xr]);
            }
            l_members.push(eg.add(dec, &[xl]));
            r_members.push(eg.add(dec, &[xr]));
        }
        let (lw, rw) = match shared {
            None => {
                let c = eg.register_op1(&format!("{tag}c{level}"), sort, sort);
                (eg.add(c, &[left]), eg.add(c, &[right]))
            }
            Some(sh) => {
                let c = eg.register_op2(&format!("{tag}c{level}"), sort, sort, sort);
                (eg.add(c, &[left, sh]), eg.add(c, &[right, sh]))
            }
        };
        l_members.push(lw);
        r_members.push(rw);
        for &m in &l_members[..l_members.len() - 1] {
            eg.merge(m, lw);
        }
        for &m in &r_members[..r_members.len() - 1] {
            eg.merge(m, rw);
        }
        left = lw;
        right = rw;
    }
    (left, right)
}

/// A standalone deceptive instance.
pub fn build_deceptive(params: DeceptiveParams) -> Instance {
    let plan = params.plan();
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let (left, right) = add_deceptive_gadget(&mut eg, sort, "g_", &plan);
    eg.rebuild();
    Instance { eg, left, right }
}

/// Knobs of one wide deceptive instance: a width-family spine over a
/// deceptive gadget.
#[derive(Clone, Copy, Debug)]
pub struct WideParams {
    /// Spine levels above the gadget.
    pub depth: usize,
    /// Same-operator members per class per side per level, so every
    /// level-pair OR state fans out `width^2` actions.
    pub width: usize,
    pub deceptive: DeceptiveParams,
}

/// A deceptive gadget under a width-family spine. The spine is what the
/// pruned exact solver still has to pay for — its actions all sit under the
/// generalize value, so neither the projection bound nor context subsumption
/// removes them — and the gadget at the base is what the estimate misranks,
/// so the instance is simultaneously hard for exact and deceptive for MCGS.
pub fn build_wide_deceptive(p: WideParams) -> Instance {
    let plan = p.deceptive.plan();
    let mut eg = Eg::new();
    let sort = eg.intern_sort("S");
    let (mut left, mut right) = add_deceptive_gadget(&mut eg, sort, "g_", &plan);
    let b = eg.register_op2("b", sort, sort, sort);
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
// Deterministic RNG and the random backbone (from au_anytime_bench.rs, with a
// Dec node kind for planted gadgets).
// ---------------------------------------------------------------------------

pub struct XorShift64(u64);

impl XorShift64 {
    pub fn new(seed: u64) -> Self {
        XorShift64(seed | 1)
    }

    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }

    pub fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

/// splitmix64: decorrelates consecutive loop indices into case seeds.
pub fn case_seed(base: u64, i: u64) -> u64 {
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
pub enum Node {
    Leaf(usize),
    Unary(usize, Box<Node>),
    Binary(usize, Box<Node>, Box<Node>),
    MSet(Vec<Node>),
    /// Planted: the cyclic W class with this index. Never generated.
    Hub(usize),
    /// Planted: index into the per-instance fresh-constant table (the sides
    /// use disjoint indices). Never generated.
    Fresh(usize),
    /// Planted: the deceptive gadget with this index. Never generated.
    Dec(usize),
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

fn positions(node: &Node, prefix: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
    out.push(prefix.clone());
    let children: Vec<&Node> = match node {
        Node::Leaf(_) | Node::Hub(_) | Node::Fresh(_) | Node::Dec(_) => Vec::new(),
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
        Node::Leaf(_) | Node::Hub(_) | Node::Fresh(_) | Node::Dec(_) => {
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

struct RandSig {
    sort: SortId,
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
    gadgets: &[ENodeId],
    node: &Node,
    acc: &mut Built,
) -> ENodeId {
    let id = match node {
        Node::Leaf(i) => eg.add(sig.leaves[*i], &[]),
        Node::Hub(i) => hubs[*i],
        Node::Dec(i) => gadgets[*i],
        Node::Fresh(i) => eg.add(sig.fresh[*i], &[]),
        Node::Unary(op, c) => {
            let cid = build_node(eg, sig, hubs, gadgets, c, acc);
            eg.add(sig.unary[*op], &[cid])
        }
        Node::Binary(op, a, b) => {
            let aid = build_node(eg, sig, hubs, gadgets, a, acc);
            let bid = build_node(eg, sig, hubs, gadgets, b, acc);
            eg.add(sig.binary[*op], &[aid, bid])
        }
        Node::MSet(cs) => {
            let cids: Vec<ENodeId> = cs
                .iter()
                .map(|c| build_node(eg, sig, hubs, gadgets, c, acc))
                .collect();
            eg.add(sig.mset, &cids)
        }
    };
    if matches!(node, Node::Leaf(_)) {
        acc.leaf_nodes.push(id);
    }
    if !matches!(node, Node::Hub(_) | Node::Dec(_)) {
        acc.nodes.push(id);
    }
    id
}

/// Knobs of one mixed instance: a random backbone with cyclic amplification,
/// carrying `n_deceptive` planted gadgets.
#[derive(Clone, Copy, Debug)]
pub struct MixedParams {
    pub seed: u64,
    /// Cyclic W classes (the crossover family's shared-operator machinery).
    pub cycles: usize,
    /// Planted deceptive gadgets; 0 gives the pilot's `rand` stratum.
    pub n_deceptive: usize,
    /// Knobs of every planted gadget.
    pub deceptive: DeceptiveParams,
}

/// What a mixed instance actually got, for the CSV.
#[derive(Clone, Copy, Debug)]
pub struct MixedDescr {
    pub cycles: usize,
    pub muts: usize,
    pub hot: usize,
    pub planted: usize,
}

pub fn build_mixed(p: MixedParams) -> (Instance, MixedDescr) {
    let mut rng = XorShift64::new(p.seed);
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

    // Shared-operator amplification: mutually reachable cyclic W classes.
    let cycles = p.cycles;
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

    // Deceptive gadgets, one class pair each.
    let plan = p.deceptive.plan();
    let mut gadget_l: Vec<ENodeId> = Vec::new();
    let mut gadget_r: Vec<ENodeId> = Vec::new();
    for i in 0..p.n_deceptive {
        let (l, r) = add_deceptive_gadget(&mut eg, sort, &format!("g{i}_"), &plan);
        gadget_l.push(l);
        gadget_r.push(r);
    }

    // Random backbone: disjoint positions replaced by hot (distinct W pair),
    // deceptive (a gadget pair), or diff (side-local fresh constants) kinds.
    let t = gen_tree(&mut rng, 0);
    let want = 2 + rng.below(3) + p.n_deceptive;
    let paths = choose_mutation_paths(&mut rng, &t, want);
    assert!(
        !paths.is_empty(),
        "seed {:#018x}: no mutable position",
        p.seed
    );
    let mut left_t = t.clone();
    let mut right_t = t;
    let mut hot = 0usize;
    let mut planted = 0usize;
    for (idx, path) in paths.iter().enumerate() {
        if planted < p.n_deceptive {
            left_t = replace_at(&left_t, path, &Node::Dec(planted));
            right_t = replace_at(&right_t, path, &Node::Dec(planted));
            planted += 1;
            continue;
        }
        let make_hot = hot < 3 && (idx == p.n_deceptive || rng.below(2) == 0);
        if make_hot {
            hot += 1;
            let i = rng.below(cycles);
            let j = (i + 1 + rng.below(cycles - 1)) % cycles;
            left_t = replace_at(&left_t, path, &Node::Hub(i));
            right_t = replace_at(&right_t, path, &Node::Hub(j));
        } else {
            let kl = eg.register_op0(&format!("kl{idx}"), sort);
            let kr = eg.register_op0(&format!("kr{idx}"), sort);
            let li = sig.fresh.len();
            sig.fresh.push(kl);
            sig.fresh.push(kr);
            left_t = replace_at(&left_t, path, &Node::Fresh(li));
            right_t = replace_at(&right_t, path, &Node::Fresh(li + 1));
        }
    }

    let mut acc = Built {
        nodes: Vec::new(),
        leaf_nodes: Vec::new(),
    };
    let left = build_node(&mut eg, &sig, &w, &gadget_l, &left_t, &mut acc);
    let right = build_node(&mut eg, &sig, &w, &gadget_r, &right_t, &mut acc);

    // Fresh-operator (rule-inert) amplification, metamorphic style: one
    // self-wrap and two leaf merges through per-merge fresh unary operators,
    // so no two classes gain a shared operator from these.
    let mut amp_tag = 0usize;
    if !acc.nodes.is_empty() {
        let target = acc.nodes[rng.below(acc.nodes.len())];
        let op = eg.register_op1(&format!("amp{amp_tag}"), sig.sort, sig.sort);
        amp_tag += 1;
        let wrapped = eg.add(op, &[target]);
        eg.merge(wrapped, target);
        for _ in 0..2 {
            if acc.leaf_nodes.is_empty() {
                break;
            }
            let src = acc.nodes[rng.below(acc.nodes.len())];
            let leaf = acc.leaf_nodes[rng.below(acc.leaf_nodes.len())];
            let op = eg.register_op1(&format!("amp{amp_tag}"), sig.sort, sig.sort);
            amp_tag += 1;
            let member = eg.add(op, &[src]);
            eg.merge(member, leaf);
        }
    }
    eg.rebuild();

    (
        Instance { eg, left, right },
        MixedDescr {
            cycles,
            muts: paths.len(),
            hot,
            planted,
        },
    )
}

// ---------------------------------------------------------------------------
// Solver runners (in-process; the corpus harness wraps them in worker guards).
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub struct Quality {
    pub size: u32,
    pub vmass: u32,
    pub ms: f64,
    pub certified: bool,
}

/// Exact ground truth. `pruned` turns on both accelerations (A2 branch and
/// bound, A6 context subsumption); their differential tests pin that the
/// qualities are the unpruned solver's.
pub fn exact_quality(inst: &Instance, pruned: bool, deadline: Option<Duration>) -> Quality {
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let cfg = AuConfig {
        algorithm: AuAlgorithm::Exact,
        exact_pruning: pruned,
        context_subsumption: pruned,
        exact_deadline: deadline,
        ..Default::default()
    };
    let start = Instant::now();
    let result = anti_unify(&snap, inst.left, inst.right, &cfg).unwrap();
    let ms = start.elapsed().as_secs_f64() * 1e3;
    let (size, vmass) = result.pool.quality(result.term_id);
    Quality {
        size,
        vmass,
        ms,
        certified: matches!(result.completion, Completion::Exact),
    }
}

/// MCGS at one playout budget. `dominance` turns on A5 pruning.
pub fn mcgs_quality(inst: &Instance, playouts: u64, dominance: bool) -> Quality {
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let cfg = AuConfig {
        algorithm: AuAlgorithm::Uct,
        playouts,
        dominance_pruning: dominance,
        ..Default::default()
    };
    let start = Instant::now();
    let result = anti_unify(&snap, inst.left, inst.right, &cfg).unwrap();
    let ms = start.elapsed().as_secs_f64() * 1e3;
    let (size, vmass) = result.pool.quality(result.term_id);
    Quality {
        size,
        vmass,
        ms,
        certified: matches!(result.completion, Completion::Exact),
    }
}

/// `bs` of each side of the root pair, the inputs of every estimate.
pub fn root_best_sizes(inst: &Instance) -> (u32, u32) {
    let snap = AuSnapshot::new(&inst.eg).unwrap();
    let l = snap.class_of(inst.left).unwrap();
    let r = snap.class_of(inst.right).unwrap();
    (snap.best_size(l), snap.best_size(r))
}

/// Lowest ladder budget at which MCGS reaches `target`, or `None` if it never
/// does within `max_playouts`.
pub fn playouts_to_optimum(inst: &Instance, target: u32, max_playouts: u64) -> Option<u64> {
    let mut p = 1u64;
    while p <= max_playouts {
        if mcgs_quality(inst, p, false).size <= target {
            return Some(p);
        }
        p *= 2;
    }
    None
}

// ---------------------------------------------------------------------------
// Verification.
// ---------------------------------------------------------------------------

/// The knob grid the smoke test and the corpus draw from.
pub fn smoke_grid() -> Vec<DeceptiveParams> {
    let mut out = Vec::new();
    for &burial_depth in &[2usize, 4, 6] {
        for &margin in &[2usize, 5] {
            for &gap in &[1usize, 4] {
                for &decoys in &[1usize, 3] {
                    let p = DeceptiveParams {
                        burial_depth,
                        margin,
                        gap,
                        decoys,
                    };
                    if p.is_feasible() {
                        out.push(p);
                    }
                }
            }
        }
    }
    out
}

/// Verify one instance: the exact optimum matches the family arithmetic, the
/// greedy answer matches the predicted misranked answer, and the greedy answer
/// is strictly worse. Returns `(plan, exact, greedy)`.
pub fn verify_deception(
    params: DeceptiveParams,
    pruned: bool,
) -> (DeceptivePlan, Quality, Quality) {
    let plan = params.plan();
    let inst = build_deceptive(params);
    let exact = exact_quality(&inst, pruned, None);
    let greedy = mcgs_quality(&inst, 1, false);
    assert_eq!(
        exact.size, plan.optimum,
        "{params:?}: exact optimum {} != predicted {}; the family arithmetic is wrong",
        exact.size, plan.optimum
    );
    assert_eq!(
        greedy.size, plan.greedy,
        "{params:?}: greedy answer {} != predicted {}; the misranking is not the constructed one",
        greedy.size, plan.greedy
    );
    assert!(
        greedy.size > exact.size,
        "{params:?}: greedy is not wrong, so the instance is not deceptive"
    );
    (plan, exact, greedy)
}

#[test]
fn deceptive_family_smoke() {
    let mut wrong = 0usize;
    let mut n = 0usize;
    for params in smoke_grid() {
        let (plan, exact, greedy) = verify_deception(params, true);
        n += 1;
        if greedy.size > exact.size {
            wrong += 1;
        }
        // The pruned exact solver is the fast path; on this grid it is cheap
        // enough to cross-check every instance against the unpruned reference.
        let inst = build_deceptive(params);
        let plain = exact_quality(&inst, false, None);
        assert_eq!(
            (plain.size, plain.vmass),
            (exact.size, exact.vmass),
            "{params:?}: pruned exact disagrees with the unpruned reference"
        );
        println!(
            "d_b={} m={} gap={}(eff {}) k={}: q={} s={} first_deceptive_level={} \
             est(decoy)={} est(winner)={} optimum={} greedy={} exact_ms={:.2}",
            params.burial_depth,
            params.margin,
            params.gap,
            plan.gap_eff,
            params.decoys,
            plan.shared,
            plan.decoy_bs,
            plan.first_deceptive_level,
            plan.est_decoy,
            plan.est_winner,
            exact.size,
            greedy.size,
            exact.ms
        );
    }
    assert_eq!(wrong, n, "greedy must be wrong on every generated instance");
    println!("greedy wrong on {wrong}/{n} instances");
}

#[test]
fn deceptive_family_mixes_into_a_random_backbone() {
    let params = DeceptiveParams {
        burial_depth: 4,
        margin: 2,
        gap: 2,
        decoys: 2,
    };
    let (inst, descr) = build_mixed(MixedParams {
        seed: case_seed(0xDECE_971E_0000_0001, 3),
        cycles: 4,
        n_deceptive: 1,
        deceptive: params,
    });
    assert_eq!(descr.planted, 1);
    let exact = exact_quality(&inst, true, None);
    let greedy = mcgs_quality(&inst, 1, false);
    assert!(
        greedy.size >= exact.size,
        "MCGS beat the exact optimum: {} < {}",
        greedy.size,
        exact.size
    );
    assert!(
        greedy.size > exact.size,
        "the planted gadget did not survive mixing: greedy already optimal at {}",
        greedy.size
    );
    println!(
        "mixed: exact ({}, {}) in {:.2} ms, greedy ({}, {}), {descr:?}",
        exact.size, exact.vmass, exact.ms, greedy.size, greedy.vmass
    );
}

#[test]
fn wide_deceptive_keeps_the_deception_under_a_spine() {
    let deceptive = DeceptiveParams {
        burial_depth: 8,
        margin: 3,
        gap: 2,
        decoys: 2,
    };
    let plan = deceptive.plan();
    for &(depth, width) in &[(2usize, 4usize), (4, 8)] {
        let inst = build_wide_deceptive(WideParams {
            depth,
            width,
            deceptive,
        });
        let exact = exact_quality(&inst, true, None);
        let greedy = mcgs_quality(&inst, 1, false);
        // Each spine level adds its operator and one matched tag to both the
        // optimum and the greedy answer, so the regret is the gadget's.
        assert_eq!(
            exact.size,
            plan.optimum + 2 * depth as u32,
            "d{depth}w{width}: spine cost is not 2 per level"
        );
        assert_eq!(
            greedy.size - exact.size,
            plan.gap_eff as u32,
            "d{depth}w{width}: the spine changed the regret"
        );
        println!(
            "wide d{depth}w{width}: exact ({}, {}) in {:.2} ms, greedy {} (+{})",
            exact.size,
            exact.vmass,
            exact.ms,
            greedy.size,
            greedy.size - exact.size
        );
    }
}

#[test]
#[ignore = "full B2 grid: ~3 min release, prints the per-instance misranking arithmetic"]
fn deceptive_family_grid() {
    let mut n = 0usize;
    let mut wrong = 0usize;
    println!(
        "{:>4} {:>4} {:>4} {:>3} {:>4} {:>4} {:>6} {:>8} {:>8} {:>8} {:>8} {:>10}",
        "d_b", "m", "gap", "k", "q", "s", "lvl1", "est_dec", "est_win", "opt", "greedy", "p_to_opt"
    );
    for &burial_depth in &[2usize, 3, 4, 6, 8, 12, 16] {
        for &margin in &[2usize, 3, 5] {
            for &gap in &[1usize, 2, 8] {
                for &decoys in &[1usize, 2, 4] {
                    let params = DeceptiveParams {
                        burial_depth,
                        margin,
                        gap,
                        decoys,
                    };
                    if !params.is_feasible() {
                        continue;
                    }
                    let (plan, exact, greedy) = verify_deception(params, true);
                    n += 1;
                    if greedy.size > exact.size {
                        wrong += 1;
                    }
                    let inst = build_deceptive(params);
                    let p = playouts_to_optimum(&inst, exact.size, 1 << 16);
                    println!(
                        "{:>4} {:>4} {:>4} {:>3} {:>4} {:>4} {:>6} {:>8} {:>8} {:>8} {:>8} {:>10}",
                        burial_depth,
                        margin,
                        gap,
                        decoys,
                        plan.shared,
                        plan.decoy_bs,
                        plan.first_deceptive_level,
                        plan.est_decoy,
                        plan.est_winner,
                        exact.size,
                        greedy.size,
                        p.map_or("none".to_owned(), |p| p.to_string())
                    );
                }
            }
        }
    }
    println!("greedy wrong on {wrong}/{n} instances");
    assert_eq!(wrong, n);
}
