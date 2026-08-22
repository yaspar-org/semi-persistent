// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! An independent oracle for the exact anti-unification solver.
//!
//! Three production claims exercised here are that the objective is a function
//! of the two e-classes rather than of which members the search happened to
//! enumerate, that the checked admissible bounds never overestimate, and that
//! counting shared children by edge rather than by node leaves the optimum
//! unchanged on this finite domain. Pair-cycle erasure, AC/ACI semantics, and
//! refinement of the production relaxation loop are separate obligations.
//!
//! This file checks all three at once, on instances small enough to settle by
//! brute force, and it does so without reusing any of the solver's machinery.
//! The specification of anti-unification over an e-graph is
//!
//! ```text
//!   AU(L, R) = min over t_l in terms(L), t_r in terms(R) of plotkin(t_l, t_r)
//! ```
//!
//! under the lexicographic key `(size, variant_mass)`. So the oracle enumerates
//! every ground term of each class, runs a certificate-carrying extension of
//! Plotkin's structural recurrence on every pair, and takes the minimum. A
//! mismatch becomes `Variants(left, right)` and costs the complete hidden mass,
//! not one syntactic variable node. A disagreement with the solver is a defect
//! in the solver, in the cost model, or in this specification, and all three are
//! worth knowing about.
//!
//! Scope, stated rather than implied. The oracle enumerates terms, so it needs
//! the reachable term set to be finite and small: the instances here are acyclic
//! and a few dozen nodes. Operators are plain constructors, because Plotkin's
//! algorithm is only the right oracle for free symbols; the AC and ACI paths
//! have their own transport tests and are out of scope here.

use std::collections::HashMap;

use semi_persistent_egraph::EGraph31;
use semi_persistent_egraph::au::egraph_api::AuSnapshot;
use semi_persistent_egraph::au::session::{AuAlgorithm, AuConfig, Completion, anti_unify};
use semi_persistent_egraph::au::space::CycleMode;
use semi_persistent_egraph::id::{ENodeId, OpId};
use semi_persistent_egraph::literal::NiraLitVal;
use semi_persistent_egraph::multiplicity::MultiplicityLike;

type Eg = EGraph31<NiraLitVal, false, false>;

/// A ground term drawn from a class.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Term {
    op: OpId,
    kids: Vec<Term>,
}

impl Term {
    fn size(&self) -> u32 {
        1 + self.kids.iter().map(Term::size).sum::<u32>()
    }
}

/// Every ground term of `class`, up to `budget` nodes. Acyclic instances only:
/// the budget is a guard against a mistake in the fixture, not a way to cope
/// with cycles, and a class whose terms are all over budget yields nothing,
/// which the caller asserts against.
/// Cap on the term set of any one class. Exceeding it makes the enumeration
/// incomplete, and an incomplete enumeration is not an oracle: it could miss the
/// very pair that achieves the optimum and then accuse the solver of being
/// wrong. So the cap returns `None` and the caller skips the fixture rather than
/// truncating.
const MAX_TERMS: usize = 20_000;

fn terms_of(
    eg: &Eg,
    class: ENodeId,
    budget: u32,
    memo: &mut HashMap<(ENodeId, u32), Option<Vec<Term>>>,
) -> Option<Vec<Term>> {
    let root = eg.find_const(class);
    if let Some(hit) = memo.get(&(root, budget)) {
        return hit.clone();
    }
    // Guard against a class whose own expansion re-enters it: a merge can make
    // a class reachable from itself, and the budget alone does not stop the
    // memo from recursing before it is populated.
    memo.insert((root, budget), None);
    let mut out = Vec::new();
    if budget > 0 {
        // Class membership straight from the e-graph, grouped the way the
        // snapshot groups it but without its subsumption filter: the oracle
        // must not inherit a decision the solver makes.
        let members: Vec<(OpId, ENodeId)> = eg
            .node_ids()
            .filter(|&id| eg.find_const(id) == root)
            .map(|id| (eg.node_op(id), id))
            .collect();
        for (op, node) in members {
            // Multiplicity matters: a multiset node whose child `x` appears
            // twice has arity two at that position, and dropping the count
            // enumerates a term the class does not contain. That was the first
            // disagreement this fixture produced, and it was in the oracle.
            let mut kids = Vec::new();
            eg.for_each_child(node, |c, m| {
                for _ in 0..m.to_usize().max(1) {
                    kids.push(c);
                }
            });
            // Cartesian product of the children's term sets, under the budget.
            let mut combos: Vec<Vec<Term>> = vec![Vec::new()];
            let mut feasible = true;
            for k in &kids {
                let sub = terms_of(eg, *k, budget - 1, memo)?;
                if sub.is_empty() {
                    feasible = false;
                    break;
                }
                let mut next = Vec::new();
                for prefix in &combos {
                    for s in &sub {
                        let mut p = prefix.clone();
                        p.push(s.clone());
                        next.push(p);
                    }
                }
                if next.len() > MAX_TERMS {
                    return None;
                }
                combos = next;
            }
            if !feasible {
                continue;
            }
            for c in combos {
                let t = Term { op, kids: c };
                if t.size() <= budget {
                    out.push(t);
                }
                if out.len() > MAX_TERMS {
                    return None;
                }
            }
        }
    }
    out.sort_by_key(|t| (t.size(), format!("{t:?}")));
    out.dedup();
    memo.insert((root, budget), Some(out.clone()));
    Some(out)
}

/// Plotkin's structural recurrence extended with projection-carrying mismatch
/// nodes, returning the production lexicographic quality key
/// `(size, variant_mass)`.
///
/// Same operator and arity recurses. Anything else is a generalized position,
/// represented here as `Variants(a, b)`. The cost model is the one the solver
/// documents: `size` counts the hidden projection mass `size(a) + size(b)`,
/// rather than assigning a standard lgg variable size one. `variant_mass` is
/// that same hidden mass, which makes `size - variant_mass` the shared backbone.
///
/// Getting this wrong is what the first run of this oracle caught, in the
/// oracle rather than in the solver: pricing a variable at one node made the
/// oracle claim a better optimum than exists.
fn plotkin(a: &Term, b: &Term) -> (u32, u32) {
    plotkin_mod(a, b, &[])
}

/// The projection-carrying recurrence, further extended to operators in `comm`
/// whose children are a multiset rather than a sequence.
///
/// For a commutative operator the positional zip is not the anti-unifier: any
/// bijection between the two member lists is admissible and the best one wins.
/// The oracle takes that literally and tries every permutation, which is only
/// tractable because the fixtures keep arities at two or three. The solver
/// reaches the same answer through a min-cost flow, so agreeing with an
/// exhaustive permutation search is the check on that transport.
///
/// Arities that differ are generalized whole: without a declared identity there
/// is no padding available, and no fixed-arity pattern instantiates to both
/// sides.
fn plotkin_mod(a: &Term, b: &Term, comm: &[OpId]) -> (u32, u32) {
    if a.op == b.op && a.kids.len() == b.kids.len() {
        if comm.contains(&a.op) {
            let n = a.kids.len();
            let mut best = (u32::MAX, u32::MAX);
            for perm in permutations(n) {
                let mut size = 1;
                let mut vmass = 0;
                for (i, &j) in perm.iter().enumerate() {
                    let (s, v) = plotkin_mod(&a.kids[i], &b.kids[j], comm);
                    size += s;
                    vmass += v;
                }
                if (size, vmass) < best {
                    best = (size, vmass);
                }
            }
            return best;
        }
        let mut size = 1;
        let mut vmass = 0;
        for (x, y) in a.kids.iter().zip(b.kids.iter()) {
            let (s, v) = plotkin_mod(x, y, comm);
            size += s;
            vmass += v;
        }
        (size, vmass)
    } else {
        let hidden = a.size() + b.size();
        (hidden, hidden)
    }
}

/// All permutations of `0..n`. `n` is an operator arity in these fixtures, so
/// it is two or three.
fn permutations(n: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let mut cur: Vec<usize> = (0..n).collect();
    permute(&mut cur, 0, &mut out);
    out
}

fn permute(cur: &mut Vec<usize>, k: usize, out: &mut Vec<Vec<usize>>) {
    if k == cur.len() {
        out.push(cur.clone());
        return;
    }
    for i in k..cur.len() {
        cur.swap(k, i);
        permute(cur, k + 1, out);
        cur.swap(k, i);
    }
}

/// The specification: the minimum over every pair of terms the two classes can
/// produce.
fn oracle(eg: &Eg, l: ENodeId, r: ENodeId, budget: u32) -> Option<(u32, u32)> {
    let mut memo = HashMap::new();
    let left = terms_of(eg, l, budget, &mut memo)?;
    let right = terms_of(eg, r, budget, &mut memo)?;
    if left.is_empty() || right.is_empty() {
        return None;
    }
    let mut best = (u32::MAX, u32::MAX);
    for a in &left {
        for b in &right {
            let q = plotkin(a, b);
            if q < best {
                best = q;
            }
        }
    }
    Some(best)
}

/// What the solver returns for the same pair.
fn solver(eg: &Eg, l: ENodeId, r: ENodeId) -> (u32, u32) {
    let snap = AuSnapshot::new(eg).unwrap();
    let res = anti_unify(
        &snap,
        l,
        r,
        &AuConfig {
            algorithm: AuAlgorithm::Exact,
            cycle_mode: CycleMode::Pair,
            exact_pruning: true,
            ..Default::default()
        },
    )
    .unwrap();
    assert_eq!(
        res.completion,
        Completion::Exact,
        "the solver must certify at this size"
    );
    (res.size, res.pool.variant_mass(res.term_id))
}

/// A small acyclic fixture, parameterized so the sweep covers several shapes.
/// `merges` unions pairs of built nodes, which is what gives classes more than
/// one member and therefore gives the solver a choice to get wrong.
fn fixture(depth: usize, merges: usize) -> (Eg, ENodeId, ENodeId) {
    let mut eg = Eg::new();
    let s = eg.intern_sort("S");
    let a = eg.register_op0("a", s);
    let b = eg.register_op0("b", s);
    let f = eg.register_op1("f", s, s);
    let g = eg.register_op1("g", s, s);
    let h = eg.register_op2("h", s, s, s);

    let na = eg.add(a, &[]);
    let nb = eg.add(b, &[]);
    let mut left = na;
    let mut right = nb;
    let mut built = vec![na, nb];
    for i in 0..depth {
        // Alternate the spine operators so the two sides share structure at some
        // levels and not others.
        let (ol, or) = if i % 2 == 0 { (f, f) } else { (f, g) };
        left = eg.add(ol, &[left]);
        right = eg.add(or, &[right]);
        built.push(left);
        built.push(right);
        let pair = eg.add(h, &[left, right]);
        built.push(pair);
    }
    // Unions give classes several members; each is a representation the solver
    // may pick and the oracle will also consider.
    for i in 0..merges {
        let x = built[(i * 3 + 1) % built.len()];
        let y = built[(i * 5 + 2) % built.len()];
        if x != y {
            eg.merge(x, y);
        }
    }
    eg.rebuild();
    (eg, left, right)
}

/// The solver's answer equals the brute-force minimum over all term pairs, on
/// every fixture in the sweep.
///
/// This is the strongest evidence available without a proof that the objective
/// is well defined on the quotient: the oracle never consults an e-class, only
/// the terms, so if the solver's answer depended on which member it enumerated
/// first, the two would disagree.
#[test]
fn solver_matches_brute_force_over_all_term_pairs() {
    let budget = 9;
    let mut checked = 0usize;
    for depth in 1..=3 {
        for merges in 0..=4 {
            let (eg, l, r) = fixture(depth, merges);
            // A fixture whose term set is unbounded or too large to enumerate is
            // skipped, not truncated: see `MAX_TERMS`.
            let Some(want) = oracle(&eg, l, r, budget) else {
                continue;
            };
            let got = solver(&eg, l, r);
            assert_eq!(
                got, want,
                "depth={depth} merges={merges}: solver returned {got:?}, brute force \
                 over all term pairs says {want:?}"
            );
            checked += 1;
        }
    }
    // Without this the test could pass by skipping everything.
    assert!(
        checked >= 6,
        "only {checked} fixtures were enumerable; the sweep is too weak"
    );
}

/// The size the solver reports is the size of the term it returns.
///
/// Trivial to state and worth pinning: every table in the records quotes
/// `result.size`, so a discrepancy between the reported number and the returned
/// term would silently invalidate all of them.
#[test]
fn reported_size_matches_the_returned_term() {
    for depth in 1..=3 {
        for merges in 0..=3 {
            let (eg, l, r) = fixture(depth, merges);
            let snap = AuSnapshot::new(&eg).unwrap();
            let res = anti_unify(
                &snap,
                l,
                r,
                &AuConfig {
                    algorithm: AuAlgorithm::Exact,
                    cycle_mode: CycleMode::Pair,
                    exact_pruning: true,
                    ..Default::default()
                },
            )
            .unwrap();
            assert_eq!(
                res.size,
                res.pool.size(res.term_id),
                "depth={depth} merges={merges}: reported size disagrees with the term"
            );
        }
    }
}

/// Pruning never changes the answer.
///
/// The bounds are what make the exact solver finish, and an inadmissible bound
/// shows up exactly here: it would prune a region containing the optimum and the
/// pruned run would report something worse than the unpruned one.
#[test]
fn pruning_does_not_change_the_optimum() {
    for depth in 1..=3 {
        for merges in 0..=4 {
            let (eg, l, r) = fixture(depth, merges);
            let snap = AuSnapshot::new(&eg).unwrap();
            let run = |pruning: bool| {
                let res = anti_unify(
                    &snap,
                    l,
                    r,
                    &AuConfig {
                        algorithm: AuAlgorithm::Exact,
                        cycle_mode: CycleMode::Pair,
                        exact_pruning: pruning,
                        ..Default::default()
                    },
                )
                .unwrap();
                assert_eq!(res.completion, Completion::Exact);
                (res.size, res.pool.variant_mass(res.term_id))
            };
            let bare = run(false);
            assert_eq!(
                run(true),
                bare,
                "depth={depth} merges={merges}: bounds pruning moved the optimum"
            );
        }
    }
}

/// Admissibility, checked exhaustively rather than argued.
///
/// `lb_pair(l, r)` is the precondition of every pruning rule in the solver: an
/// arm is excluded when its bound exceeds the incumbent, so a bound that ever
/// exceeds the true optimum would prune the answer. Chapter 19 §9.2 argues it
/// holds. This checks it, for every ordered pair of classes in the fixture and
/// not only for the roots, against the brute-force optimum of that same pair.
///
/// The two cases the bound distinguishes are both covered, because the sweep
/// includes merges: `l == r`, where the bound is `bs(l)` and is meant to be
/// tight, and `l != r`, where it is `max(bs_l, bs_r) + 1`.
#[test]
fn lb_pair_never_exceeds_the_true_optimum() {
    let budget = 8;
    let mut checked = 0usize;
    let mut tight = 0usize;
    for depth in 1..=3 {
        for merges in 0..=4 {
            let (eg, _, _) = fixture(depth, merges);
            let snap = AuSnapshot::new(&eg).unwrap();
            let classes: Vec<_> = eg
                .node_ids()
                .map(|id| eg.find_const(id))
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect();
            for &a in &classes {
                for &b in &classes {
                    let Some(want) = oracle(&eg, a, b, budget) else {
                        continue;
                    };
                    let (Some(ca), Some(cb)) = (snap.class_of(a), snap.class_of(b)) else {
                        continue;
                    };
                    let (bound, _) = semi_persistent_egraph::au::estimates::lb_pair(&snap, ca, cb);
                    assert!(
                        bound <= want.0,
                        "depth={depth} merges={merges}: lb_pair says {bound} but the \
                         true optimum is {}; an inadmissible bound prunes the answer",
                        want.0
                    );
                    if bound == want.0 {
                        tight += 1;
                    }
                    checked += 1;
                }
            }
        }
    }
    assert!(
        checked >= 100,
        "only {checked} class pairs were enumerable; the sweep is too weak"
    );
    // A bound of zero would be admissible and useless. This is the check that
    // the sweep exercises the bound rather than a degenerate case.
    assert!(
        tight > 0,
        "the bound was never tight over {checked} pairs, so the sweep proves nothing \
         about its usefulness"
    );
}

/// Edge-count sharing preserves the optimum.
///
/// The solver computes over a DAG and prices an AND node at
/// `1 + sum over children of count * L(child)`, counting edges rather than
/// nodes, so a child reachable by several paths is solved once and charged
/// several times. That this gives the same optimum as the tree unfolding is the
/// step where a double-count would hide.
///
/// The oracle settles it without a separate mechanism: Plotkin runs over ground
/// terms, which are fully unfolded and share nothing, so agreement between the
/// two IS the statement that sharing preserved the optimum. This test makes the
/// claim explicit by running the comparison on the fixtures with the most
/// sharing, which are the ones with the most merges.
#[test]
fn edge_count_sharing_agrees_with_the_unfolded_optimum() {
    let budget = 9;
    let mut checked = 0usize;
    for depth in 2..=3 {
        for merges in 2..=4 {
            let (eg, l, r) = fixture(depth, merges);
            let Some(want) = oracle(&eg, l, r, budget) else {
                continue;
            };
            assert_eq!(
                solver(&eg, l, r),
                want,
                "depth={depth} merges={merges}: the DAG computation disagrees with the \
                 unfolded one, which is what a double-count looks like"
            );
            checked += 1;
        }
    }
    assert!(
        checked >= 3,
        "only {checked} sharing-heavy fixtures were enumerable"
    );
}

/// A fixture with a commutative binary operator, so the member matching is a
/// choice rather than a positional zip.
fn comm_fixture(depth: usize, merges: usize) -> (Eg, ENodeId, ENodeId, Vec<OpId>) {
    let mut eg = Eg::new();
    let s = eg.intern_sort("S");
    let a = eg.register_op0("a", s);
    let b = eg.register_op0("b", s);
    let c = eg.register_op0("c", s);
    let f = eg.register_op1("f", s, s);
    // A multiset operator: its children are a multiset, so matching them
    // between two nodes is a choice rather than a positional zip.
    let p = eg.register_mset("p", s, s);

    let na = eg.add(a, &[]);
    let nb = eg.add(b, &[]);
    let nc = eg.add(c, &[]);
    let mut left = eg.add(p, &[na, nb]);
    let mut right = eg.add(p, &[nb, nc]);
    let mut built = vec![na, nb, nc, left, right];
    for i in 0..depth {
        // Argument order is swapped on one side each level. Under a multiset
        // operator those are the same node after canonization, so a cost
        // difference between them would be a canonization defect.
        let fa = eg.add(f, &[na]);
        let fc = eg.add(f, &[nc]);
        left = if i % 2 == 0 {
            eg.add(p, &[left, fa])
        } else {
            eg.add(p, &[fa, left])
        };
        right = eg.add(p, &[fc, right]);
        built.push(left);
        built.push(right);
    }
    for i in 0..merges {
        let x = built[(i * 3 + 1) % built.len()];
        let y = built[(i * 7 + 2) % built.len()];
        if x != y {
            eg.merge(x, y);
        }
    }
    eg.rebuild();
    (eg, left, right, vec![p])
}

/// The solver's AC transport agrees with an exhaustive search over member
/// matchings.
///
/// This is the gap the free-symbol oracle above leaves open. For a commutative
/// operator the anti-unifier is the best bijection between the two member
/// lists, which the solver finds with a min-cost flow. The oracle tries every
/// permutation instead, so agreement is an independent check on the transport
/// rather than on the search around it.
#[test]
fn ac_transport_agrees_with_exhaustive_member_matching() {
    let budget = 9;
    let mut checked = 0usize;
    for depth in 1..=2 {
        for merges in 0..=3 {
            let (eg, l, r, comm) = comm_fixture(depth, merges);
            let mut memo = HashMap::new();
            let (Some(left), Some(right)) = (
                terms_of(&eg, l, budget, &mut memo),
                terms_of(&eg, r, budget, &mut memo),
            ) else {
                continue;
            };
            if left.is_empty() || right.is_empty() {
                continue;
            }
            let mut want = (u32::MAX, u32::MAX);
            for x in &left {
                for y in &right {
                    let q = plotkin_mod(x, y, &comm);
                    if q < want {
                        want = q;
                    }
                }
            }
            assert_eq!(
                solver(&eg, l, r),
                want,
                "depth={depth} merges={merges}: the transport disagrees with an \
                 exhaustive search over member matchings"
            );
            checked += 1;
        }
    }
    assert!(
        checked >= 4,
        "only {checked} commutative fixtures were enumerable"
    );
}

/// The answer depends on the classes, not on how they were named or ordered.
///
/// Well-definedness on the quotient is the one property under the optimality
/// claim with no mechanical check, and a proof is the right instrument. This is
/// the next best thing and it is a direct test rather than an inference: build
/// the same e-graph with the merges applied in a different order, so the
/// union-find picks different representatives and each class enumerates its
/// members in a different order, and assert the solver returns the same answer.
///
/// A cost model that accidentally read the representative, or a search that
/// stopped at the first member it happened to visit, would differ here. It is
/// still evidence and not a proof: it samples orderings rather than quantifying
/// over them.
#[test]
fn the_optimum_does_not_depend_on_merge_order() {
    for depth in 1..=3 {
        for merges in 1..=4 {
            let forward = {
                let (eg, l, r) = fixture(depth, merges);
                solver(&eg, l, r)
            };
            let reversed = {
                let (eg, l, r) = fixture_rev(depth, merges);
                solver(&eg, l, r)
            };
            assert_eq!(
                forward, reversed,
                "depth={depth} merges={merges}: the optimum moved when the merges were \
                 applied in the opposite order, so it is reading the representative \
                 rather than the class"
            );
        }
    }
}

/// `fixture` with the merges applied back to front. Same e-graph as a quotient,
/// different representatives and different member orders.
fn fixture_rev(depth: usize, merges: usize) -> (Eg, ENodeId, ENodeId) {
    let mut eg = Eg::new();
    let s = eg.intern_sort("S");
    let a = eg.register_op0("a", s);
    let b = eg.register_op0("b", s);
    let f = eg.register_op1("f", s, s);
    let g = eg.register_op1("g", s, s);
    let h = eg.register_op2("h", s, s, s);

    let na = eg.add(a, &[]);
    let nb = eg.add(b, &[]);
    let mut left = na;
    let mut right = nb;
    let mut built = vec![na, nb];
    for i in 0..depth {
        let (ol, or) = if i % 2 == 0 { (f, f) } else { (f, g) };
        left = eg.add(ol, &[left]);
        right = eg.add(or, &[right]);
        built.push(left);
        built.push(right);
        let pair = eg.add(h, &[left, right]);
        built.push(pair);
    }
    // The one difference: same merge set, opposite order, and each union is
    // applied with its arguments swapped so the survivor differs too.
    for i in (0..merges).rev() {
        let x = built[(i * 3 + 1) % built.len()];
        let y = built[(i * 5 + 2) % built.len()];
        if x != y {
            eg.merge(y, x);
        }
    }
    eg.rebuild();
    (eg, left, right)
}

/// The lemma §9.6 rests on: a lexicographic minimum decomposes over independent
/// sums, so summing per-child optima gives the parent's optimum.
///
/// It is the step that makes a dynamic program valid for a lexicographic
/// objective at all. Obvious for a scalar objective; not obvious here, because a
/// child could in principle trade size for variant mass. This checks the lemma
/// directly on the pair arithmetic, over every combination of small achievable
/// sets, rather than trusting the paper argument alone.
#[test]
fn lexicographic_minimum_decomposes_over_sums() {
    // Achievable sets a child might offer, including ones that tempt a trade:
    // (2, 5) is smaller in size and larger in mass than (3, 0).
    let sets: Vec<Vec<(u32, u32)>> = vec![
        vec![(2, 5), (3, 0)],
        vec![(1, 1), (1, 0), (4, 0)],
        vec![(3, 3), (2, 9)],
        vec![(5, 0)],
    ];
    for i in 0..sets.len() {
        for j in 0..sets.len() {
            for k in 0..sets.len() {
                let children = [&sets[i], &sets[j], &sets[k]];
                // Sum of the per-child lexicographic minima.
                let decomposed = children.iter().fold((0u32, 0u32), |acc, s| {
                    let m = s.iter().min().copied().unwrap();
                    (acc.0 + m.0, acc.1 + m.1)
                });
                // Lexicographic minimum over the whole product.
                let mut direct = (u32::MAX, u32::MAX);
                for &a in children[0] {
                    for &b in children[1] {
                        for &c in children[2] {
                            let sum = (a.0 + b.0 + c.0, a.1 + b.1 + c.1);
                            if sum < direct {
                                direct = sum;
                            }
                        }
                    }
                }
                assert_eq!(
                    decomposed, direct,
                    "sets {i}/{j}/{k}: summing per-child lexicographic minima gave \
                     {decomposed:?} but the minimum over the product is {direct:?}"
                );
            }
        }
    }
}
