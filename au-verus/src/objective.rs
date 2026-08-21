// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The anti-unification quality key and the lemma the dynamic program rests on.
//!
//! Quality is the pair `(size, variant_mass)` ordered lexicographically, where
//! `size` counts concrete nodes and `variant_mass` counts those under a
//! generalized position. Both components are additive over an anti-unifier's
//! children, and the children are chosen independently.
//!
//! The step that needs checking is that a lexicographic minimum decomposes over
//! those independent sums. It is obvious for a scalar objective and not obvious
//! here: a child could in principle accept a larger size to buy a smaller mass,
//! and if that trade ever paid, summing per-child optima would not give the
//! parent's optimum and the whole dynamic program would be invalid.
//!
//! It never pays, and this is the proof.

use vstd::prelude::*;

verus! {

/// The quality of an anti-unifier: `(size, variant_mass)`.
pub struct Quality {
    pub size: nat,
    pub mass: nat,
}

/// Lexicographic order: smaller size wins; at equal size, smaller mass wins.
pub open spec fn leq(a: Quality, b: Quality) -> bool {
    a.size < b.size || (a.size == b.size && a.mass <= b.mass)
}

/// Componentwise addition, which is how a parent's quality is built from its
/// children: sizes add, masses add.
pub open spec fn add(a: Quality, b: Quality) -> Quality {
    Quality { size: (a.size + b.size) as nat, mass: (a.mass + b.mass) as nat }
}

/// The order is total, so "the minimum" is well defined.
pub proof fn lemma_leq_total(a: Quality, b: Quality)
    ensures leq(a, b) || leq(b, a),
{
}

/// The order is transitive.
pub proof fn lemma_leq_transitive(a: Quality, b: Quality, c: Quality)
    requires leq(a, b), leq(b, c),
    ensures leq(a, c),
{
}

/// **The decomposition lemma, two children.**
///
/// If `a` is at least as good as any alternative `x` for the first child, and
/// `b` for the second, then their sum is at least as good as the sum of the
/// alternatives. This is what licenses choosing each child's optimum
/// independently and adding.
///
/// The proof is the whole argument in miniature: a strict increase in one
/// child's size cannot be paid back by another child's mass, because size is
/// compared first and masses only break ties among size-minimal choices.
pub proof fn lemma_add_monotone(a: Quality, x: Quality, b: Quality, y: Quality)
    requires leq(a, x), leq(b, y),
    ensures leq(add(a, b), add(x, y)),
{
    if a.size < x.size {
        assert(add(a, b).size < add(x, y).size);
    } else if b.size < y.size {
        assert(add(a, b).size < add(x, y).size);
    } else {
        // Neither child grew, so both sizes are equal and the masses decide,
        // each of them componentwise.
        assert(a.size == x.size);
        assert(b.size == y.size);
        assert(a.mass <= x.mass);
        assert(b.mass <= y.mass);
    }
}

/// Adding a constant to both sides preserves the order. The constant is the one
/// node an anti-unifier spends on the operator it matched.
pub proof fn lemma_add_constant_monotone(a: Quality, b: Quality, k: Quality)
    requires leq(a, b),
    ensures leq(add(k, a), add(k, b)),
{
    lemma_add_monotone(k, k, a, b);
}

/// The decomposition lemma over a sequence of children, which is the form the
/// recurrence actually uses: an operator of any arity.
///
/// `best` is a per-child optimum and `alt` any other admissible choice. Folding
/// both and comparing gives the same conclusion at every arity.
pub open spec fn fold(s: Seq<Quality>) -> Quality
    decreases s.len(),
{
    if s.len() == 0 {
        Quality { size: 0, mass: 0 }
    } else {
        add(s[0], fold(s.subrange(1, s.len() as int)))
    }
}

/// **The decomposition lemma at arbitrary arity.**
///
/// If every child's chosen quality is at least as good as the alternative's,
/// the folded sum is at least as good as the folded alternative. Induction on
/// the number of children, with `lemma_add_monotone` at each step.
pub proof fn lemma_fold_monotone(best: Seq<Quality>, alt: Seq<Quality>)
    requires
        best.len() == alt.len(),
        forall|i: int| 0 <= i < best.len() ==> leq(#[trigger] best[i], alt[i]),
    ensures leq(fold(best), fold(alt)),
    decreases best.len(),
{
    if best.len() == 0 {
    } else {
        let bt = best.subrange(1, best.len() as int);
        let at = alt.subrange(1, alt.len() as int);
        assert forall|i: int| 0 <= i < bt.len() implies leq(#[trigger] bt[i], at[i]) by {
            assert(bt[i] == best[i + 1]);
            assert(at[i] == alt[i + 1]);
        }
        lemma_fold_monotone(bt, at);
        lemma_add_monotone(best[0], alt[0], fold(bt), fold(at));
    }
}

} // verus!
