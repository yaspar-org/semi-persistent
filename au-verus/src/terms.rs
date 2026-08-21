// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The positional term model used by the recurrence lower-bound theorem.
//!
//! `recurrence.rs` checks objective algebra and a conditional set-minimum
//! lemma. `completeness.rs` uses the definitions here to prove that any
//! function satisfying the current recurrence inequalities is below every
//! represented positional term pair. No declaration in these modules defines
//! a selected recurrence solution or proves that it equals `OPT`.
//!
//! What is assumed and what is proved. The e-graph's meaning is the interface
//! here, not a result: `terms_intro` and `terms_elim` state that a class
//! represents exactly the terms built by picking one of its members and a term
//! from each child class. Those two are the definition of what an e-graph
//! represents, and they are the only assumptions. Everything else is proved.

use vstd::prelude::*;

verus! {

/// A ground term: an operator and its children.
pub struct Term {
    pub op: nat,
    pub kids: Seq<Term>,
}

/// Height of a term, the measure every induction below decreases on.
pub open spec fn term_height(t: Term) -> nat
    decreases t,
{
    1 + kids_height(t.kids)
}

pub open spec fn kids_height(s: Seq<Term>) -> nat
    decreases s,
{
    if s.len() == 0 {
        0
    } else {
        let h = term_height(s[0]);
        let r = kids_height(s.subrange(1, s.len() as int));
        if h > r { h } else { r }
    }
}

/// Every child is no taller than the list it belongs to.
pub proof fn lemma_kid_height_le(s: Seq<Term>, i: int)
    requires 0 <= i < s.len(),
    ensures term_height(s[i]) <= kids_height(s),
    decreases s.len(),
{
    if i > 0 {
        let rest = s.subrange(1, s.len() as int);
        assert(rest[i - 1] == s[i]);
        lemma_kid_height_le(rest, i - 1);
    }
}

/// Node count.
///
/// The measure is a lexicographic triple, and each component earns its place.
/// Height leads, because a term is taller than its child list. The middle
/// component orders the two functions at equal height, so a list may call into
/// its head even when the head is the tallest element. The length breaks the
/// remaining tie when a list calls its own tail at unchanged height.
pub open spec fn term_size(t: Term) -> nat
    decreases term_height(t), 0nat, 0nat,
{
    1 + kids_size(t.kids)
}

pub open spec fn kids_size(s: Seq<Term>) -> nat
    decreases kids_height(s), 1nat, s.len(),
{
    if s.len() == 0 {
        0
    } else {
        proof {
            lemma_kid_height_le(s, 0);
            lemma_kids_height_tail(s);
        }
        term_size(s[0]) + kids_size(s.subrange(1, s.len() as int))
    }
}

/// A tail is no taller than the list it came from.
pub proof fn lemma_kids_height_tail(s: Seq<Term>)
    requires s.len() > 0,
    ensures kids_height(s.subrange(1, s.len() as int)) <= kids_height(s),
{
}

/// A term's size is at least one: every term has a root.
pub proof fn lemma_term_size_positive(t: Term)
    ensures term_size(t) >= 1,
{
}

/// Plotkin's first-order anti-unification, as a quality rather than a term.
///
/// Matching operators recurse; anything else is a generalized position costing
/// the mass it hides, which is the cost model chapter 19 documents: `size`
/// counts concrete nodes, so `size - mass` is the shared backbone.
///
/// The measure is the triple again, summed over the two sides.
pub open spec fn plotkin(a: Term, b: Term) -> crate::objective::Quality
    decreases term_height(a) + term_height(b), 0nat, 0nat,
{
    if a.op == b.op && a.kids.len() == b.kids.len() {
        proof {
            lemma_kids_height_sum(a, b);
        }
        crate::objective::add(
            crate::objective::Quality { size: 1, mass: 0 },
            zip_plotkin(a.kids, b.kids),
        )
    } else {
        let hidden = (term_size(a) + term_size(b)) as nat;
        crate::objective::Quality { size: hidden, mass: hidden }
    }
}

pub open spec fn zip_plotkin(xs: Seq<Term>, ys: Seq<Term>) -> crate::objective::Quality
    decreases kids_height(xs) + kids_height(ys), 1nat, xs.len(),
{
    if xs.len() == 0 || ys.len() == 0 {
        crate::objective::Quality { size: 0, mass: 0 }
    } else {
        proof {
            lemma_kid_height_le(xs, 0);
            lemma_kid_height_le(ys, 0);
            lemma_kids_height_tail(xs);
            lemma_kids_height_tail(ys);
        }
        crate::objective::add(
            plotkin(xs[0], ys[0]),
            zip_plotkin(xs.subrange(1, xs.len() as int), ys.subrange(1, ys.len() as int)),
        )
    }
}

/// The child lists of two terms are jointly shorter than the terms are tall,
/// which is what lets `plotkin` call `zip_plotkin`.
pub proof fn lemma_kids_height_sum(a: Term, b: Term)
    ensures kids_height(a.kids) + kids_height(b.kids) < term_height(a) + term_height(b),
{
}

/// Anti-unifying a term with itself costs exactly the term: nothing is
/// generalized, so the backbone is the whole thing and the mass is zero.
///
/// The base case of the correspondence between this model and the solver, and
/// the one case where the answer is known without any search.
pub proof fn lemma_plotkin_reflexive(t: Term)
    ensures
        plotkin(t, t).size == term_size(t),
        plotkin(t, t).mass == 0,
    decreases term_height(t), 0nat, 0nat,
{
    lemma_zip_plotkin_reflexive(t.kids);
}

pub proof fn lemma_zip_plotkin_reflexive(s: Seq<Term>)
    ensures
        zip_plotkin(s, s).size == kids_size(s),
        zip_plotkin(s, s).mass == 0,
    decreases kids_height(s), 1nat, s.len(),
{
    if s.len() > 0 {
        lemma_kid_height_le(s, 0);
        lemma_kids_height_tail(s);
        lemma_plotkin_reflexive(s[0]);
        lemma_zip_plotkin_reflexive(s.subrange(1, s.len() as int));
    }
}

} // verus!
