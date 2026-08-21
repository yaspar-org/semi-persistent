// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! A lower-bound theorem for functions satisfying recurrence inequalities.
//!
//! This module does not define or select a recurrence solution. In particular,
//! the constant-zero quality function satisfies the inequalities below. The
//! theorem therefore proves a useful lower-bound property, not optimality or
//! attainability.
//!
//! # Why the theorem is stated over any `d` satisfying the inequalities
//!
//! A class may represent infinitely many terms and a class pair may reach
//! itself, so the recurrence is not a well-founded definition over classes and
//! cannot be written as a `spec fn` with a `decreases`. The paper proof does not
//! need it to be: its induction runs on `|s| + |t|`, which is finite for every
//! term pair even when the class is cyclic.
//!
//! So `d` here is any function satisfying the two inequalities and the theorem
//! is that any such function is a lower bound. Connecting this predicate to the
//! production solver, or showing that a least/selected solution is attainable,
//! is separate proof work.
//!
//! # What is assumed
//!
//! `represents` and `bs` are uninterpreted, constrained by the four properties
//! below. They are the definition of what an e-graph means, not results:
//! a class represents exactly the terms built from one of its members and a term
//! from each child class, and `bs` is the size of its smallest term.

use vstd::prelude::*;

verus! {

#[allow(unused_imports)]
use crate::objective::Quality;
#[allow(unused_imports)]
use crate::terms::Term;

pub type ClassId = nat;

/// A member of a class: an operator and the classes of its children.
pub struct Member {
    pub op: nat,
    pub kids: Seq<ClassId>,
}

/// The e-graph, as the two relations the argument needs.
pub struct Model {
    /// The members of each class.
    pub members: spec_fn(ClassId) -> Set<Member>,
    /// Which terms a class represents.
    pub represents: spec_fn(ClassId, Term) -> bool,
    /// The size of the class's smallest term.
    pub bs: spec_fn(ClassId) -> nat,
    /// A smallest term of the class. The witness direction needs a term in
    /// hand, not just the assertion that one exists, so the model supplies it.
    pub min_term: spec_fn(ClassId) -> Term,
}

/// A class represents a term exactly when some member's operator and arity
/// match it and each child class represents the corresponding child term.
///
/// Both directions are assumed: this is the meaning of the e-graph.
pub open spec fn model_wf(m: Model) -> bool {
    &&& forall|c: ClassId, t: Term| #[trigger] (m.represents)(c, t) ==> exists|mem: Member|
            (m.members)(c).contains(mem) && mem.op == t.op && mem.kids.len() == t.kids.len()
            && forall|i: int| 0 <= i < mem.kids.len() ==> (m.represents)(mem.kids[i], t.kids[i])
    &&& forall|c: ClassId, t: Term| #[trigger] (m.represents)(c, t) ==> (m.bs)(c) <= crate::terms::term_size(t)
    // The other direction of the meaning: a member plus a term from each child
    // class builds a term the class represents. `model_wf`'s first clause takes
    // a term apart; this puts one together, and the witness direction needs it.
    &&& forall|c: ClassId, mem: Member, t: Term|
            #![trigger (m.members)(c).contains(mem), (m.represents)(c, t)]
            (m.members)(c).contains(mem) && mem.op == t.op
            && mem.kids.len() == t.kids.len()
            && (forall|i: int| 0 <= i < mem.kids.len() ==> (m.represents)(mem.kids[i], t.kids[i]))
            ==> (m.represents)(c, t)
    // The smallest term is a term of the class, and it has the smallest size.
    &&& forall|c: ClassId| #[trigger] (m.represents)(c, (m.min_term)(c))
    &&& forall|c: ClassId| crate::terms::term_size(#[trigger] (m.min_term)(c)) == (m.bs)(c)
}

/// The quality of generalizing a class pair: the two smallest terms' mass.
pub open spec fn generalize_cost(m: Model, a: ClassId, b: ClassId) -> Quality {
    let h = ((m.bs)(a) + (m.bs)(b)) as nat;
    Quality { size: h, mass: h }
}

/// Folding a value function over paired child classes, which is what a
/// structural action costs below the operator node.
pub open spec fn fold_kids(
    d: spec_fn(ClassId, ClassId) -> Quality,
    xs: Seq<ClassId>,
    ys: Seq<ClassId>,
) -> Quality
    decreases xs.len(),
{
    if xs.len() == 0 || ys.len() == 0 {
        Quality { size: 0, mass: 0 }
    } else {
        crate::objective::add(
            d(xs[0], ys[0]),
            fold_kids(d, xs.subrange(1, xs.len() as int), ys.subrange(1, ys.len() as int)),
        )
    }
}

/// The two inequalities the solver's value satisfies at every state: it is no
/// worse than generalizing, and no worse than any structural action.
pub open spec fn satisfies_recurrence_lower_bounds(
    m: Model,
    d: spec_fn(ClassId, ClassId) -> Quality,
) -> bool {
    &&& forall|a: ClassId, b: ClassId|
            crate::objective::leq(#[trigger] d(a, b), generalize_cost(m, a, b))
    &&& forall|a: ClassId, b: ClassId, ma: Member, mb: Member|
            #[trigger] (m.members)(a).contains(ma) && #[trigger] (m.members)(b).contains(mb)
            && ma.op == mb.op && ma.kids.len() == mb.kids.len()
            ==> crate::objective::leq(
                    d(a, b),
                    crate::objective::add(
                        Quality { size: 1, mass: 0 },
                        fold_kids(d, ma.kids, mb.kids),
                    ),
                )
}

/// Generalizing is never worse than any term pair, because `bs` is below every
/// represented term's size.
pub proof fn lemma_generalize_below_any_pair(m: Model, a: ClassId, b: ClassId, s: Term, t: Term)
    requires
        model_wf(m),
        (m.represents)(a, s),
        (m.represents)(b, t),
    ensures
        crate::objective::leq(
            generalize_cost(m, a, b),
            Quality {
                size: (crate::terms::term_size(s) + crate::terms::term_size(t)) as nat,
                mass: (crate::terms::term_size(s) + crate::terms::term_size(t)) as nat,
            },
        ),
{
}

/// Anti-unifying two terms never costs more than hiding them both.
///
/// Matching roots can only share, and mismatched roots pay exactly the two
/// sizes. This is the step that turns the generalize action from an upper bound
/// on cost into a witness that something at least that good is achievable.
pub proof fn lemma_plotkin_below_hiding(s: Term, t: Term)
    ensures
        crate::objective::leq(
            crate::terms::plotkin(s, t),
            Quality {
                size: (crate::terms::term_size(s) + crate::terms::term_size(t)) as nat,
                mass: (crate::terms::term_size(s) + crate::terms::term_size(t)) as nat,
            },
        ),
    decreases crate::terms::term_height(s) + crate::terms::term_height(t), 0nat, 0nat,
{
    if s.op == t.op && s.kids.len() == t.kids.len() {
        crate::terms::lemma_kids_height_sum(s, t);
        lemma_zip_below_hiding(s.kids, t.kids);
    }
}

/// The child-list form: a zipped anti-unification never costs more than the two
/// child lists together.
pub proof fn lemma_zip_below_hiding(xs: Seq<Term>, ys: Seq<Term>)
    requires xs.len() == ys.len(),
    ensures
        crate::terms::zip_plotkin(xs, ys).size
            <= crate::terms::kids_size(xs) + crate::terms::kids_size(ys),
    decreases
        crate::terms::kids_height(xs) + crate::terms::kids_height(ys), 1nat, xs.len(),
{
    if xs.len() > 0 {
        crate::terms::lemma_kid_height_le(xs, 0);
        crate::terms::lemma_kid_height_le(ys, 0);
        crate::terms::lemma_kids_height_tail(xs);
        crate::terms::lemma_kids_height_tail(ys);
        lemma_plotkin_below_hiding(xs[0], ys[0]);
        lemma_zip_below_hiding(xs.subrange(1, xs.len() as int), ys.subrange(1, ys.len() as int));
    }
}

/// The two minimum-size represented terms are no worse than hiding both terms.
///
/// This witnesses a quality at most `generalize_cost`; it does not relate that
/// witness to an arbitrary `d` or prove that a recurrence value is attained.
pub proof fn lemma_generalize_has_no_worse_witness(m: Model, a: ClassId, b: ClassId)
    requires model_wf(m),
    ensures
        (m.represents)(a, (m.min_term)(a)),
        (m.represents)(b, (m.min_term)(b)),
        crate::objective::leq(
            crate::terms::plotkin((m.min_term)(a), (m.min_term)(b)),
            generalize_cost(m, a, b),
        ),
{
    lemma_plotkin_below_hiding((m.min_term)(a), (m.min_term)(b));
}

/// Assemble represented child terms into represented parent terms.
///
/// The postcondition is representation only. It states no quality relation and
/// is therefore not an attainability theorem for a structural action.
pub proof fn lemma_structural_terms_are_represented(
    m: Model,
    a: ClassId,
    b: ClassId,
    ma: Member,
    mb: Member,
    s: Term,
    t: Term,
)
    requires
        model_wf(m),
        (m.members)(a).contains(ma),
        (m.members)(b).contains(mb),
        ma.op == s.op,
        mb.op == t.op,
        ma.kids.len() == s.kids.len(),
        mb.kids.len() == t.kids.len(),
        forall|i: int| 0 <= i < ma.kids.len() ==> (m.represents)(ma.kids[i], #[trigger] s.kids[i]),
        forall|i: int| 0 <= i < mb.kids.len() ==> (m.represents)(mb.kids[i], #[trigger] t.kids[i]),
    ensures
        (m.represents)(a, s),
        (m.represents)(b, t),
{
}

/// **The theorem.** Any value satisfying the recurrence is a lower bound on
/// every term pair the two classes represent.
///
/// Induction on the two terms' combined height, which is finite for each pair
/// even when the classes are cyclic, so no well-foundedness over classes is
/// needed.
#[verifier::rlimit(60)]
pub proof fn lemma_recurrence_below_every_pair(
    m: Model,
    d: spec_fn(ClassId, ClassId) -> Quality,
    a: ClassId,
    b: ClassId,
    s: Term,
    t: Term,
)
    requires
        model_wf(m),
        satisfies_recurrence_lower_bounds(m, d),
        (m.represents)(a, s),
        (m.represents)(b, t),
    ensures
        crate::objective::leq(d(a, b), crate::terms::plotkin(s, t)),
    // The same lexicographic triple the term functions use: combined height
    // leads, the middle component orders these two mutually recursive lemmas at
    // equal height, and the length breaks the remaining tie.
    decreases crate::terms::term_height(s) + crate::terms::term_height(t), 0nat, 0nat,
{
    crate::terms::lemma_kids_height_sum(s, t);
    if s.op == t.op && s.kids.len() == t.kids.len() {
        // Both classes have a member matching the term's root, by `model_wf`.
        let ma = choose|ma: Member|
            (m.members)(a).contains(ma) && ma.op == s.op && ma.kids.len() == s.kids.len()
            && forall|i: int| 0 <= i < ma.kids.len() ==> (m.represents)(ma.kids[i], s.kids[i]);
        let mb = choose|mb: Member|
            (m.members)(b).contains(mb) && mb.op == t.op && mb.kids.len() == t.kids.len()
            && forall|i: int| 0 <= i < mb.kids.len() ==> (m.represents)(mb.kids[i], t.kids[i]);
        lemma_kids_below(m, d, ma.kids, mb.kids, s.kids, t.kids);
        crate::objective::lemma_add_monotone(
            Quality { size: 1, mass: 0 },
            Quality { size: 1, mass: 0 },
            fold_kids(d, ma.kids, mb.kids),
            crate::terms::zip_plotkin(s.kids, t.kids),
        );
        crate::objective::lemma_leq_transitive(
            d(a, b),
            crate::objective::add(Quality { size: 1, mass: 0 }, fold_kids(d, ma.kids, mb.kids)),
            crate::terms::plotkin(s, t),
        );
    } else {
        lemma_generalize_below_any_pair(m, a, b, s, t);
        crate::objective::lemma_leq_transitive(
            d(a, b),
            generalize_cost(m, a, b),
            crate::terms::plotkin(s, t),
        );
    }
}

/// The child-list form of the theorem, folded on both sides.
#[verifier::rlimit(60)]
pub proof fn lemma_kids_below(
    m: Model,
    d: spec_fn(ClassId, ClassId) -> Quality,
    ka: Seq<ClassId>,
    kb: Seq<ClassId>,
    sa: Seq<Term>,
    sb: Seq<Term>,
)
    requires
        model_wf(m),
        satisfies_recurrence_lower_bounds(m, d),
        ka.len() == sa.len(),
        kb.len() == sb.len(),
        sa.len() == sb.len(),
        forall|i: int| 0 <= i < ka.len() ==> (m.represents)(ka[i], #[trigger] sa[i]),
        forall|i: int| 0 <= i < kb.len() ==> (m.represents)(kb[i], #[trigger] sb[i]),
    ensures
        crate::objective::leq(fold_kids(d, ka, kb), crate::terms::zip_plotkin(sa, sb)),
    decreases
        crate::terms::kids_height(sa) + crate::terms::kids_height(sb), 1nat, sa.len(),
{
    if sa.len() > 0 {
        crate::terms::lemma_kid_height_le(sa, 0);
        crate::terms::lemma_kid_height_le(sb, 0);
        crate::terms::lemma_kids_height_tail(sa);
        crate::terms::lemma_kids_height_tail(sb);
        lemma_recurrence_below_every_pair(m, d, ka[0], kb[0], sa[0], sb[0]);
        lemma_kids_below(
            m,
            d,
            ka.subrange(1, ka.len() as int),
            kb.subrange(1, kb.len() as int),
            sa.subrange(1, sa.len() as int),
            sb.subrange(1, sb.len() as int),
        );
        crate::objective::lemma_add_monotone(
            d(ka[0], kb[0]),
            crate::terms::plotkin(sa[0], sb[0]),
            fold_kids(d, ka.subrange(1, ka.len() as int), kb.subrange(1, kb.len() as int)),
            crate::terms::zip_plotkin(sa.subrange(1, sa.len() as int), sb.subrange(1, sb.len() as int)),
        );
    }
}

} // verus!
