// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Objective-order lemmas for an abstract action set.
//!
//! The key set-minimum lemma is conditional: its precondition already says the
//! selected action belongs to the set and is no worse than every action. This
//! module does not prove that a recurrence or solver selects such an action.

use vstd::prelude::*;

verus! {

// Only the struct is imported. `leq`, `add`, `fold` and the lemmas are spec and
// proof items, which plain rustc erases when it expands `verus!`, so importing
// them by name breaks `cargo build` even though `cargo verus verify` is happy.
// Full paths at the call sites are erased along with the calls.
#[allow(unused_imports)]
use crate::objective::Quality;

/// An action available at a state: either generalize, paying both sides' mass,
/// or match an operator and recurse into the paired children.
pub enum Action {
    /// The single generalized position: quality is the mass it hides.
    Generalize(Quality),
    /// One structural match: one node for the operator, plus the children.
    Match(Seq<Quality>),
}

/// What an action costs, given the quality achieved at each child.
pub open spec fn action_cost(a: Action) -> Quality {
    match a {
        Action::Generalize(q) => q,
        Action::Match(kids) => crate::objective::add(Quality { size: 1, mass: 0 }, crate::objective::fold(kids)),
    }
}

/// `best` is the minimum of the achievable set when it is achievable and no
/// alternative beats it. This is the specification the recurrence must meet.
pub open spec fn is_min(best: Quality, achievable: Set<Quality>) -> bool {
    &&& achievable.contains(best)
    &&& forall|q: Quality| #[trigger] achievable.contains(q) ==> crate::objective::leq(best, q)
}

/// **Choosing the better of two actions is choosing the minimum of the two.**
///
/// Trivial on its own, and stated because the recurrence is a fold of exactly
/// this step over the action list, so its correctness is this plus totality.
pub proof fn lemma_pick_better(a: Quality, b: Quality)
    ensures
        (crate::objective::leq(a, b) ==> crate::objective::leq(a, a) && crate::objective::leq(a, b)),
        (!crate::objective::leq(a, b) ==> crate::objective::leq(b, a)),
{
    crate::objective::lemma_leq_total(a, b);
}

/// **A structural action improves when its children improve.**
///
/// The recurrence evaluates a `Match` action by recursing into the children and
/// summing. If every child returns its own optimum, this action's cost is the
/// best that action can achieve. That is `lemma_fold_monotone` lifted through
/// the operator node, and it is what makes per-child optimality sufficient.
pub proof fn lemma_match_monotone(best: Seq<Quality>, alt: Seq<Quality>)
    requires
        best.len() == alt.len(),
        forall|i: int| 0 <= i < best.len() ==> crate::objective::leq(#[trigger] best[i], alt[i]),
    ensures crate::objective::leq(action_cost(Action::Match(best)), action_cost(Action::Match(alt))),
{
    crate::objective::lemma_fold_monotone(best, alt);
    crate::objective::lemma_add_monotone(
        Quality { size: 1, mass: 0 },
        Quality { size: 1, mass: 0 },
        crate::objective::fold(best),
        crate::objective::fold(alt),
    );
}

/// A preselected least action satisfies the set-minimum predicate.
///
/// The two facts needed for minimality are assumptions below; this lemma
/// repackages them as `is_min`.
pub proof fn lemma_preselected_action_is_min(
    actions: Set<Action>,
    chosen: Action,
)
    requires
        actions.contains(chosen),
        forall|a: Action| #[trigger] actions.contains(a) ==> crate::objective::leq(action_cost(chosen), action_cost(a)),
    ensures
        is_min(action_cost(chosen), actions.map(|a: Action| action_cost(a))),
{
    let costs = actions.map(|a: Action| action_cost(a));
    assert(costs.contains(action_cost(chosen)));
    assert forall|q: Quality| #[trigger] costs.contains(q) implies crate::objective::leq(action_cost(chosen), q) by {
        let a = choose|a: Action| actions.contains(a) && action_cost(a) == q;
        assert(actions.contains(a));
    }
}

} // verus!
