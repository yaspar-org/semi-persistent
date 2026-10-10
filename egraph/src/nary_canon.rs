// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! The one normalization of an n-ary node's children
//! (`doc/goal-canonical-flatten-views.md`, decision 1).
//!
//! Every path that needs a canonical child list calls [`normalize`]: building a node
//! (`EGraph::add`), forming a `:flatten` view (`crate::flatten`), and the test
//! references. So every algebraic law is applied identically everywhere:
//! - coalescing (AC) or deduplication (ACI), in canonical class order (`:assoc` keeps
//!   its order);
//! - the identity drop (`:identity`);
//! - the nilpotent clamp (counts mod n);
//! - inverse-pair cancellation (`:inverse`);
//! - the degenerate arity: an empty result is the unit, and a single child of
//!   multiplicity 1 is that child's class.
//!
//! The caller supplies the operator's laws with its unit already resolved to a class,
//! and the inverse lookup: the build path from the live union-find and hash-cons, the
//! matcher from the round's snapshot. Class resolution of the children themselves is the
//! caller's too: the children arrive as classes.

use crate::multiplicity::MultiplicityLike;

/// How an n-ary operator's children are combined.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NaryKind {
    /// `:assoc` and the folds: an ordered sequence.
    Assoc,
    /// AC: a multiset, equal classes summed; `:nilpotent n` reduces counts mod `n`.
    Ac { nilpotent: Option<u8> },
    /// ACI: a set, equal classes dropped.
    Aci,
}

/// The laws [`normalize`] applies for one operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NaryLaws<G, O> {
    pub kind: NaryKind,
    /// The class of the operator's `:identity`, in the caller's class resolution.
    pub unit: Option<G>,
    /// The operator's `:inverse` (AC only).
    pub inverse: Option<O>,
}

/// What a normalized child list is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Normal<G> {
    /// The children form a node: the list holds them, canonical.
    Node,
    /// The children cancelled to nothing and the operator has an identity: the term is
    /// the unit.
    Unit,
    /// A single child of multiplicity 1: the term is that child's class.
    Single(G),
    /// The children cancelled to nothing and the operator has no identity: no term.
    Empty,
    /// A multiplicity exceeded the configured width.
    Overflow,
}

/// Normalize `kids`, classes with their multiplicities (1 except under AC), in place.
/// `inverse_class(inv, x)` is the class of the node `inv(x)` if one exists; it is read
/// only for an operator with an `:inverse`. A wrapper of [`normalize_by`] for
/// `(class, multiplicity)` pairs.
pub fn normalize<G, O, M>(
    laws: &NaryLaws<G, O>,
    kids: &mut Vec<(G, M)>,
    inverse_class: impl Fn(O, G) -> Option<G>,
) -> Normal<G>
where
    G: Copy + Ord,
    O: Clone,
    M: MultiplicityLike,
{
    normalize_by(laws, kids, |k| k.0, |k| k.1, |k, m| k.1 = m, inverse_class)
}

/// The normalization, over any child representation `T` that has a class and a
/// multiplicity: `class` and `mult` read them, `set_mult` writes a multiplicity (a
/// representation without one, a bare class under ACI, ignores it). The build path,
/// recanonization, `:flatten` views, and the test references all reach this.
pub fn normalize_by<T, G, O, M>(
    laws: &NaryLaws<G, O>,
    kids: &mut Vec<T>,
    class: impl Fn(&T) -> G,
    mult: impl Fn(&T) -> M,
    set_mult: impl Fn(&mut T, M),
    inverse_class: impl Fn(O, G) -> Option<G>,
) -> Normal<G>
where
    T: Clone,
    G: Copy + Ord,
    O: Clone,
    M: MultiplicityLike,
{
    match laws.kind {
        NaryKind::Assoc => {}
        NaryKind::Aci => {
            kids.sort_by_key(&class);
            kids.dedup_by_key(|k| class(k));
            for k in kids.iter_mut() {
                set_mult(k, M::ONE);
            }
        }
        NaryKind::Ac { .. } => {
            kids.sort_by_key(&class);
            let mut w = 0usize;
            for r in 0..kids.len() {
                if w > 0 && class(&kids[w - 1]) == class(&kids[r]) {
                    let Some(sum) = mult(&kids[w - 1]).checked_add(mult(&kids[r])) else {
                        return Normal::Overflow;
                    };
                    set_mult(&mut kids[w - 1], sum);
                } else {
                    kids[w] = kids[r].clone();
                    w += 1;
                }
            }
            kids.truncate(w);
        }
    }
    if let Some(u) = laws.unit {
        kids.retain(|k| class(k) != u);
    }
    if let NaryKind::Ac { nilpotent } = laws.kind {
        if let Some(order) = nilpotent {
            for k in kids.iter_mut() {
                let m = mult(k).rem_order(order);
                set_mult(k, m);
            }
            kids.retain(|k| mult(k) != M::ZERO);
        }
        if let Some(inv) = &laws.inverse {
            cancel_by(kids, &class, &mult, &set_mult, |x| {
                inverse_class(inv.clone(), x)
            });
        }
    }
    match kids.len() {
        0 if laws.unit.is_some() => Normal::Unit,
        0 => Normal::Empty,
        1 if mult(&kids[0]) == M::ONE => Normal::Single(class(&kids[0])),
        _ => Normal::Node,
    }
}

/// The group law `x ∘ inv(x) = e` at pair level, on a list sorted by class: for each
/// child `x` whose inverse node `inv(x)` exists (`inverse_of(x)` gives its class `y`),
/// the smaller count of `x` and `y` cancels from both. A class that is its own inverse
/// cancels in pairs. Whether anything changed. Completion's normal forms reach it too.
pub fn cancel_inverse_pairs<G, M>(
    kids: &mut Vec<(G, M)>,
    inverse_of: impl Fn(G) -> Option<G>,
) -> bool
where
    G: Copy + Ord,
    M: MultiplicityLike,
{
    cancel_by(
        kids,
        &|k: &(G, M)| k.0,
        &|k: &(G, M)| k.1,
        &|k: &mut (G, M), m| k.1 = m,
        inverse_of,
    )
}

fn cancel_by<T, G, M>(
    kids: &mut Vec<T>,
    class: &impl Fn(&T) -> G,
    mult: &impl Fn(&T) -> M,
    set_mult: &impl Fn(&mut T, M),
    inverse_of: impl Fn(G) -> Option<G>,
) -> bool
where
    G: Copy + Ord,
    M: MultiplicityLike,
{
    let zero = M::ZERO;
    let mut changed = false;
    for i in 0..kids.len() {
        let (x, xc) = (class(&kids[i]), mult(&kids[i]));
        if xc == zero {
            continue;
        }
        let Some(y) = inverse_of(x) else {
            continue;
        };
        if y == x {
            // x is its own inverse: copies cancel pairwise (x ∘ x = e here).
            if xc > M::ONE {
                set_mult(&mut kids[i], xc.rem_order(2));
                changed = true;
            }
        } else if let Ok(j) = kids.binary_search_by(|p| class(p).cmp(&y)) {
            // The probe is one-directional (inv(y)'s node may not exist), so cancel
            // eagerly on first sight; the mirrored visit then finds a zeroed side.
            let k = mult(&kids[i]).min(mult(&kids[j]));
            if k > zero {
                let (mi, mj) = (
                    mult(&kids[i]).saturating_sub(k),
                    mult(&kids[j]).saturating_sub(k),
                );
                set_mult(&mut kids[i], mi);
                set_mult(&mut kids[j], mj);
                changed = true;
            }
        }
    }
    if changed {
        kids.retain(|p| mult(p) != zero);
    }
    changed
}
