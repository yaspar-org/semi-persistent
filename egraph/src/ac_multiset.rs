// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Multiset algebra over canonical AC child slices.
//!
//! These are the search-and-arithmetic primitives for AC congruence completion
//! (superposition / inter-reduction). See `doc/future/ac-congruence-completeness-plan.md`
//! and `doc/design/ac-congruence-completeness.md` §6–§7.
//!
//! All functions operate on the *canonical* AC child form produced by
//! [`crate::canon::ACCanon`]: a slice `&[(G, Multiplicity)]` that is
//!
//! - **sorted ascending by `G`**,
//! - **duplicate-free in `G`** (multiplicities of equal `G` already summed), and
//! - **positive** (every multiplicity is `>= 1`; zero entries never appear).
//!
//! Inputs are assumed canonical; outputs are canonical by construction. The
//! invariant is checked under `debug_assert!`. Every function is a single
//! sorted-merge walk, `O(|a| + |b|)`.

use crate::multiplicity::Multiplicity;

/// An AC child: a class id paired with its multiplicity in the multiset.
type Pair<G> = (G, Multiplicity);

/// Debug-only check that a slice is in canonical AC child form.
#[inline]
fn debug_assert_canonical<G: Copy + Ord>(m: &[Pair<G>]) {
    debug_assert!(
        m.windows(2).all(|w| w[0].0 < w[1].0),
        "AC multiset not strictly sorted / duplicate-free by class id"
    );
    debug_assert!(
        m.iter().all(|(_, mult)| mult.0 >= 1),
        "AC multiset has a zero (or absent) multiplicity entry"
    );
}

/// Do `a` and `b` share no class id? Disjoint multisets have a trivial critical
/// pair (their rules commute), so the completion search skips them (spec §6).
pub fn multiset_disjoint<G: Copy + Ord>(a: &[Pair<G>], b: &[Pair<G>]) -> bool {
    debug_assert_canonical(a);
    debug_assert_canonical(b);
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Equal => return false,
        }
    }
    true
}

/// Is `a` a sub-multiset of `b` (`a ⊆ b`)? True iff every class in `a` occurs in
/// `b` with at least the same multiplicity. This is the (A) inter-reduction test:
/// the sub-sum `+a` is virtually contained in `+b`.
pub fn multiset_subset<G: Copy + Ord>(a: &[Pair<G>], b: &[Pair<G>]) -> bool {
    debug_assert_canonical(a);
    debug_assert_canonical(b);
    let mut j = 0;
    for &(ag, am) in a {
        // Advance b past classes smaller than ag; any such class is in b but not
        // required by a, which is fine. If we run out of b, a has an element b lacks.
        while j < b.len() && b[j].0 < ag {
            j += 1;
        }
        if j >= b.len() || b[j].0 != ag || b[j].1.0 < am.0 {
            return false;
        }
        j += 1;
    }
    true
}

/// Multiset difference `a − b`: per-class multiplicity subtraction, clamped at
/// zero, with zero results dropped. Classes in `b` but not `a` are ignored.
///
/// Used to compute the residual `M − A` when substituting a known sub-sum.
pub fn multiset_subtract<G: Copy + Ord>(a: &[Pair<G>], b: &[Pair<G>]) -> Vec<Pair<G>> {
    debug_assert_canonical(a);
    debug_assert_canonical(b);
    let mut out = Vec::with_capacity(a.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() {
        if j < b.len() && b[j].0 < a[i].0 {
            j += 1;
            continue;
        }
        if j < b.len() && b[j].0 == a[i].0 {
            let rem = a[i].0; // class id
            let mult = a[i].1.0.saturating_sub(b[j].1.0);
            if mult > 0 {
                out.push((rem, Multiplicity(mult)));
            }
            i += 1;
            j += 1;
        } else {
            out.push(a[i]);
            i += 1;
        }
    }
    out
}

/// Multiset union (sum) `a ⊎ b`: multiplicities of shared classes add.
pub fn multiset_union<G: Copy + Ord>(a: &[Pair<G>], b: &[Pair<G>]) -> Vec<Pair<G>> {
    debug_assert_canonical(a);
    debug_assert_canonical(b);
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                out.push((a[i].0, Multiplicity(a[i].1.0 + b[j].1.0)));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// Multiset lcm (least common multiple) `(a ⊎ b) − (a ∩ b)`: per-class **maximum**
/// multiplicity. This is the superposition multiset `AB` (spec §6 fix (B)) — the
/// smallest multiset containing both `a` and `b`.
pub fn multiset_lcm<G: Copy + Ord>(a: &[Pair<G>], b: &[Pair<G>]) -> Vec<Pair<G>> {
    debug_assert_canonical(a);
    debug_assert_canonical(b);
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => {
                out.push(a[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                out.push((a[i].0, Multiplicity(a[i].1.0.max(b[j].1.0))));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// Total size of a monomial: the sum of its multiplicities.
pub fn multiset_size<G: Copy>(m: &[Pair<G>]) -> u64 {
    m.iter().map(|(_, mult)| mult.0 as u64).sum()
}

/// Degree-lexicographic order on monomials — a *total admissible* monomial order
/// (Kapur §3.1): compare total size first, then lexicographically by the sorted
/// `(class id, multiplicity)` sequence. Admissible = subterm property (a proper
/// super-multiset is strictly larger, since size grows) + compatibility (`a ≫ b ⟹
/// a⊎x ≫ b⊎x`). The `≫`-smaller monomial is a class's normal-form representative;
/// orienting every rule "larger → smaller" is what makes AC rewriting shrink and
/// terminate (design doc §6b, §9).
pub fn monomial_cmp<G: Copy + Ord>(a: &[Pair<G>], b: &[Pair<G>]) -> std::cmp::Ordering {
    multiset_size(a)
        .cmp(&multiset_size(b))
        .then_with(|| a.iter().cmp(b.iter()))
}

/// A ground AC rewrite rule `+lhs → +rhs`, both monomials, oriented `lhs ≫ rhs` by
/// [`monomial_cmp`]. `rhs` is the **minimal monomial** of `lhs`'s e-class (its
/// normal-form representative) — *not* a bare fresh class id, which would reintroduce
/// an atom every critical pair and diverge (design doc §6b).
pub struct NfRule<G> {
    pub lhs: Vec<Pair<G>>,
    pub rhs: Vec<Pair<G>>,
}

/// Normalize a monomial to a fixpoint by AC rewriting (Kapur Def. 3): while some rule
/// `+A → +B` has `A ⊆ ms`, replace `A` by `B` (`ms := (ms − A) ⊎ B`). Every rule is
/// oriented `A ≫ B` ([`monomial_cmp`]), so each step strictly lowers `ms` in the
/// degree-lex order (compatibility) and the loop terminates; the result is irreducible.
///
/// `rules` must already be filtered to the relevant AC op, and each must satisfy
/// `monomial_cmp(lhs, rhs) == Greater` (the caller builds them that way). This is the
/// "normalize the reduct before materializing" step whose omission diverges (§6b).
pub fn normalize_ms<G: Copy + Ord>(ms: &[Pair<G>], rules: &[NfRule<G>]) -> Vec<Pair<G>> {
    let mut cur = ms.to_vec();
    // Defensive iteration cap: each rewrite strictly lowers cur in the well-founded
    // degree-lex order, but guard against a mis-oriented rule slipping in.
    let mut guard = 4 * (multiset_size(&cur) as usize + 1);
    'outer: loop {
        for rule in rules {
            debug_assert!(monomial_cmp(&rule.lhs, &rule.rhs) == std::cmp::Ordering::Greater);
            if !rule.lhs.is_empty() && multiset_subset(&rule.lhs, &cur) {
                cur = multiset_union(&multiset_subtract(&cur, &rule.lhs), &rule.rhs);
                guard = guard.saturating_sub(1);
                if guard == 0 {
                    break 'outer;
                }
                continue 'outer;
            }
        }
        break;
    }
    cur
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::ENodeId;

    fn id(n: u32) -> ENodeId {
        ENodeId::new(n)
    }

    /// Build a canonical multiset from (id, mult) pairs given in any order.
    fn ms(pairs: &[(u32, u32)]) -> Vec<Pair<ENodeId>> {
        let mut v: Vec<Pair<ENodeId>> =
            pairs.iter().map(|&(g, m)| (id(g), Multiplicity(m))).collect();
        v.sort_by_key(|p| p.0);
        v
    }

    #[test]
    fn disjoint_basic() {
        assert!(multiset_disjoint(&ms(&[(1, 1), (2, 1)]), &ms(&[(3, 1), (4, 1)])));
        assert!(!multiset_disjoint(&ms(&[(1, 1), (2, 1)]), &ms(&[(2, 1), (5, 1)])));
        // empty is disjoint from anything
        assert!(multiset_disjoint::<ENodeId>(&[], &ms(&[(1, 1)])));
        assert!(multiset_disjoint::<ENodeId>(&[], &[]));
    }

    #[test]
    fn disjoint_ignores_multiplicity() {
        // sharing a class is non-disjoint regardless of multiplicity
        assert!(!multiset_disjoint(&ms(&[(2, 5)]), &ms(&[(2, 1)])));
    }

    #[test]
    fn subset_basic() {
        // {a,b} ⊆ {a,b,d}
        assert!(multiset_subset(&ms(&[(1, 1), (2, 1)]), &ms(&[(1, 1), (2, 1), (4, 1)])));
        // {a,b,d} ⊄ {a,b}
        assert!(!multiset_subset(&ms(&[(1, 1), (2, 1), (4, 1)]), &ms(&[(1, 1), (2, 1)])));
        // overlap but neither contains (the §4b case)
        assert!(!multiset_subset(&ms(&[(1, 1), (2, 1)]), &ms(&[(2, 1), (4, 1)])));
        // empty ⊆ anything
        assert!(multiset_subset::<ENodeId>(&[], &ms(&[(1, 1)])));
    }

    #[test]
    fn subset_respects_multiplicity() {
        // {a:2} ⊆ {a:3} but not {a:3} ⊆ {a:2}
        assert!(multiset_subset(&ms(&[(1, 2)]), &ms(&[(1, 3)])));
        assert!(!multiset_subset(&ms(&[(1, 3)]), &ms(&[(1, 2)])));
        // equal multiplicity is a subset
        assert!(multiset_subset(&ms(&[(1, 2)]), &ms(&[(1, 2)])));
    }

    #[test]
    fn subtract_basic() {
        // {a,b,d} − {a,b} = {d}
        assert_eq!(
            multiset_subtract(&ms(&[(1, 1), (2, 1), (4, 1)]), &ms(&[(1, 1), (2, 1)])),
            ms(&[(4, 1)])
        );
        // subtracting a class not present is a no-op on it
        assert_eq!(
            multiset_subtract(&ms(&[(1, 1)]), &ms(&[(9, 1)])),
            ms(&[(1, 1)])
        );
    }

    #[test]
    fn subtract_multiplicity_clamps_and_drops_zeros() {
        // {a:3, b:1} − {a:1} = {a:2, b:1}
        assert_eq!(
            multiset_subtract(&ms(&[(1, 3), (2, 1)]), &ms(&[(1, 1)])),
            ms(&[(1, 2), (2, 1)])
        );
        // exact cancel drops the class entirely
        assert_eq!(
            multiset_subtract(&ms(&[(1, 2), (2, 1)]), &ms(&[(1, 2)])),
            ms(&[(2, 1)])
        );
        // over-subtract clamps at zero, does not go negative
        let empty: Vec<Pair<ENodeId>> = Vec::new();
        assert_eq!(multiset_subtract(&ms(&[(1, 1)]), &ms(&[(1, 5)])), empty);
    }

    #[test]
    fn union_sums_multiplicities() {
        // {a,b} ⊎ {b,d} = {a, b:2, d}
        assert_eq!(
            multiset_union(&ms(&[(1, 1), (2, 1)]), &ms(&[(2, 1), (4, 1)])),
            ms(&[(1, 1), (2, 2), (4, 1)])
        );
        // union with singleton {c} adds c (the ⊎ {a} substitution step)
        assert_eq!(
            multiset_union(&ms(&[(4, 1)]), &ms(&[(3, 1)])),
            ms(&[(3, 1), (4, 1)])
        );
        // union with a singleton already present bumps its multiplicity
        assert_eq!(
            multiset_union(&ms(&[(3, 1), (4, 1)]), &ms(&[(3, 1)])),
            ms(&[(3, 2), (4, 1)])
        );
    }

    #[test]
    fn lcm_takes_max_multiplicity() {
        // lcm({a,b}, {b,d}) = {a,b,d}  (the §4b superposition)
        assert_eq!(
            multiset_lcm(&ms(&[(1, 1), (2, 1)]), &ms(&[(2, 1), (4, 1)])),
            ms(&[(1, 1), (2, 1), (4, 1)])
        );
        // per-element max, not sum: lcm({a:3}, {a:1}) = {a:3}
        assert_eq!(multiset_lcm(&ms(&[(1, 3)]), &ms(&[(1, 1)])), ms(&[(1, 3)]));
        // disjoint lcm is the union
        assert_eq!(
            multiset_lcm(&ms(&[(1, 2)]), &ms(&[(5, 1)])),
            ms(&[(1, 2), (5, 1)])
        );
    }

    #[test]
    fn lcm_contains_both_operands() {
        // a ⊆ lcm(a,b) and b ⊆ lcm(a,b), by construction (per-element max)
        let a = ms(&[(1, 2), (2, 1)]);
        let b = ms(&[(2, 3), (4, 1)]);
        let ab = multiset_lcm(&a, &b);
        assert!(multiset_subset(&a, &ab));
        assert!(multiset_subset(&b, &ab));
    }

    #[test]
    fn subtract_then_union_round_trips_lcm() {
        // (AB − A) ⊎ A == AB when A ⊆ AB — the substitution arithmetic identity.
        let a = ms(&[(1, 1), (2, 2)]);
        let b = ms(&[(2, 1), (4, 1)]);
        let ab = multiset_lcm(&a, &b);
        let residual = multiset_subtract(&ab, &a);
        assert_eq!(multiset_union(&residual, &a), ab);
    }
}
