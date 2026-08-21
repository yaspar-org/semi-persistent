// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Multiset algebra over canonical AC child slices.
//!
//! These are the search-and-arithmetic primitives for AC congruence completion
//! (superposition / inter-reduction). See `doc/design/ac-completion-spec.md`
//! and `doc/design/ac-congruence-completeness.md` §6–§7.
//!
//! All functions operate on the *canonical* AC child form produced by
//! [`crate::canon::MSetCanon`]: a slice `&[(G, M)]` that is
//!
//! - **sorted ascending by `G`**,
//! - **duplicate-free in `G`** (multiplicities of equal `G` already summed), and
//! - **positive** (every multiplicity is `>= 1`; zero entries never appear).
//!
//! Inputs are assumed canonical; outputs are canonical by construction. The
//! invariant is checked under `debug_assert!`. Every function is a single
//! sorted-merge walk, `O(|a| + |b|)`.
//!
//! ## Width
//!
//! The multiplicity type `M` is the caller's — in practice
//! [`EGraphConfig::M`](crate::config::EGraphConfig::M) — not a fixed `u32`, so
//! these operations neither cap nor narrow the configured width. Of the per-class
//! combinators only [`multiset_union_into`] increases a multiplicity; the rest
//! take a max, min, or clamped difference and so cannot overflow. That one, and
//! the cross-class sum in [`multiset_size`], are checked.

use crate::multiplicity::MultiplicityLike;

/// Raised where a multiset operation would exceed the caller's multiplicity
/// width. The positivity invariant above makes wrapping actively dangerous: a sum
/// that wraps to zero produces an entry the canonical form says cannot exist, and
/// the `retain`-based clamps would then silently delete the summand — turning an
/// overflow into a wrong equality rather than a failure.
const SUM_OVERFLOW: &str = "AC multiset multiplicity overflowed its configured width";

/// An AC child: a class id paired with its multiplicity in the multiset.
type Pair<G, M> = (G, M);

/// Debug-only check that a slice is in canonical AC child form.
#[inline]
fn debug_assert_canonical<G: Copy + Ord, M: MultiplicityLike>(m: &[Pair<G, M>]) {
    debug_assert!(
        m.windows(2).all(|w| w[0].0 < w[1].0),
        "AC multiset not strictly sorted / duplicate-free by class id"
    );
    debug_assert!(
        m.iter().all(|(_, mult)| *mult >= M::ONE),
        "AC multiset has a zero (or absent) multiplicity entry"
    );
}

/// Do `a` and `b` share no class id? Disjoint multisets have a trivial critical
/// pair (their rules commute), so the completion search skips them (spec §6).
pub fn multiset_disjoint<G: Copy + Ord, M: MultiplicityLike>(
    a: &[Pair<G, M>],
    b: &[Pair<G, M>],
) -> bool {
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
pub fn multiset_subset<G: Copy + Ord, M: MultiplicityLike>(
    a: &[Pair<G, M>],
    b: &[Pair<G, M>],
) -> bool {
    debug_assert_canonical(a);
    debug_assert_canonical(b);
    let mut j = 0;
    for &(ag, am) in a {
        // Advance b past classes smaller than ag; any such class is in b but not
        // required by a, which is fine. If we run out of b, a has an element b lacks.
        while j < b.len() && b[j].0 < ag {
            j += 1;
        }
        if j >= b.len() || b[j].0 != ag || b[j].1 < am {
            return false;
        }
        j += 1;
    }
    true
}

/// Multiset difference `a − b` into `out` (cleared first): per-class multiplicity
/// subtraction, clamped at zero, with zero results dropped. Classes in `b` but not
/// `a` are ignored. `out` must not alias `a` or `b`.
///
/// Destination-passing form for the completion hot loop (design §9a). Computes the
/// residual `M − A` when substituting a known sub-sum.
pub fn multiset_subtract_into<G: Copy + Ord, M: MultiplicityLike>(
    out: &mut Vec<Pair<G, M>>,
    a: &[Pair<G, M>],
    b: &[Pair<G, M>],
) {
    debug_assert_canonical(a);
    debug_assert_canonical(b);
    out.clear();
    let (mut i, mut j) = (0, 0);
    while i < a.len() {
        if j < b.len() && b[j].0 < a[i].0 {
            j += 1;
            continue;
        }
        if j < b.len() && b[j].0 == a[i].0 {
            let rem = a[i].0; // class id
            let mult = a[i].1.saturating_sub(b[j].1);
            if mult > M::ZERO {
                out.push((rem, mult));
            }
            i += 1;
            j += 1;
        } else {
            out.push(a[i]);
            i += 1;
        }
    }
}

/// Allocating wrapper over [`multiset_subtract_into`].
pub fn multiset_subtract<G: Copy + Ord, M: MultiplicityLike>(
    a: &[Pair<G, M>],
    b: &[Pair<G, M>],
) -> Vec<Pair<G, M>> {
    let mut out = Vec::with_capacity(a.len());
    multiset_subtract_into(&mut out, a, b);
    out
}

/// Multiset union (sum) `a ⊎ b` into `out` (cleared first): multiplicities of shared
/// classes add. `out` must not alias `a` or `b`.
pub fn multiset_union_into<G: Copy + Ord, M: MultiplicityLike>(
    out: &mut Vec<Pair<G, M>>,
    a: &[Pair<G, M>],
    b: &[Pair<G, M>],
) {
    debug_assert_canonical(a);
    debug_assert_canonical(b);
    out.clear();
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
                out.push((a[i].0, a[i].1.checked_add(b[j].1).expect(SUM_OVERFLOW)));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
}

/// Allocating wrapper over [`multiset_union_into`].
pub fn multiset_union<G: Copy + Ord, M: MultiplicityLike>(
    a: &[Pair<G, M>],
    b: &[Pair<G, M>],
) -> Vec<Pair<G, M>> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    multiset_union_into(&mut out, a, b);
    out
}

/// Multiset lcm (least common multiple) `(a ⊎ b) − (a ∩ b)` into `out` (cleared first):
/// per-class **maximum** multiplicity, the superposition multiset `AB` (spec §6 fix (B)),
/// the smallest multiset containing both `a` and `b`. `out` must not alias `a` or `b`.
pub fn multiset_lcm_into<G: Copy + Ord, M: MultiplicityLike>(
    out: &mut Vec<Pair<G, M>>,
    a: &[Pair<G, M>],
    b: &[Pair<G, M>],
) {
    debug_assert_canonical(a);
    debug_assert_canonical(b);
    out.clear();
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
                out.push((a[i].0, a[i].1.max(b[j].1)));
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
}

/// Allocating wrapper over [`multiset_lcm_into`].
pub fn multiset_lcm<G: Copy + Ord, M: MultiplicityLike>(
    a: &[Pair<G, M>],
    b: &[Pair<G, M>],
) -> Vec<Pair<G, M>> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    multiset_lcm_into(&mut out, a, b);
    out
}

/// Multiset intersection `a ∩ b` into `out` (cleared first): per-class **minimum**
/// multiplicity, the common part canceled by a cancelative op (Kapur §5.1's `A ∩ B`).
/// `out` must not alias `a` or `b`.
pub fn multiset_intersect_into<G: Copy + Ord, M: MultiplicityLike>(
    out: &mut Vec<Pair<G, M>>,
    a: &[Pair<G, M>],
    b: &[Pair<G, M>],
) {
    debug_assert_canonical(a);
    debug_assert_canonical(b);
    out.clear();
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => i += 1,
            std::cmp::Ordering::Greater => j += 1,
            std::cmp::Ordering::Equal => {
                out.push((a[i].0, a[i].1.min(b[j].1)));
                i += 1;
                j += 1;
            }
        }
    }
}

/// Allocating wrapper over [`multiset_intersect_into`].
pub fn multiset_intersect<G: Copy + Ord, M: MultiplicityLike>(
    a: &[Pair<G, M>],
    b: &[Pair<G, M>],
) -> Vec<Pair<G, M>> {
    let mut out = Vec::new();
    multiset_intersect_into(&mut out, a, b);
    out
}

/// Total size of a monomial: the sum of its multiplicities.
pub fn multiset_size<G: Copy, M: MultiplicityLike>(m: &[Pair<G, M>]) -> u64 {
    m.iter()
        .try_fold(0u64, |acc, (_, mult)| acc.checked_add(mult.to_u64()))
        .expect(SUM_OVERFLOW)
}

/// Degree-lexicographic order on monomials — a *total admissible* monomial order
/// (Kapur LMCS 2023 §3): compare total size first, then lexicographically over the
/// `(class id, multiplicity)` entries **from the largest class id downward**. At the
/// first non-tied position (descending) either one side holds a strictly larger id, or
/// both hold the same id with different counts and the larger count wins — both branches
/// say "the side with more of the largest differing class is greater", which is exactly
/// Kapur's degree-lex (`∃c ∈ A−B, ∀d ∈ B−A, c ≫ d`).
///
/// Admissible = subterm property (a proper super-multiset is strictly larger, since size
/// grows) + compatibility (`a ≫ b ⟹ a⊎x ≫ b⊎x`; adding `x` shifts both counts equally,
/// so the largest differing id and the sign of its count difference are unchanged). The
/// `≫`-smaller monomial is a class's normal-form representative; orienting every rule
/// "larger → smaller" is what makes AC rewriting shrink and terminate (design doc §6b, §9).
///
/// NOTE: the tie-break direction matters. Comparing the *ascending* sequences
/// (`a.iter().cmp(b.iter())`) is NOT admissible: at the smallest differing id it says
/// "more copies wins" when both sides carry the id but "absence wins" when one lacks it,
/// and those two branches disagree — `{b:2} ≫ {a,c}` yet `{a,b:2} ≺ {a:2,c}`, breaking
/// compatibility and with it the termination of [`normalize_ms_into`].
pub fn monomial_cmp<G: Copy + Ord, M: MultiplicityLike>(
    a: &[Pair<G, M>],
    b: &[Pair<G, M>],
) -> std::cmp::Ordering {
    multiset_size(a)
        .cmp(&multiset_size(b))
        .then_with(|| a.iter().rev().cmp(b.iter().rev()))
}

/// A ground AC rewrite rule `+lhs → +rhs`, both monomials, oriented `lhs ≫ rhs` by
/// [`monomial_cmp`]. `rhs` is the **minimal monomial** of `lhs`'s e-class (its
/// normal-form representative) — *not* a bare fresh class id, which would reintroduce
/// an atom every critical pair and diverge (design doc §6b).
pub struct NfRule<G, M> {
    pub lhs: Vec<Pair<G, M>>,
    pub rhs: Vec<Pair<G, M>>,
}

/// A borrowed view of a ground AC rewrite rule, the form the completion hot loop lends to
/// every normalization: the round's rule table owns each `lhs`/`rhs` once and hands out
/// `Copy` views, with no per-call deep copies. The allocating
/// [`normalize_ms`]/[`normalize_set`]/[`normalize_nilpotent`] wrappers keep accepting owned
/// [`NfRule`]s for tests and diagnostics and build the views internally.
#[derive(Clone, Copy)]
pub struct NfRuleRef<'a, G, M> {
    pub lhs: &'a [Pair<G, M>],
    pub rhs: &'a [Pair<G, M>],
}

impl<'a, G, M> From<&'a NfRule<G, M>> for NfRuleRef<'a, G, M> {
    fn from(r: &'a NfRule<G, M>) -> Self {
        Self {
            lhs: &r.lhs,
            rhs: &r.rhs,
        }
    }
}

/// A rule set as the normalizers consume it: the rules themselves, plus an optional
/// [`NfIndex`] over them.
///
/// Two shapes rather than one because the two completion call sites amortize differently.
/// The critical-pair loop normalizes thousands of reducts against one rule table already
/// hoisted outside the loop, so an index built alongside it is paid for once — use
/// [`indexed`](Self::indexed). Inter-reduction refills a *different* rule slice per target
/// (each target is normalized by all rules but its own), so there is nothing to amortize
/// over and indexing would cost more than the scan it replaces — use
/// [`linear`](Self::linear).
#[derive(Clone, Copy)]
pub struct NfRules<'r, 'i, G, M> {
    rules: &'i [NfRuleRef<'r, G, M>],
    index: Option<&'i NfIndex<G>>,
}

impl<'r, 'i, G: Copy + Ord, M: MultiplicityLike> NfRules<'r, 'i, G, M> {
    /// Scan every rule on every step. Correct for any rule set; the right choice when the
    /// set is not reused across enough normalizations to pay for an index.
    pub fn linear(rules: &'i [NfRuleRef<'r, G, M>]) -> Self {
        Self { rules, index: None }
    }

    /// Consult `index` to narrow the rules tested. `index` must have been built from
    /// exactly this `rules` slice ([`NfIndex::rebuild`] stores positions into it).
    pub fn indexed(rules: &'i [NfRuleRef<'r, G, M>], index: &'i NfIndex<G>) -> Self {
        debug_assert_eq!(
            index.n_rules,
            rules.len(),
            "NfIndex was built from a different rule slice"
        );
        Self {
            rules,
            index: Some(index),
        }
    }

    /// The lowest-indexed rule whose LHS is contained in `out`, or `None` if the monomial
    /// is irreducible. `cands` is caller-owned scratch, reused across steps.
    ///
    /// **Both paths return the same rule.** A rule applies only if its whole LHS is
    /// contained in `out`, so in particular the LHS's smallest class is present — which is
    /// exactly the key it is indexed under. The index therefore admits every applicable
    /// rule (it can only over-admit), and the candidates are visited in ascending position,
    /// so the first hit is the one the linear scan's `find` would have stopped at.
    #[inline]
    fn find_applicable(
        &self,
        out: &[Pair<G, M>],
        cands: &mut CandVec,
    ) -> Option<NfRuleRef<'r, G, M>> {
        match self.index {
            None => self
                .rules
                .iter()
                .copied()
                .find(|r| rule_applies_linear(r, out)),
            Some(ix) => {
                ix.candidates(out, cands);
                cands.iter().find_map(|&i| {
                    let r = self.rules[i as usize];
                    multiset_subset(r.lhs, out).then_some(r)
                })
            }
        }
    }
}

/// Applicability test for the unindexed path, with the orientation check the indexed path
/// performs once at [`NfIndex::rebuild`] time instead.
#[inline]
fn rule_applies_linear<G: Copy + Ord, M: MultiplicityLike>(
    r: &NfRuleRef<'_, G, M>,
    out: &[Pair<G, M>],
) -> bool {
    // Orientation is only meaningful for a rule the normalizers can apply: `monomial_cmp`
    // reports Equal for an empty pair, so the emptiness guard has to come first.
    if r.lhs.is_empty() {
        return false;
    }
    debug_assert!(monomial_cmp(r.lhs, r.rhs) == std::cmp::Ordering::Greater);
    multiset_subset(r.lhs, out)
}

/// Candidate rule positions for one index probe.
///
/// A monomial contributes one bucket per distinct class it contains. The inline
/// capacity is a tuning choice for the retained completion workloads; beyond it
/// the list spills and stays correct. Capacity changes require the Criterion
/// completion benchmark.
type CandVec = smallvec::SmallVec<[u32; 32]>;

/// Inverted index over a rule table's left-hand sides, keyed by each LHS's **smallest
/// class**.
///
/// The normalize loops otherwise scan every rule per step. Keying each rule by
/// a required LHS member avoids testing rules whose key is absent from the host
/// monomial; the retained Criterion completion workloads measure the resulting
/// candidate distribution.
///
/// Soundness needs only that the key be *some* fixed member of the LHS: containment
/// implies every LHS class is present in the host, so whichever member is chosen, a probe
/// over the host's classes reaches the rule's bucket. The minimum is picked as a
/// deterministic balance heuristic rather than for correctness. Its distributional
/// advantage, if any, is a Criterion question.
///
/// CSR layout — `keys` ascending and distinct, `order[starts[i]..starts[i + 1]]` the rule
/// positions for `keys[i]` in ascending order — so a probe is a binary search plus a slice
/// copy, and the whole index is three allocations regardless of table size.
///
/// # Position width
///
/// `starts` and `order` are `u32` and stay `u32`: they index the *rule table*, which is
/// a population unrelated to [`EGraphConfig::Index`](crate::config::EGraphConfig::Index)
/// and not governed by it. Unlike an id, a rule position is an index into a slice that
/// has been materialized — 2^32 rules is at least 137 GB of monomial storage before the
/// index is built at all — so the width is a space decision (two words per bucket
/// instead of four, over a table read on every normalize step) and not a capacity cap
/// anyone can reach. [`rebuild`](Self::rebuild) still checks it once rather than
/// trusting that, because the failure mode of the unchecked cast it replaces is
/// aliasing rule 2^32 onto rule 0 and silently rewriting with the wrong rule.
pub struct NfIndex<G> {
    /// Distinct LHS-minimum classes, ascending.
    keys: Vec<G>,
    /// `keys.len() + 1` offsets into `order`.
    starts: Vec<u32>,
    /// Rule positions grouped by key, ascending within each group.
    order: Vec<u32>,
    /// Length of the rule slice this was built from, to catch a mismatched pairing.
    n_rules: usize,
}

/// The index is generic over the class id only: it stores LHS-minimum classes and rule
/// positions, never a multiplicity, so one index type serves every configured
/// [`EGraphConfig::M`](crate::config::EGraphConfig::M). The multiplicity width appears
/// only on the methods that read rules.
impl<G: Copy + Ord> NfIndex<G> {
    /// Build an index over `rules`.
    pub fn build<M: MultiplicityLike>(rules: &[NfRuleRef<'_, G, M>]) -> Self {
        let mut ix = Self {
            keys: Vec::new(),
            starts: Vec::new(),
            order: Vec::new(),
            n_rules: 0,
        };
        ix.rebuild(rules);
        ix
    }

    /// Re-index `rules` in place, reusing the existing allocations. Rules with an empty LHS
    /// are omitted: the normalizers never apply them, so leaving them out of the index is
    /// the same filter the linear path's `!lhs.is_empty()` performs per visit.
    pub fn rebuild<M: MultiplicityLike>(&mut self, rules: &[NfRuleRef<'_, G, M>]) {
        self.keys.clear();
        self.starts.clear();
        self.order.clear();
        self.n_rules = rules.len();

        // One check covers every narrowing below. Positions are `< rules.len()` and
        // `order.len() <= rules.len()` (each applicable rule is pushed exactly once), so
        // bounding the table length bounds both the values stored in `order` and the
        // offsets stored in `starts`. Checking here rather than per-cast also means the
        // index is never half-built from truncated positions.
        u32::try_from(rules.len()).expect(
            "NfIndex holds rule positions as u32; a table of 2^32 or more rules needs a \
             wider position word",
        );

        // (LHS-minimum, position) for every applicable rule, ordered by key then position —
        // the latter is what makes each group ascending, hence the scan order-preserving.
        let mut pairs: Vec<(G, u32)> = rules
            .iter()
            .enumerate()
            .filter(|(_, r)| {
                // Empty-LHS rules are dropped before the orientation check: `monomial_cmp`
                // reports Equal for an empty pair, and the normalizers never apply them.
                if r.lhs.is_empty() {
                    return false;
                }
                debug_assert!(monomial_cmp(r.lhs, r.rhs) == std::cmp::Ordering::Greater);
                true
            })
            .map(|(i, r)| {
                // A canonical monomial is sorted by class, so element 0 is the minimum.
                debug_assert_canonical(r.lhs);
                // Exact: `i < rules.len()`, and `rules.len()` fits `u32` (checked above).
                (r.lhs[0].0, i as u32)
            })
            .collect();
        pairs.sort_unstable_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));

        self.starts.push(0);
        for (k, i) in pairs {
            if self.keys.last() != Some(&k) {
                self.keys.push(k);
                // Exact: one push per applicable rule, so `order.len() <= rules.len()`,
                // which fits `u32` (checked above). Same for the offset written below.
                self.starts.push(self.order.len() as u32);
            }
            self.order.push(i);
            *self.starts.last_mut().unwrap() = self.order.len() as u32;
        }
    }

    /// Positions of every rule that could apply to `out`, ascending. Over-admits (a
    /// candidate still needs the full containment test) but never under-admits.
    #[inline]
    fn candidates<M: MultiplicityLike>(&self, out: &[Pair<G, M>], buf: &mut CandVec) {
        buf.clear();
        for p in out {
            if let Ok(k) = self.keys.binary_search(&p.0) {
                let (s, e) = (self.starts[k] as usize, self.starts[k + 1] as usize);
                buf.extend_from_slice(&self.order[s..e]);
            }
        }
        // Each rule sits in exactly one bucket, so the gathered positions are distinct and
        // sorting is all that is needed to recover the linear scan's visit order.
        buf.sort_unstable();
    }
}

/// Release-mode backstop for the normalize loops. With every rule oriented `lhs ≫ rhs`
/// in the admissible order, each rewrite strictly lowers the host monomial, so the loop
/// terminates unconditionally; legitimate chains are short in practice but have no small
/// closed-form bound (a chain of equal-size rules can lex-descend many times), so the cap
/// must be generous enough to never truncate a real normalization. Reaching it means a
/// mis-oriented rule got in — debug builds assert instead of truncating silently.
const GUARD_MAX_REWRITES: usize = 1_000_000;

/// Normalize a monomial to a fixpoint by AC rewriting (Kapur Def. 3): while some rule
/// `+A → +B` has `A ⊆ ms`, replace `A` by `B` (`ms := (ms − A) ⊎ B`). Every rule is
/// oriented `A ≫ B` ([`monomial_cmp`]), so each step strictly lowers `ms` in the
/// degree-lex order (compatibility) and the loop terminates; the irreducible result is
/// left in `out`.
///
/// Destination-passing: `out` holds the result (seeded from `ms`), `scratch` is a
/// caller-owned ping-pong buffer; neither may alias `ms`. No per-rewrite allocation
/// (design §9a). `rules` must already be filtered to the relevant AC op, and each must
/// satisfy `monomial_cmp(lhs, rhs) == Greater` (the caller builds them that way). This is
/// the "normalize the reduct before materializing" step whose omission diverges (§6b).
pub fn normalize_ms_into<G: Copy + Ord, M: MultiplicityLike>(
    out: &mut Vec<Pair<G, M>>,
    scratch: &mut Vec<Pair<G, M>>,
    ms: &[Pair<G, M>],
    rules: NfRules<'_, '_, G, M>,
) {
    out.clear();
    out.extend_from_slice(ms);
    // Termination is a theorem, not a hope: every rule is oriented `lhs ≫ rhs` in the
    // admissible [`monomial_cmp`] order, so each step strictly lowers `out` (compatibility)
    // in a well-founded order. The guard is a release-mode backstop against a caller
    // passing a mis-oriented rule; hitting it is always a bug (debug builds assert).
    let mut cands = CandVec::new();
    let mut guard = GUARD_MAX_REWRITES;
    while let Some(rule) = rules.find_applicable(out, &mut cands) {
        #[cfg(debug_assertions)]
        let before = out.clone();
        // out := (out − lhs) ⊎ rhs, ping-ponging through `scratch`.
        multiset_subtract_into(scratch, out, rule.lhs);
        multiset_union_into(out, scratch, rule.rhs);
        #[cfg(debug_assertions)]
        debug_assert!(
            monomial_cmp(out, &before) == std::cmp::Ordering::Less,
            "rewrite step failed to lower the host monomial (order not admissible?)"
        );
        guard -= 1;
        if guard == 0 {
            debug_assert!(
                false,
                "normalize_ms_into hit the rewrite guard: a rule set \
                 oriented by monomial_cmp cannot loop, so a mis-oriented rule slipped in"
            );
            break;
        }
    }
}

/// Allocating wrapper over [`normalize_ms_into`].
pub fn normalize_ms<G: Copy + Ord, M: MultiplicityLike>(
    ms: &[Pair<G, M>],
    rules: &[NfRule<G, M>],
) -> Vec<Pair<G, M>> {
    let refs: Vec<NfRuleRef<'_, G, M>> = rules.iter().map(NfRuleRef::from).collect();
    let mut out = Vec::new();
    let mut scratch = Vec::new();
    normalize_ms_into(&mut out, &mut scratch, ms, NfRules::linear(&refs));
    out
}

/// Clamp every multiplicity to 1 in place: the idempotent (set) normal form of a monomial
/// (`x∘x = x`). A canonical multiset is already sorted+duplicate-free in `G`, so this only
/// rewrites the counts, never the class set. Applied after each monomial operation for a Set
/// (ACI) op, so its monomials stay {0,1}-valued (design "three independent axes": idempotent
/// bounds counts to {0,1}).
pub fn clamp_idempotent<G: Copy, M: MultiplicityLike>(ms: &mut [Pair<G, M>]) {
    for p in ms.iter_mut() {
        p.1 = M::ONE;
    }
}

/// Idempotent (set) normalization: like [`normalize_ms`] but every intermediate and the final
/// result is clamped to multiplicity 1, so the rewrite operates over sets. The union in a
/// rewrite step (`(ms − A) ⊎ B`) can raise a count above 1 (e.g. a summand already present in
/// both the residual and `B`); the clamp collapses it back, which is exactly the ACI
/// idempotence join. Termination still holds: each step strictly lowers the *set* in degree-lex
/// (the clamp only ever lowers counts), so the guard bound from the multiset case still applies.
pub fn normalize_set_into<G: Copy + Ord, M: MultiplicityLike>(
    out: &mut Vec<Pair<G, M>>,
    scratch: &mut Vec<Pair<G, M>>,
    ms: &[Pair<G, M>],
    rules: NfRules<'_, '_, G, M>,
) {
    out.clear();
    out.extend_from_slice(ms);
    clamp_idempotent(out);
    let mut cands = CandVec::new();
    let mut guard = GUARD_MAX_REWRITES;
    while let Some(rule) = rules.find_applicable(out, &mut cands) {
        #[cfg(debug_assertions)]
        let before = out.clone();
        // out := (out − lhs) ⊎ rhs, ping-ponging through `scratch`.
        multiset_subtract_into(scratch, out, rule.lhs);
        multiset_union_into(out, scratch, rule.rhs);
        clamp_idempotent(out);
        // Strictness survives the clamp: the multiset step is strict (admissible
        // order + lhs ≫ rhs) and the clamp only lowers counts (can(t) ≼ t).
        #[cfg(debug_assertions)]
        debug_assert!(
            monomial_cmp(out, &before) == std::cmp::Ordering::Less,
            "idempotent rewrite step failed to lower the host monomial"
        );
        guard -= 1;
        if guard == 0 {
            debug_assert!(false, "normalize_set_into hit the rewrite guard");
            break;
        }
    }
}

/// Allocating wrapper over [`normalize_set_into`].
pub fn normalize_set<G: Copy + Ord, M: MultiplicityLike>(
    ms: &[Pair<G, M>],
    rules: &[NfRule<G, M>],
) -> Vec<Pair<G, M>> {
    let refs: Vec<NfRuleRef<'_, G, M>> = rules.iter().map(NfRuleRef::from).collect();
    let mut out = Vec::new();
    let mut scratch = Vec::new();
    normalize_set_into(&mut out, &mut scratch, ms, NfRules::linear(&refs));
    out
}

/// Reduce every multiplicity modulo `order` in place and drop the summands that vanish: the
/// nilpotent normal form of a monomial (`x∘x = e` at order 2; count mod `order` in general).
/// `order ≥ 2`. A canonical multiset is sorted+coalesced in `G`, so this only rewrites counts
/// and removes zeroed entries; the surviving order is unchanged. Applied after each monomial
/// operation for a nilpotent op, so its monomials stay {0,…,order−1}-valued and an emptied
/// monomial becomes `{}` (which the caller maps to the unit). `retain` preserves order, so the
/// result stays canonical.
pub fn clamp_nilpotent<G: Copy, M: MultiplicityLike>(ms: &mut Vec<Pair<G, M>>, order: u8) {
    for p in ms.iter_mut() {
        p.1 = p.1.rem_order(order);
    }
    ms.retain(|p| p.1 != M::ZERO);
}

/// Nilpotent normalization: like [`normalize_ms`] but every intermediate and the final result is
/// reduced modulo `order` ([`clamp_nilpotent`]), so the rewrite operates over the nilpotent group
/// `(ℤ/order)`-multiset. The union in a rewrite step can raise a count to or past `order` (a
/// summand present in both the residual and `B`); the mod-`order` clamp cancels it, which is
/// exactly the symmetric-difference join at order 2. Termination: each step's underlying multiset
/// rewrite strictly lowers the monomial in degree-lex, and the clamp only ever lowers counts, so
/// the guard bound from the multiset case still applies.
pub fn normalize_nilpotent_into<G: Copy + Ord, M: MultiplicityLike>(
    out: &mut Vec<Pair<G, M>>,
    scratch: &mut Vec<Pair<G, M>>,
    ms: &[Pair<G, M>],
    rules: NfRules<'_, '_, G, M>,
    order: u8,
) {
    out.clear();
    out.extend_from_slice(ms);
    clamp_nilpotent(out, order);
    let mut cands = CandVec::new();
    let mut guard = GUARD_MAX_REWRITES;
    while let Some(rule) = rules.find_applicable(out, &mut cands) {
        #[cfg(debug_assertions)]
        let before = out.clone();
        // out := (out − lhs) ⊎ rhs, ping-ponging through `scratch`.
        multiset_subtract_into(scratch, out, rule.lhs);
        multiset_union_into(out, scratch, rule.rhs);
        clamp_nilpotent(out, order);
        // Strictness survives the clamp: the multiset step is strict (admissible
        // order + lhs ≫ rhs) and the mod-n clamp only lowers counts (can(t) ≼ t).
        #[cfg(debug_assertions)]
        debug_assert!(
            monomial_cmp(out, &before) == std::cmp::Ordering::Less,
            "nilpotent rewrite step failed to lower the host monomial"
        );
        guard -= 1;
        if guard == 0 {
            debug_assert!(false, "normalize_nilpotent_into hit the rewrite guard");
            break;
        }
    }
}

/// Allocating wrapper over [`normalize_nilpotent_into`].
pub fn normalize_nilpotent<G: Copy + Ord, M: MultiplicityLike>(
    ms: &[Pair<G, M>],
    rules: &[NfRule<G, M>],
    order: u8,
) -> Vec<Pair<G, M>> {
    let refs: Vec<NfRuleRef<'_, G, M>> = rules.iter().map(NfRuleRef::from).collect();
    let mut out = Vec::new();
    let mut scratch = Vec::new();
    normalize_nilpotent_into(&mut out, &mut scratch, ms, NfRules::linear(&refs), order);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::ENodeId;
    use crate::multiplicity::Multiplicity;

    fn id(n: u32) -> ENodeId {
        ENodeId::new(n)
    }

    /// Build a canonical multiset from (id, mult) pairs given in any order.
    fn ms(pairs: &[(u32, u32)]) -> Vec<Pair<ENodeId, Multiplicity>> {
        let mut v: Vec<Pair<ENodeId, Multiplicity>> = pairs
            .iter()
            .map(|&(g, m)| (id(g), Multiplicity(m)))
            .collect();
        v.sort_by_key(|p| p.0);
        v
    }

    #[test]
    fn disjoint_basic() {
        assert!(multiset_disjoint(
            &ms(&[(1, 1), (2, 1)]),
            &ms(&[(3, 1), (4, 1)])
        ));
        assert!(!multiset_disjoint(
            &ms(&[(1, 1), (2, 1)]),
            &ms(&[(2, 1), (5, 1)])
        ));
        // empty is disjoint from anything
        assert!(multiset_disjoint::<ENodeId, Multiplicity>(
            &[],
            &ms(&[(1, 1)])
        ));
        assert!(multiset_disjoint::<ENodeId, Multiplicity>(&[], &[]));
    }

    #[test]
    fn disjoint_ignores_multiplicity() {
        // sharing a class is non-disjoint regardless of multiplicity
        assert!(!multiset_disjoint(&ms(&[(2, 5)]), &ms(&[(2, 1)])));
    }

    #[test]
    fn subset_basic() {
        // {a,b} ⊆ {a,b,d}
        assert!(multiset_subset(
            &ms(&[(1, 1), (2, 1)]),
            &ms(&[(1, 1), (2, 1), (4, 1)])
        ));
        // {a,b,d} ⊄ {a,b}
        assert!(!multiset_subset(
            &ms(&[(1, 1), (2, 1), (4, 1)]),
            &ms(&[(1, 1), (2, 1)])
        ));
        // overlap but neither contains (the §4b case)
        assert!(!multiset_subset(
            &ms(&[(1, 1), (2, 1)]),
            &ms(&[(2, 1), (4, 1)])
        ));
        // empty ⊆ anything
        assert!(multiset_subset::<ENodeId, Multiplicity>(
            &[],
            &ms(&[(1, 1)])
        ));
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
        let empty: Vec<Pair<ENodeId, Multiplicity>> = Vec::new();
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

    #[test]
    fn into_variants_match_allocating_and_reuse_buffer() {
        let a = ms(&[(1, 1), (2, 2), (4, 1)]);
        let b = ms(&[(2, 1), (4, 1), (5, 1)]);
        // A pre-dirtied buffer must be cleared, and each _into matches its wrapper.
        let mut buf = ms(&[(99, 7)]);
        multiset_subtract_into(&mut buf, &a, &b);
        assert_eq!(buf, multiset_subtract(&a, &b));
        multiset_union_into(&mut buf, &a, &b);
        assert_eq!(buf, multiset_union(&a, &b));
        multiset_lcm_into(&mut buf, &a, &b);
        assert_eq!(buf, multiset_lcm(&a, &b));
    }

    #[test]
    fn normalize_ms_into_matches_and_reuses() {
        // Rules: {1,2}→{3} and {3,4}→{5}, so {1,2,4} → {3,4} → {5}.
        let rules = vec![
            NfRule {
                lhs: ms(&[(1, 1), (2, 1)]),
                rhs: ms(&[(3, 1)]),
            },
            NfRule {
                lhs: ms(&[(3, 1), (4, 1)]),
                rhs: ms(&[(5, 1)]),
            },
        ];
        let input = ms(&[(1, 1), (2, 1), (4, 1)]);
        let refs: Vec<NfRuleRef<'_, ENodeId, Multiplicity>> =
            rules.iter().map(NfRuleRef::from).collect();
        let mut out = ms(&[(99, 3)]); // pre-dirtied
        let mut scratch = ms(&[(88, 2)]); // pre-dirtied
        normalize_ms_into(&mut out, &mut scratch, &input, NfRules::linear(&refs));
        assert_eq!(out, ms(&[(5, 1)]));
        assert_eq!(out, normalize_ms(&input, &rules));
    }

    /// The indexed path must pick the same rule the linear scan would, not merely *a*
    /// rule that applies — the two differ whenever more than one rule is applicable, and
    /// which one fires determines the normal form reached.
    ///
    /// The rules here are ordered so position and LHS-minimum *disagree*: rule 0 keys on
    /// class 3, rule 1 on class 1. A host containing both is reducible by either, the
    /// linear scan takes rule 0, and an index that returned candidates in key order rather
    /// than position order would take rule 1.
    #[test]
    fn indexed_picks_the_same_rule_as_the_linear_scan() {
        let rules = [
            NfRule {
                lhs: ms(&[(3, 1), (4, 1)]),
                rhs: ms(&[(6, 1)]),
            },
            NfRule {
                lhs: ms(&[(1, 1), (2, 1)]),
                rhs: ms(&[(7, 1)]),
            },
        ];
        let refs: Vec<NfRuleRef<'_, ENodeId, Multiplicity>> =
            rules.iter().map(NfRuleRef::from).collect();
        let index = NfIndex::build(&refs);
        // Reducible by rule 0 and rule 1 both; the earlier rule must win either way.
        let input = ms(&[(1, 1), (2, 1), (3, 1), (4, 1)]);

        let mut lin = Vec::new();
        let mut ixd = Vec::new();
        let mut scratch = Vec::new();
        normalize_ms_into(&mut lin, &mut scratch, &input, NfRules::linear(&refs));
        normalize_ms_into(
            &mut ixd,
            &mut scratch,
            &input,
            NfRules::indexed(&refs, &index),
        );
        assert_eq!(lin, ixd, "indexed and linear normal forms diverged");
        // Rule 0 fires first ({3,4}→{6}), leaving {1,2,6}, then rule 1 ({1,2}→{7}).
        assert_eq!(lin, ms(&[(6, 1), (7, 1)]));
    }

    /// Exhaustive equivalence over a small space, for all three normalizers: every host
    /// monomial over 6 classes against a fixed rule table, indexed vs linear. This is the
    /// property the `Bclose` call site depends on, so it is checked over many shapes
    /// rather than the one hand-picked above — including hosts no rule touches (the 94-98%
    /// case the index exists to skip) and hosts reducible several steps deep.
    #[test]
    fn indexed_matches_linear_for_every_host_over_six_classes() {
        // LHS-minima deliberately repeated (two rules key on class 1) and out of position
        // order, so buckets hold multiple rules and key order ≠ position order.
        let rules = vec![
            NfRule {
                lhs: ms(&[(2, 1), (3, 1)]),
                rhs: ms(&[(1, 1)]),
            },
            NfRule {
                lhs: ms(&[(1, 1), (4, 1)]),
                rhs: ms(&[(2, 1)]),
            },
            NfRule {
                lhs: ms(&[(1, 2)]),
                rhs: ms(&[(3, 1)]),
            },
            NfRule {
                lhs: ms(&[(4, 1), (5, 1)]),
                rhs: ms(&[(1, 1)]),
            },
            NfRule {
                lhs: ms(&[(1, 1), (2, 1), (3, 1)]),
                rhs: ms(&[(5, 1)]),
            },
        ];
        // Orientation is the normalizers' precondition (lhs ≫ rhs); assert it up front so a
        // future edit to the table above fails here rather than in a debug_assert.
        for r in &rules {
            assert_eq!(
                monomial_cmp(&r.lhs, &r.rhs),
                std::cmp::Ordering::Greater,
                "test rule table is mis-oriented"
            );
        }
        let refs: Vec<NfRuleRef<'_, ENodeId, Multiplicity>> =
            rules.iter().map(NfRuleRef::from).collect();
        let index = NfIndex::build(&refs);

        // Every multiplicity vector over classes 1..=6 with counts 0..=2: 3^6 = 729 hosts.
        let mut checked = 0;
        for code in 0..3usize.pow(6) {
            let mut host: Vec<Pair<ENodeId, Multiplicity>> = Vec::new();
            let mut c = code;
            for cls in 1..=6u32 {
                let mult = (c % 3) as u32;
                c /= 3;
                if mult > 0 {
                    host.push((id(cls), Multiplicity(mult)));
                }
            }
            let (mut lin, mut ixd, mut scratch) = (Vec::new(), Vec::new(), Vec::new());

            normalize_ms_into(&mut lin, &mut scratch, &host, NfRules::linear(&refs));
            normalize_ms_into(
                &mut ixd,
                &mut scratch,
                &host,
                NfRules::indexed(&refs, &index),
            );
            assert_eq!(lin, ixd, "normalize_ms_into diverged on host {host:?}");

            normalize_set_into(&mut lin, &mut scratch, &host, NfRules::linear(&refs));
            normalize_set_into(
                &mut ixd,
                &mut scratch,
                &host,
                NfRules::indexed(&refs, &index),
            );
            assert_eq!(lin, ixd, "normalize_set_into diverged on host {host:?}");

            for order in [2u8, 3] {
                normalize_nilpotent_into(
                    &mut lin,
                    &mut scratch,
                    &host,
                    NfRules::linear(&refs),
                    order,
                );
                normalize_nilpotent_into(
                    &mut ixd,
                    &mut scratch,
                    &host,
                    NfRules::indexed(&refs, &index),
                    order,
                );
                assert_eq!(
                    lin, ixd,
                    "normalize_nilpotent_into (order {order}) diverged on host {host:?}"
                );
            }
            checked += 1;
        }
        assert_eq!(checked, 729);
    }

    /// `rebuild` must leave the index equivalent to a fresh `build`, since it exists to
    /// reuse one index's allocations across rounds.
    #[test]
    fn nf_index_rebuild_matches_fresh_build() {
        let first = [NfRule {
            lhs: ms(&[(5, 1), (6, 1)]),
            rhs: ms(&[(2, 1)]),
        }];
        let second = [
            NfRule {
                lhs: ms(&[(1, 1), (9, 1)]),
                rhs: ms(&[(4, 1)]),
            },
            NfRule {
                lhs: ms(&[(1, 3)]),
                rhs: ms(&[(2, 1)]),
            },
        ];
        let r1: Vec<NfRuleRef<'_, ENodeId, Multiplicity>> =
            first.iter().map(NfRuleRef::from).collect();
        let r2: Vec<NfRuleRef<'_, ENodeId, Multiplicity>> =
            second.iter().map(NfRuleRef::from).collect();

        let mut reused = NfIndex::build(&r1);
        reused.rebuild(&r2);
        let fresh = NfIndex::build(&r2);
        assert_eq!(reused.keys, fresh.keys);
        assert_eq!(reused.starts, fresh.starts);
        assert_eq!(reused.order, fresh.order);
        assert_eq!(reused.n_rules, fresh.n_rules);
    }

    /// An empty-LHS rule is skipped by the linear path's `!lhs.is_empty()` guard and
    /// omitted from the index; both must still agree, and the omission must not renumber
    /// the rules around it.
    #[test]
    fn empty_lhs_rule_is_skipped_by_both_paths() {
        let rules = [
            NfRule {
                lhs: Vec::new(),
                rhs: Vec::new(),
            },
            NfRule {
                lhs: ms(&[(1, 1), (2, 1)]),
                rhs: ms(&[(3, 1)]),
            },
        ];
        let refs: Vec<NfRuleRef<'_, ENodeId, Multiplicity>> =
            rules.iter().map(NfRuleRef::from).collect();
        let index = NfIndex::build(&refs);
        // Rule 1 is at position 1 in `order`, not renumbered to 0 by the omission.
        assert_eq!(index.order, vec![1]);

        let input = ms(&[(1, 1), (2, 1)]);
        let (mut lin, mut ixd, mut scratch) = (Vec::new(), Vec::new(), Vec::new());
        normalize_ms_into(&mut lin, &mut scratch, &input, NfRules::linear(&refs));
        normalize_ms_into(
            &mut ixd,
            &mut scratch,
            &input,
            NfRules::indexed(&refs, &index),
        );
        assert_eq!(lin, ms(&[(3, 1)]));
        assert_eq!(lin, ixd);
    }

    #[test]
    fn clamp_nilpotent_reduces_mod_order_and_drops_zeros() {
        // Order 2: counts mod 2, zeros dropped. {a:2, b:3, c:4} → {b:1}.
        let mut m = ms(&[(1, 2), (2, 3), (3, 4)]);
        clamp_nilpotent(&mut m, 2);
        assert_eq!(m, ms(&[(2, 1)]));
        // Order 3: {a:3, b:4, c:5} → {b:1, c:2}.
        let mut m3 = ms(&[(1, 3), (2, 4), (3, 5)]);
        clamp_nilpotent(&mut m3, 3);
        assert_eq!(m3, ms(&[(2, 1), (3, 2)]));
        // A fully-even monomial empties.
        let mut even = ms(&[(1, 2), (2, 4)]);
        clamp_nilpotent(&mut even, 2);
        assert!(even.is_empty());
    }

    #[test]
    fn normalize_nilpotent_symmetric_difference_join() {
        // Rule {a,b}→{} (i.e. a⊕b = e). Normalizing {a,b,c} cancels the pair, leaving {c};
        // the mod-2 clamp is what makes the union in a rewrite step cancel. Also check a step
        // that raises a count to 2 then cancels: input {a,a,c} clamps to {c} up front.
        let rules = vec![NfRule {
            lhs: ms(&[(1, 1), (2, 1)]),
            rhs: vec![], // → the unit (empty monomial)
        }];
        assert_eq!(
            normalize_nilpotent(&ms(&[(1, 1), (2, 1), (3, 1)]), &rules, 2),
            ms(&[(3, 1)])
        );
        // {a,a} → {} regardless of rules (build gives {a:2}; clamp cancels).
        assert!(normalize_nilpotent(&ms(&[(1, 2)]), &[], 2).is_empty());
        // _into matches the wrapper and clears a dirty buffer.
        let input = ms(&[(1, 1), (2, 1), (3, 1)]);
        let refs: Vec<NfRuleRef<'_, ENodeId, Multiplicity>> =
            rules.iter().map(NfRuleRef::from).collect();
        let mut out = ms(&[(99, 3)]);
        let mut scratch = ms(&[(88, 2)]);
        normalize_nilpotent_into(&mut out, &mut scratch, &input, NfRules::linear(&refs), 2);
        assert_eq!(out, normalize_nilpotent(&input, &rules, 2));
    }

    // ── Admissibility of monomial_cmp (Kapur LMCS 2023 §3) ──────────────────────
    // These guard the W1 conformance fix: the tie-break must compare from the largest
    // class id downward. The ascending tie-break it replaced violated compatibility.

    fn lcg(rng: &mut u64, m: u32) -> u32 {
        *rng = rng
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((*rng >> 33) as u32) % m
    }

    /// Random canonical monomial over ids 1..=6 with counts 0..=3.
    fn rand_ms(rng: &mut u64) -> Vec<Pair<ENodeId, Multiplicity>> {
        let mut v = Vec::new();
        for g in 1..=6u32 {
            let c = lcg(rng, 4);
            if c > 0 {
                v.push((id(g), Multiplicity(c)));
            }
        }
        v
    }

    #[test]
    fn monomial_cmp_kapur_deglex_counterexample() {
        // The exact pair the old ascending tie-break got wrong (ids a=1 < b=2 < c=3).
        // Sizes tie at 2; the largest differing id is c, owned by {a,c}: {a,c} ≫ {b:2}.
        let bb = ms(&[(2, 2)]);
        let ac = ms(&[(1, 1), (3, 1)]);
        assert_eq!(monomial_cmp(&ac, &bb), std::cmp::Ordering::Greater);
        // Compatibility on the pair that used to flip after ⊎{a}.
        let ac_a = multiset_union(&ac, &ms(&[(1, 1)])); // {a:2, c}
        let bb_a = multiset_union(&bb, &ms(&[(1, 1)])); // {a, b:2}
        assert_eq!(monomial_cmp(&ac_a, &bb_a), std::cmp::Ordering::Greater);
    }

    #[test]
    fn monomial_cmp_compatibility_randomized() {
        // Admissibility axiom: a ≫ b ⟹ a⊎x ≫ b⊎x (and Equal only for identical multisets).
        let mut rng: u64 = 42;
        let mut checked = 0usize;
        for _ in 0..2000 {
            let a = rand_ms(&mut rng);
            let b = rand_ms(&mut rng);
            let x = rand_ms(&mut rng);
            let ord = monomial_cmp(&a, &b);
            if ord == std::cmp::Ordering::Equal {
                assert_eq!(a, b, "Equal must mean identical multisets");
                continue;
            }
            assert_eq!(
                monomial_cmp(&multiset_union(&a, &x), &multiset_union(&b, &x)),
                ord,
                "compatibility violated: a={a:?} b={b:?} x={x:?}"
            );
            checked += 1;
        }
        assert!(checked > 1000);
    }

    #[test]
    fn monomial_cmp_subterm_property_randomized() {
        // A proper super-multiset is strictly greater (degree component).
        let mut rng: u64 = 7;
        for _ in 0..1000 {
            let b = rand_ms(&mut rng);
            let mut ext = rand_ms(&mut rng);
            if ext.is_empty() {
                ext = ms(&[(1, 1)]);
            }
            let a = multiset_union(&b, &ext);
            assert_eq!(monomial_cmp(&a, &b), std::cmp::Ordering::Greater);
        }
    }

    #[test]
    fn former_cycle_rules_terminate_at_irreducible_normal_form() {
        // Under the old tie-break, {b:2}→{a,c} and {a:2,c}→{a,b:2} both passed the
        // Greater orientation guard and normalize_ms two-cycled on {a,b:2} until the
        // defensive guard, returning a REDUCIBLE monomial. Under Kapur deg-lex the first
        // orients the other way; with both correctly oriented, normalization terminates
        // at an irreducible normal form from every start point.
        let r1 = NfRule {
            lhs: ms(&[(1, 1), (3, 1)]),
            rhs: ms(&[(2, 2)]),
        }; // {a,c} → {b:2}
        let r2 = NfRule {
            lhs: ms(&[(1, 2), (3, 1)]),
            rhs: ms(&[(1, 1), (2, 2)]),
        }; // {a:2,c} → {a,b:2}
        assert_eq!(monomial_cmp(&r1.lhs, &r1.rhs), std::cmp::Ordering::Greater);
        assert_eq!(monomial_cmp(&r2.lhs, &r2.rhs), std::cmp::Ordering::Greater);
        let rules = [r1, r2];
        for host in [
            ms(&[(1, 1), (2, 2)]),
            ms(&[(1, 2), (3, 1)]),
            ms(&[(1, 2), (3, 2)]),
        ] {
            let out = normalize_ms(&host, &rules);
            for r in &rules {
                assert!(
                    !multiset_subset(&r.lhs, &out),
                    "normalize_ms({host:?}) returned a reducible result {out:?}"
                );
            }
        }
    }
}
