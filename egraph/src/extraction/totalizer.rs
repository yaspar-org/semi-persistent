// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Generalized Totalizer Encoding (GTE) for a weighted sum over Booleans.
//!
//! Joshi, Martins, and Manquinho, "Generalized Totalizer Encoding for
//! Pseudo-Boolean Constraints", CP 2015. The encoding builds a balanced merge
//! tree over the weighted literals. Each node carries a map from an achievable
//! partial sum `s` to a literal read as "this subtree's sum is at least `s`", so
//! the size follows the number of distinct achievable sums rather than the
//! magnitude of the weights.
//!
//! # Only the forward direction is emitted
//!
//! The classical presentation emits two families of clauses. The forward family
//! forces an output up when the inputs meet a threshold; the backward family
//! forces it down when they do not. A caller that reads an output as a fact
//! ("the sum is at least `s`") needs both. A caller that only ever *asserts the
//! negation* of an output needs the forward family alone:
//!
//! ```text
//! forward clauses entail:  weighted_sum >= t  ==>  indicator(t)
//! contrapositive:          !indicator(t)      ==>  weighted_sum < t
//! ```
//!
//! The descent in the extractor asserts `!indicator(t)` to bound the objective
//! below `t`, so the contrapositive is the property it depends on, and the
//! backward family is not emitted. Two consequences follow. An indicator may be
//! spuriously true in a model, so the attained sum must be recomputed from the
//! input literals rather than counted off the indicators. And the encoding is
//! roughly half the size of the two-sided one.
//!
//! Monotonicity clauses are emitted and are not optional: without them a model
//! could satisfy `!indicator(t)` while a higher achievable total was forced
//! true, which would report a sum below the real one.

use crate::extraction::cnf::{ClauseSink, Lit};
use std::collections::{BTreeMap, BTreeSet};

/// The indicators for a weighted sum, and the threshold each one stands for.
///
/// `indicators[i]` is true whenever the weighted sum is at least
/// `thresholds[i]`. Thresholds are the achievable partial sums in increasing
/// order, so they are generally not consecutive integers.
#[derive(Clone, Debug, Default)]
pub struct SumIndicators {
    pub indicators: Vec<Lit>,
    pub thresholds: Vec<u64>,
}

impl SumIndicators {
    /// The indicator for the least achievable threshold at or above `t`, which is
    /// the one to negate in order to assert `sum < t`.
    ///
    /// `None` when no achievable threshold reaches `t`: the sum cannot reach `t`,
    /// so the bound holds unconditionally and no assumption is needed.
    pub fn indicator_at_least(&self, t: u64) -> Option<Lit> {
        let i = self.thresholds.partition_point(|&x| x < t);
        self.indicators.get(i).copied()
    }
}

/// Encode a weighted sum, emitting clauses into `sink`.
///
/// `bound` caps the partial sums the encoding tracks, which keeps the encoding
/// small when an upper bound is known in advance (the greedy solution's cost,
/// for instance). The result constrains the sum only up to `bound`, so the
/// caller must not assert a threshold above it.
///
/// Two classes of input term are not tracked, and each is handled rather than
/// dropped:
///
/// - Weight zero cannot change the sum, so the term is discarded.
/// - Weight above `bound` cannot appear in any solution whose sum is at most
///   `bound`, so the unit clause forbidding its literal is emitted. Discarding
///   such a term instead would let a model set the literal and carry a sum above
///   `bound` that no indicator reports, which is the one error that would make
///   the descent report an unachievable cost.
///
/// Every literal in `weighted` must be `Lit::Var`. A constant carries no
/// variable for the unit clause above, and the intended caller supplies
/// indicators it allocated itself.
pub fn encode_sum<S: ClauseSink>(
    sink: &mut S,
    weighted: &[(Lit, u64)],
    bound: u64,
) -> SumIndicators {
    let mut filtered: Vec<(Lit, u64)> = Vec::with_capacity(weighted.len());
    for &(l, w) in weighted {
        debug_assert!(
            !l.is_const(),
            "objective literal must be a variable, got {l:?}"
        );
        if w == 0 {
            continue;
        }
        if w > bound {
            sink.clause(&[l.not()]);
            continue;
        }
        filtered.push((l, w));
    }
    if filtered.is_empty() || bound == 0 {
        return SumIndicators::default();
    }
    let map = encode_tree(sink, &filtered, bound);
    let mut thresholds: Vec<u64> = Vec::new();
    let mut indicators: Vec<Lit> = Vec::new();
    for (&s, &l) in map.iter() {
        if s > 0 {
            thresholds.push(s);
            indicators.push(l);
        }
    }
    SumIndicators {
        indicators,
        thresholds,
    }
}

/// Recursive construction over a balanced split of `weighted`.
///
/// The returned map sends each achievable partial sum to its indicator, and
/// always contains the entry `0 -> Lit::True`: every sum is at least zero, and
/// representing that as a constant keeps a unit clause out of the output.
fn encode_tree<S: ClauseSink>(
    sink: &mut S,
    weighted: &[(Lit, u64)],
    bound: u64,
) -> BTreeMap<u64, Lit> {
    if weighted.len() == 1 {
        let (lit, w) = weighted[0];
        let mut m = BTreeMap::new();
        m.insert(0u64, Lit::True);
        // `w <= bound` was established by the caller's filter.
        m.insert(w, lit);
        return m;
    }
    let mid = weighted.len() / 2;
    let left = encode_tree(sink, &weighted[..mid], bound);
    let right = encode_tree(sink, &weighted[mid..], bound);
    merge(sink, &left, &right, bound)
}

/// Combine two subtree encodings into one.
fn merge<S: ClauseSink>(
    sink: &mut S,
    left: &BTreeMap<u64, Lit>,
    right: &BTreeMap<u64, Lit>,
    bound: u64,
) -> BTreeMap<u64, Lit> {
    // Every sum the pair of subtrees can reach, capped at `bound`.
    let mut achievable: Vec<u64> = Vec::new();
    // A sum past u64 is past `bound` too, so `checked_add` failing is "skip".
    for &l in left.keys() {
        for &r in right.keys() {
            if let Some(total) = l.checked_add(r).filter(|&t| t <= bound) {
                achievable.push(total);
            }
        }
    }
    achievable.sort_unstable();
    achievable.dedup();

    let mut out: BTreeMap<u64, Lit> = BTreeMap::new();
    for &s in &achievable {
        if s == 0 {
            out.insert(0, Lit::True);
        } else {
            let v = sink.fresh();
            out.insert(s, Lit::pos(v));
        }
    }

    // Forward: a pair of partial sums that together reach `total` forces the
    // indicator for `total`.  (left >= l) /\ (right >= r) -> (out >= l + r)
    for (&l, &lv) in left.iter() {
        for (&r, &rv) in right.iter() {
            let Some(total) = l.checked_add(r).filter(|&t| t != 0 && t <= bound) else {
                continue;
            };
            let ov = out[&total];
            sink.clause(&[lv.not(), rv.not(), ov]);
        }
    }

    // Monotonicity: reaching a higher achievable total implies reaching every
    // lower one. Required for `!indicator(t)` to mean `sum < t`, because the
    // forward clauses fire only at exactly attained totals and the achievable
    // set is not an interval.
    for w in achievable.windows(2) {
        let (lo, hi) = (w[0], w[1]);
        if lo == 0 {
            continue;
        }
        sink.clause(&[out[&hi].not(), out[&lo]]);
    }

    out
}

/// The sum of the weights whose literal is true under `model`.
///
/// The counterpart to the specification function of the same name: the descent
/// calls this to recover the attained objective from a model, because the
/// one-sided encoding permits spuriously true indicators.
pub fn attained_sum(model: &dyn Fn(Lit) -> bool, weighted: &[(Lit, u64)]) -> u64 {
    let mut total = 0u64;
    for &(l, w) in weighted {
        if model(l) {
            // Checked: a saturated total would be reported as the attained cost and
            // silently understate it, which is the one error that makes the search
            // report a cost it cannot realize.
            total = total.checked_add(w).expect("attained sum overflows u64");
        }
    }
    total
}

// ---------------------------------------------------------------------------
// Windowed encoding
// ---------------------------------------------------------------------------

/// The largest cap the encoding accepts.
///
/// Two values from the children's sets are added when a parent's set is built, and
/// both are at most the cap, so `2 * cap` must be representable. Above this the
/// construction refuses rather than saturating: a saturated sum maps two distinct
/// totals onto one value, and two distinct totals sharing an indicator makes the
/// encoding unsound rather than merely imprecise. Every arithmetic operation on
/// values below is justified by this bound, so it is checked once at construction
/// instead of defensively at each use.
pub const MAX_CAP: u64 = u64::MAX / 2;

/// A weight the windowed totalizer sums: `u64`, whose arithmetic is exact below
/// [`MAX_CAP`], or an exact unbounded integer (`crate::extraction::Cost`), which has no cap.
/// The encoding is the same for both: values, splits, and clauses depend only on the
/// order and sums of the weights, so an instance whose weights all fit `u64` is encoded
/// identically by either.
pub trait Weight: Clone + Ord + core::fmt::Debug + core::fmt::Display {
    fn zero() -> Self;
    /// `self + o`, or `None` when the type cannot hold it.
    fn checked_add(&self, o: &Self) -> Option<Self>;
    /// `self - o` for `o <= self`.
    fn sub(&self, o: &Self) -> Self;
    /// The largest cap whose doubled values are still exact, or `None` for no cap.
    fn max_cap() -> Option<Self>;
    fn is_zero(&self) -> bool {
        *self == Self::zero()
    }
}

impl Weight for u64 {
    fn zero() -> Self {
        0
    }
    fn checked_add(&self, o: &Self) -> Option<Self> {
        u64::checked_add(*self, *o)
    }
    fn sub(&self, o: &Self) -> Self {
        *self - *o
    }
    fn max_cap() -> Option<Self> {
        Some(MAX_CAP)
    }
}

/// A generalized totalizer that defines only the output values a bound needs.
///
/// [`encode_sum`] materializes an indicator for *every* achievable partial sum at
/// every internal node. That is what an interface offering `indicator_at_least`
/// for an arbitrary threshold requires, and it is quadratic in the achievable set:
/// on a real objective of 128 terms with five distinct weights and a bound of
/// 45,930 it emitted 32,705,841 clauses, against 19,005 for a reference
/// implementation of the same encoding on the same input. The family was never the
/// problem.
///
/// To forbid `sum > ub` it is enough to deny the output values in the window
/// `(ub, ub + max_weight]`. If the true sum exceeded `ub`, then adding the true
/// terms one at a time first crosses `ub` by at most one weight, so some subset of
/// the true terms sums into the window, and that value's indicator is forced true
/// by the forward clauses. Denying the window therefore denies the sum, and the
/// values below `ub` never need an indicator at all.
///
/// Because the window is narrow and each value is defined recursively on demand,
/// nothing outside it is built. The descent tightens `ub` monotonically, so
/// successive calls to [`Self::deny_above`] add a few clauses each and keep every
/// clause already learned, which is the incremental strengthening PBLib exposes as
/// `encodeNewLeq` and rustsat as `encode_ub_change`.
pub struct WindowedSum<W: Weight = u64> {
    nodes: Vec<Node<W>>,
    terms: Vec<(Lit, W)>,
    max_weight: W,
    cap: W,
    /// The largest bound this instance was built for, which is the precondition
    /// `deny_above` is checked against.
    max_bound: W,
    shortcuts: bool,
    /// Descendant indicators already wired to a root value, so the clause is not
    /// emitted twice as the window moves down.
    wired: BTreeSet<(usize, W)>,
}

/// How the merge tree is built, which trades encoding size against propagation
/// distance rather than being strictly better one way.
///
/// Grouping by weight keeps each group's achievable set at `{w, 2w, ..., nw}` and
/// cut the worst objective from 51,470 clauses to 11,900. It also adds one to two
/// levels of depth on every objective with more than one distinct weight, because
/// each group becomes a subtree and a merge tree sits above them. Propagation must
/// then climb further to force a root indicator, measured at 13.76 milliseconds per
/// solve against 8.29 for the position split on the same corpus.
///
/// Objectives with a single distinct weight are identical under both, which is the
/// control for that measurement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TreeShape {
    /// One subtree per distinct weight, then a balanced merge. Smaller, deeper.
    WeightGrouped,
    /// Balanced split of the weight-sorted term list. Larger, shallower.
    PositionSplit,
    /// One subtree per distinct weight, merged so the heaviest group is the
    /// shallowest.
    ///
    /// Depth is only paid on the path a contribution actually travels, and the
    /// contributions that decide a window value are the heavy ones: with a bound of
    /// 45,930 and a group of 47 terms of weight 1000, that group alone spans the
    /// bound. Combining the groups in ascending weight order leaves the heaviest as
    /// a direct child of the root, so its indicators force a root value in one step
    /// instead of climbing a balanced merge tree. Light groups take the extra depth
    /// instead, where it costs less because they move the sum less.
    HeavyGroupsShallow,
}

struct Node<W> {
    /// Achievable sums of this subtree, ascending, each at most `cap`.
    values: Vec<W>,
    /// Indicators allocated so far. Absent means not yet needed.
    defined: BTreeMap<W, Lit>,
    /// Child node indices, or `None` for a leaf.
    kids: Option<(usize, usize)>,
    /// A leaf's own literal.
    leaf: Option<Lit>,
}

impl<W: Weight> WindowedSum<W> {
    /// Whether [`Self::new`] accepts `weighted` and `max_bound`: the total weight fits
    /// u64, and the bound plus the largest weight is at most [`MAX_CAP`]. `Err` names
    /// the condition that fails, so a caller reports it in place of the constructor's
    /// panic.
    pub fn fits(weighted: &[(Lit, W)], max_bound: &W) -> Result<(), String> {
        let positive = || weighted.iter().map(|(_, w)| w).filter(|w| !w.is_zero());
        positive()
            .try_fold(W::zero(), |t, w| t.checked_add(w))
            .ok_or("the total objective weight exceeds u64, the totalizer's range")?;
        let max_weight = positive().max().cloned().unwrap_or_else(W::zero);
        match (max_bound.checked_add(&max_weight), W::max_cap()) {
            (Some(_), None) => Ok(()),
            (Some(cap), Some(m)) if cap <= m => Ok(()),
            (_, m) => Err(format!(
                "the bound {max_bound} plus the largest weight {max_weight} exceeds the totalizer's cap {}",
                m.map_or_else(|| "(none)".to_string(), |m| m.to_string())
            )),
        }
    }

    /// Build the tree for `weighted`, sized for bounds no larger than `max_bound`.
    ///
    /// No clauses are emitted here. Only the achievable-value sets are computed,
    /// and they are capped at `max_bound + max_weight`, since no larger value can
    /// ever fall in a window for a bound at or below `max_bound`.
    /// The default construction, chosen by measurement over the 64-instance corpus.
    ///
    /// [`TreeShape::PositionSplit`] without residual clauses wins on total time,
    /// 2.10 seconds against 3.25 for weight grouping and 3.33 for heavy-groups-
    /// shallow, with all three proving all 64 optima and agreeing on every one.
    ///
    /// The choice is not uniform and the reason is worth recording. Grouping wins
    /// the *typical* instance, at a median factor of 1.20 and 31 of 37 instances.
    /// The total is decided by two instances of 604 terms over two distinct weights,
    /// where grouping costs 0.748 and 0.475 seconds; every other instance differs by
    /// under 40 milliseconds. Since the hard instances are the ones that matter,
    /// total time is the criterion.
    ///
    /// A per-instance selection rule was considered and rejected: the lower envelope
    /// of all three constructions is 2.018 seconds against 2.099 for the best single
    /// one, so selection could recover about 4% and would need a predictor to do it.
    ///
    /// Grouping is retained rather than deleted because it is 0.84 times the clause
    /// count, which makes it the fallback if an instance ever threatens memory.
    ///
    /// Panics where [`Self::fits`] fails: a caller with input from a program checks it
    /// first.
    pub fn new(weighted: &[(Lit, W)], max_bound: W) -> Self {
        Self::with_shape(weighted, max_bound, TreeShape::PositionSplit)
    }

    /// As [`Self::new`], with the merge tree chosen by the caller.
    pub fn with_shape(weighted: &[(Lit, W)], max_bound: W, shape: TreeShape) -> Self {
        let mut terms: Vec<(Lit, W)> = Vec::with_capacity(weighted.len());
        for (l, w) in weighted {
            debug_assert!(!l.is_const(), "objective literal must be a variable");
            if !w.is_zero() {
                terms.push((*l, w.clone()));
            }
        }
        // Group equal weights together. A subtree whose leaves all share a weight
        // `w` reaches only `{w, 2w, ..., nw}`, so its achievable set is linear in
        // its size rather than exponential, and the pairs its parent must consider
        // shrink with it. Splitting by position instead scatters the distinct
        // weights across the tree and makes every node's set dense: on the
        // objective with 128 terms over five distinct weights that difference was
        // 2,694,974 clauses against 22,203.
        // Stable, as `sort_by_key` was: equal weights keep their input order.
        terms.sort_by(|a, b| a.1.cmp(&b.1));
        let max_weight = terms
            .iter()
            .map(|(_, w)| w)
            .max()
            .cloned()
            .unwrap_or_else(W::zero);
        // Two conditions, checked in order of generality. An objective whose own
        // total is unrepresentable cannot be encoded at any bound, so it is rejected
        // first and independently of the bound asked for.
        let mut total = W::zero();
        for (_, w) in &terms {
            total = total
                .checked_add(w)
                .expect("total objective weight overflows u64");
        }
        // Then the cap. Checked rather than saturating: an overflow would produce a
        // cap smaller than the bound it is meant to cover, and every value above it
        // would be dropped while the caller still believed the bound was enforced.
        let cap = max_bound
            .checked_add(&max_weight)
            .expect("bound plus maximum weight overflows u64");
        if let Some(m) = W::max_cap() {
            assert!(
                cap <= m,
                "cap {cap} exceeds MAX_CAP {m}: value arithmetic could overflow"
            );
        }
        // No value can exceed the total, so a cap above it prunes nothing and only
        // wastes the value sets. Tightening it here is what keeps a caller's
        // sentinel bound, such as `u64::MAX / 4`, from building an enormous tree.
        let cap = cap.min(total);
        let mut me = WindowedSum {
            nodes: Vec::new(),
            terms,
            max_weight,
            cap,
            max_bound,
            shortcuts: false,
            wired: BTreeSet::new(),
        };
        if !me.terms.is_empty() {
            let terms = me.terms.clone();
            match shape {
                TreeShape::WeightGrouped => me.build_grouped(&terms),
                TreeShape::PositionSplit => me.build(&terms),
                TreeShape::HeavyGroupsShallow => me.build_heavy_shallow(&terms),
            };
        }
        me
    }

    /// One subtree per distinct weight, then a balanced merge of those subtrees.
    ///
    /// Sorting alone is not enough. A balanced split by position cuts through a
    /// weight group whenever the midpoint falls inside one, and both halves then
    /// hold a mixture whose achievable set is dense again. Respecting the group
    /// boundaries keeps each group's set at `{w, 2w, ..., nw}`, and only the merge
    /// above the groups deals in mixed sums. This is what rustsat's
    /// `GeneralizedTotalizer::extend_tree` does by building a `lit_tree` per
    /// equal-weight run and attaching each through a weighted connection.
    fn build_grouped(&mut self, terms: &[(Lit, W)]) -> usize {
        let mut roots: Vec<usize> = Vec::new();
        let mut i = 0;
        while i < terms.len() {
            let mut j = i + 1;
            while j < terms.len() && terms[j].1 == terms[i].1 {
                j += 1;
            }
            roots.push(self.build(&terms[i..j]));
            i = j;
        }
        self.merge_balanced(&roots)
    }

    /// One subtree per distinct weight, combined so the heaviest is shallowest.
    ///
    /// `terms` is sorted ascending by weight, so the group roots come out ascending
    /// too. Folding left over that order makes each successive group shallower, and
    /// the last one, the heaviest, a direct child of the root.
    fn build_heavy_shallow(&mut self, terms: &[(Lit, W)]) -> usize {
        let mut roots: Vec<usize> = Vec::new();
        let mut i = 0;
        while i < terms.len() {
            let mut j = i + 1;
            while j < terms.len() && terms[j].1 == terms[i].1 {
                j += 1;
            }
            roots.push(self.build(&terms[i..j]));
            i = j;
        }
        let mut it = roots.into_iter();
        let mut acc = it.next().expect("at least one group");
        for r in it {
            acc = self.join(acc, r);
        }
        acc
    }

    /// Combine subtree roots pairwise, balanced by count.
    fn merge_balanced(&mut self, roots: &[usize]) -> usize {
        if roots.len() == 1 {
            return roots[0];
        }
        let mid = roots.len() / 2;
        let left = self.merge_balanced(&roots[..mid]);
        let right = self.merge_balanced(&roots[mid..]);
        self.join(left, right)
    }

    /// Construct nodes bottom up within one equal-weight run.
    fn build(&mut self, terms: &[(Lit, W)]) -> usize {
        if terms.len() == 1 {
            let (l, w) = terms[0].clone();
            self.nodes.push(Node {
                values: vec![w],
                defined: BTreeMap::new(),
                kids: None,
                leaf: Some(l),
            });
            return self.nodes.len() - 1;
        }
        let mid = terms.len() / 2;
        let left = self.build(&terms[..mid]);
        let right = self.build(&terms[mid..]);
        self.join(left, right)
    }

    /// An internal node over two existing subtrees.
    fn join(&mut self, left: usize, right: usize) -> usize {
        // Every sum reachable by taking any subset of each side, capped. Zero is
        // representable by taking nothing from a side, so it joins both operands.
        let zero = W::zero();
        let mut values: Vec<W> = Vec::new();
        for l in std::iter::once(&zero).chain(self.nodes[left].values.iter()) {
            for r in std::iter::once(&zero).chain(self.nodes[right].values.iter()) {
                // `l` and `r` are at most `cap` and `2 * cap` is representable by
                // the assertion in `with_shape` (or the type has no cap), so this
                // addition cannot fail. A value above the cap is dropped by design: no
                // bound at or below `max_bound` has a window reaching it.
                let t = l.checked_add(r).expect("2 * cap is representable");
                if !t.is_zero() && t <= self.cap {
                    values.push(t);
                }
            }
        }
        values.sort_unstable();
        values.dedup();
        self.nodes.push(Node {
            values,
            defined: BTreeMap::new(),
            kids: Some((left, right)),
            leaf: None,
        });
        self.nodes.len() - 1
    }

    fn root(&self) -> Option<usize> {
        self.nodes.len().checked_sub(1)
    }

    /// Emit residual clauses linking descendant indicators straight to the root.
    ///
    /// A subset of the true terms below any node is also a subset of the true terms
    /// below the root, so `Reach(d, v)` implies `Reach(root, v)` for the same `v`.
    /// The implication is redundant, being derivable by the forward clauses level by
    /// level, and that is exactly the point: it is binary, so unit propagation
    /// reaches the root in one step instead of one step per level. Depth was
    /// measured as the cost driver, at 13.76 milliseconds per solve for a
    /// ten-level tree against 8.29 for an eight-level one.
    ///
    /// Only indicators that already exist are wired, so this costs no variables and
    /// no recursive definitions: purely additional binary clauses.
    pub fn with_shortcuts(mut self, on: bool) -> Self {
        self.shortcuts = on;
        self
    }

    /// The literals to assume false in order to forbid `sum > ub`.
    ///
    /// Emits whatever clauses the window needs that are not already present, so
    /// calling this repeatedly with decreasing `ub` is incremental.
    pub fn deny_above<S: ClauseSink>(&mut self, sink: &mut S, ub: W) -> Vec<Lit> {
        // Precondition, and the one an audit should check at every call site.
        // Values above `cap` were dropped at construction, so for a larger `ub` the
        // window could fall entirely inside the dropped region; this would return no
        // literals, which the caller reads as "the sum cannot reach that high". The
        // descent only ever lowers its bound from `max_bound`, so it holds there.
        //
        // When the cap clamped to the total weight nothing was dropped and any bound
        // is safe, which is why the test is against `max_bound` rather than against
        // `cap - max_weight`.
        // A release assert: a violation would silently drop the bound, and the check
        // is one comparison per call.
        assert!(
            ub <= self.max_bound,
            "deny_above({ub}) exceeds the bound {} this encoding was built for",
            self.max_bound
        );
        let Some(root) = self.root() else {
            return Vec::new();
        };
        // Cannot overflow: `ub <= cap - max_weight` and `cap <= MAX_CAP`.
        let hi = ub
            .checked_add(&self.max_weight)
            .expect("ub + max_weight <= cap");
        let window: Vec<W> = self.nodes[root]
            .values
            .iter()
            .filter(|&v| *v > ub && *v <= hi)
            .cloned()
            .collect();
        let mut out = Vec::with_capacity(window.len());
        for v in &window {
            out.push(self.define(sink, root, v.clone()));
        }
        if self.shortcuts {
            for (i, v) in window.iter().enumerate() {
                let target = out[i];
                // Every node that can reach this exact value on its own.
                let donors: Vec<usize> = (0..self.nodes.len())
                    .filter(|&d| {
                        d != root
                            && !self.wired.contains(&(d, v.clone()))
                            && self.nodes[d].defined.contains_key(v)
                    })
                    .collect();
                for d in donors {
                    let lit = self.nodes[d].defined[v];
                    self.wired.insert((d, v.clone()));
                    // Aliasing can make the donor literally the root's indicator.
                    if lit != target {
                        sink.clause(&[lit.not(), target]);
                    }
                }
            }
        }
        out
    }

    /// The indicator for value `v` at `node`, allocating and defining it if needed.
    ///
    /// `v` must be achievable at `node`. A leaf's indicator is its own literal, so
    /// a leaf costs nothing.
    fn define<S: ClauseSink>(&mut self, sink: &mut S, node: usize, v: W) -> Lit {
        if let Some(&l) = self.nodes[node].defined.get(&v) {
            return l;
        }
        if let Some(leaf) = self.nodes[node].leaf {
            debug_assert_eq!(self.nodes[node].values, vec![v.clone()]);
            self.nodes[node].defined.insert(v, leaf);
            return leaf;
        }
        let (left, right) = self.nodes[node]
            .kids
            .expect("an internal node has children");

        // Every way `v` splits across the two sides. A zero component means that
        // side contributes nothing and so needs no literal. Collected before any
        // recursion, both to end the borrows and because the count decides whether
        // this value needs a variable at all.
        let mut pairs: Vec<(W, W)> = Vec::new();
        for l in &self.nodes[left].values {
            if *l > v {
                break;
            }
            let r = v.sub(l);
            if r.is_zero() {
                pairs.push((l.clone(), W::zero()));
            } else if self.nodes[right].values.binary_search(&r).is_ok() {
                pairs.push((l.clone(), r));
            }
        }
        if self.nodes[right].values.binary_search(&v).is_ok() {
            pairs.push((W::zero(), v.clone()));
        }

        // One literal per distinct sum, and no more. If `v` splits exactly one way
        // and that way is one-sided, then "this subtree reaches v" and "that child
        // reaches v" are the same proposition: no subset spanning both sides can
        // sum to v, or a two-sided split would appear above. A fresh variable here
        // would be a second name for a literal that already exists, so the child's
        // is reused instead.
        //
        // Note that this is sharing *within* a node's value column. Two different
        // nodes holding the same numerical value must keep separate literals, since
        // they assert reachability of that sum in different subtrees.
        if pairs.len() == 1 {
            let (l, r) = pairs[0].clone();
            if r.is_zero() {
                let a = self.define(sink, left, l);
                self.nodes[node].defined.insert(v, a);
                return a;
            }
            if l.is_zero() {
                let b = self.define(sink, right, r);
                self.nodes[node].defined.insert(v, b);
                return b;
            }
        }

        let out = Lit::pos(sink.fresh());
        self.nodes[node].defined.insert(v, out);
        for (l, r) in pairs {
            if r.is_zero() {
                let a = self.define(sink, left, l);
                sink.clause(&[a.not(), out]);
            } else if l.is_zero() {
                let b = self.define(sink, right, r);
                sink.clause(&[b.not(), out]);
            } else {
                let a = self.define(sink, left, l);
                let b = self.define(sink, right, r);
                sink.clause(&[a.not(), b.not(), out]);
            }
        }
        out
    }

    /// Every indicator allocated so far, which the caller freezes across
    /// incremental solver calls.
    pub fn allocated(&self) -> Vec<Lit> {
        let mut out = Vec::new();
        for n in &self.nodes {
            if n.leaf.is_none() {
                out.extend(n.defined.values().copied());
            }
        }
        out
    }

    /// Depth of the tree and the largest number of splits any single value has.
    ///
    /// Both bound how far unit propagation must travel to force a root value: the
    /// depth is the number of levels a contribution climbs, and the split count is
    /// the number of clauses that can force one indicator. A construction that
    /// reduces clause count by increasing either is trading propagation strength
    /// for size, which is not always a gain.
    pub fn shape_stats(&self) -> (usize, usize, usize) {
        fn depth<W>(nodes: &[Node<W>], i: usize) -> usize {
            match nodes[i].kids {
                None => 1,
                Some((l, r)) => 1 + depth(nodes, l).max(depth(nodes, r)),
            }
        }
        let d = self.root().map(|r| depth(&self.nodes, r)).unwrap_or(0);
        let widest = self.nodes.iter().map(|n| n.values.len()).max().unwrap_or(0);
        let total_values: usize = self.nodes.iter().map(|n| n.values.len()).sum();
        (d, widest, total_values)
    }

    /// Child indices per arena slot, for checking the ordering invariant.
    ///
    /// Exposed because the invariant is load-bearing for the proof strategy rather
    /// than an implementation detail: it is the well-founded measure induction over
    /// the tree uses, and the reason `define` terminates.
    pub fn arena_children(&self) -> Vec<Option<(usize, usize)>> {
        self.nodes.iter().map(|n| n.kids).collect()
    }

    /// Terms the encoding tracks, for recovering the attained sum from a model.
    pub fn terms(&self) -> &[(Lit, W)] {
        &self.terms
    }
}
