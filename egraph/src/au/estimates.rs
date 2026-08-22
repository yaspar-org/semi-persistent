// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Static per-pair estimates shared by the solvers: the exact generalize
//! quality (an upper bound used for action ordering and rollout
//! initialization) and the projection lower bound (used for pruning).
//!
//! Both read only the snapshot's per-class fixpoint sizes (`best_size`), so
//! they are constants of a class pair, independent of any search state or
//! cycle context.

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::literal::LitVal;

use super::ac_repr;
use super::egraph_api::{AuSnapshot, ClassOf};
use super::transport::{Cell, TransportProblem, solve_transport};

/// Exact quality of the terminal generalize action without interning its term.
/// MCGS initial rollout and contextual Exact's best-first ordering rank actions
/// with the same lazy-completion estimate. Root Exact uses the achieved term,
/// not this scalar helper, as each pair's initial value.
pub(crate) fn static_generalize_quality<
    Cfg: EGraphConfig,
    L: LitVal,
    const T: bool,
    const P: bool,
>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
) -> (u32, u32)
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if l == r {
        (snap.best_size(l), 0)
    } else {
        let size = snap
            .best_size(l)
            .checked_add(snap.best_size(r))
            .expect("generalize estimate exceeds u32 term-size capacity");
        (size, size)
    }
}

/// Admissible lower bound on the quality `(size, variant_mass)` of every AU
/// term for the class pair `(l, r)`, from the projection identity
/// `size(t) = size(proj_L) + size(proj_R) - #backbone`.
///
/// `l == r`: the exact terminal value `(bs(l), 0)`, because the solver
/// returns the class's best ground term. Distinct classes: every valid term
/// contains a `Variants` node (a `Variants`-free term projects to itself on
/// both sides, and distinct classes are disjoint), so
/// `size >= max(bs(l), bs(r)) + 1`; the variant-mass component is 0, the
/// trivial bound. `bs` is the least fixpoint of the extraction recurrence:
/// the true minimum over ground member terms, not an incumbent, so the bound
/// holds at every node under every context and does not assume the
/// projections are optimal representatives.
///
/// Sentinel and saturation: `best_size` reserves `u32::MAX` for a class with
/// no finite member, and `saturating_add` keeps a sentinel input at
/// `u32::MAX`. Inside the exact solver the sentinel is unreachable
/// (`validate_finite_from` rejects such roots and children), but the bound
/// stays sound if one arrives: pruning compares `bound > incumbent`, a
/// saturated bound discards the action, and a pair with no finite member
/// admits no valid term at all, so discarding it loses nothing. In the
/// finite case saturation only lowers the bound (`saturating_add <=` the
/// exact sum), which weakens pruning, never unsoundly strengthens it.
pub fn lb_pair<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
) -> (u32, u32)
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if l == r {
        (snap.best_size(l), 0)
    } else {
        let floor = snap.best_size(l).max(snap.best_size(r));
        (floor.saturating_add(1), 0)
    }
}

/// How many distinct class pairs a subproblem rooted at `(l, r)` can reach:
/// `|{l} ∪ reach(l)| * |{r} ∪ reach(r)|`.
///
/// This is the size of the rectangle every OR state below `(l, r)` lives in.
/// It over-counts, because an action pairs a left child with a right child of
/// the *same* operator, so most cells of the rectangle are never states; and it
/// under-counts states, since a state is a pair plus two cycle contexts. What
/// it does is separate shallow subproblems from deep ones at the cost of two
/// array reads, which is what the hybrid trigger needs: the popcounts are
/// precomputed per SCC with the reachability bitsets themselves.
///
/// Saturating, so a product past `u64` reads as "very hard" and the caller's
/// `estimate <= threshold` gate rejects it.
pub fn reachable_pairs<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    l: ClassOf<Cfg>,
    r: ClassOf<Cfg>,
) -> u64
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let side = |c: ClassOf<Cfg>| {
        let reach = snap.reachability();
        // A class is in its own reachable set only when it sits on a cycle;
        // add it back exactly when the bitset does not already hold it.
        reach.reach_count(c) + u64::from(!reach.is_reachable(c, c))
    };
    side(l).saturating_mul(side(r))
}

/// Admissible lower bound on the size of any term one AC/ACI representation
/// pair `(lm, rm)` can produce: the min-cost flow over `lb_pair` cell costs
/// (illegal cells `Forbidden`) plus 1 for the operator. Sound because every
/// true cell value dominates its `lb_pair` bound and the true optimal flow is
/// feasible in the bound problem. `legal(i, j)` must be the same cell mask the
/// real solve uses; the supplies are the monomials' own multiplicities, so an
/// infeasible bound problem (`None` — Hall-infeasible, or multiplicities the
/// transport solver cannot represent) means the real pair contributes no
/// candidate either. Shared by the exact solver's representation-pair
/// pre-screen and MCGS dominance pruning.
///
/// `saturating_add` keeps a `u128::MAX` total a lower bound; a saturated
/// value still strictly exceeds every `u32` comparison target, so the caller's
/// `bound > target` prune stays sound.
pub(crate) fn transport_pair_lb<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    lm: &ac_repr::Monomial<ClassOf<Cfg>>,
    rm: &ac_repr::Monomial<ClassOf<Cfg>>,
    legal: impl Fn(usize, usize) -> bool,
) -> Option<u128>
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let mut cost = vec![vec![Cell::Forbidden; rm.len()]; lm.len()];
    for (i, &(lc, _)) in lm.iter().enumerate() {
        for (j, &(rc, _)) in rm.iter().enumerate() {
            if legal(i, j) {
                let (s, v) = lb_pair(snap, lc, rc);
                cost[i][j] = Cell::Cost(s, v);
            }
        }
    }
    let problem = TransportProblem::narrowed(
        &lm.iter().map(|&(_, k)| k).collect::<Vec<_>>(),
        &rm.iter().map(|&(_, k)| k).collect::<Vec<_>>(),
        cost,
    )?;
    let solution = solve_transport(&problem)?;
    Some(solution.total.0.saturating_add(1))
}
