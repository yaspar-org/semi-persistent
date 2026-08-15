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

use super::egraph_api::{AuSnapshot, ClassOf};

/// Exact quality of the terminal generalize action without interning its term.
/// The MCGS initial rollout ranks actions with it, and the exact solver's
/// best-first ordering ranks structural actions by the same lazy-completion
/// estimate.
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
/// `size(t) = size(proj_L) + size(proj_R) - #backbone` (plan item A1,
/// doc/au-solver-plan.md).
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
