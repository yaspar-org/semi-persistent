// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Anti-unification over the frozen e-graph.
//!
//! Implements the core of `doc/future/anti-unification-mcgs.md`: an exact memoized
//! solver and a Monte-Carlo graph search over the AND/OR graph of class-pair
//! subproblems, sharing one search-space layer, term pool, and best-result table.
//!
//! **Milestone scope** (see `anti-unification-plan.md`, "Delivered / Deferred"):
//! UCT + round-robin only (no PUCT, priors, or uct_and/lct_and); no lazy-AC chain
//! states (the exact solver uses min-cost transportation instead; MCGS truncates
//! at `A_max` and is anytime, not complete, past that bound); plain `Vec`/`HashMap`
//! storage (no semi-persistent containers, so no whole-search mark/restore and no
//! `SearchSession`/`SearchToken`); no interpreter commands.
//!
//! One deliberate extension beyond the design doc: results are ranked by the
//! lexicographic key `(size, variant_mass)` — at equal size, the term with less
//! structure under `Variants` nodes (= more shared backbone) wins, so
//! `f(Variants(x,y))` beats `Variants(x, f(y))`. See `terms.rs` and Appendix C.1
//! of the design doc.

pub mod ac_repr;
pub mod actions;
pub mod egraph_api;
pub mod exact;
pub mod mcgs;
pub mod pretty;
pub mod results;
pub mod reward;
pub mod session;
pub mod space;
pub mod terms;
pub mod transport;

use crate::containers;

containers::define_id31! {
    /// Dense index of a live e-class inside one AU snapshot (§5.3). Minted only by
    /// the snapshot's representative-to-dense map, so a non-canonical id or an id
    /// from another snapshot cannot enter search state.
    pub struct AuClassId / StoredAuClassId, "auc";
}

containers::define_id31! {
    /// Index of a strongly connected component in the snapshot's class graph (§2.4).
    pub struct SccId / StoredSccId, "scc";
}

/// Errors surfaced while building an AU snapshot (§4.1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AuError {
    /// A class transitively needed by a root has no admissible finite member
    /// after filtering `FLAG_SUBSUMED` nodes.
    NoFiniteRepresentative(AuClassId),
    /// A multiplicity did not fit in `u32` during snapshot construction.
    MultiplicityOverflow,
}

impl core::fmt::Display for AuError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AuError::NoFiniteRepresentative(c) => {
                write!(f, "class {c:?} has no admissible finite member")
            }
            AuError::MultiplicityOverflow => write!(f, "multiplicity does not fit in u32"),
        }
    }
}

impl std::error::Error for AuError {}
