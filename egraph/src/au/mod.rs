// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Anti-unification over the frozen e-graph.
//!
//! Implements `doc/design/19-anti-unification.md`: an exact memoized
//! solver and a Monte-Carlo graph search over the AND/OR graph of class-pair
//! subproblems, sharing one search-space layer, term pool, and best-result table.
//!
//! Both algorithms handle AC/ACI operators through min-cost transportation
//! (`transport.rs`, `ac_repr.rs`): the exact solver solves each cell subproblem
//! once and finds the optimal matching by flow; MCGS uses one transport-AND-node
//! per feasible representation pair, with all legal cells as bandit arms and the
//! flow recomputed from cell Q estimates on every backpropagation. Neither path
//! enumerates matching matrices.
//!
//! Search state is semi-persistent (`SearchSession`/`SearchToken` in
//! `session.rs`): the space, term pool, best-result table, action cache, and
//! MCGS statistics all mark/restore together through bundled underlying container
//! tokens. MCGS reports a structural completion certificate (`Completion::Exact` after a children-first closure
//! pass, or `BudgetExhausted`). Interpreter commands `(antiunify)` and
//! `(checkau)` expose the system from .egg programs.
//!
//! The implemented policies are UCT OR-selection and three AND-node effort
//! selectors — `lct_and` (default), `uct_and`, and `round_robin` (§3.3.5)
//! (alternatives such as PUCT and priors are future work; see
//! `doc/future/au-associative-operators.md`). AU id widths follow
//! `EGraphConfig::Au`: every container instantiates its id family from
//! the configuration (`AuIds31` for DefaultConfig, `AuIds64` for Config64).
//!
//! Results are ranked by the lexicographic key `(size, variant_mass)` — at equal
//! size, the term with less structure under `Variants` nodes (= more shared
//! backbone) wins, so `f(Variants(x,y))` beats `Variants(x, f(y))`. See `terms.rs`
//! and Appendix C.1 of the design chapter.

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

// --- 31-bit AU id family (DefaultConfig) ---

containers::define_id31! { pub struct SnapshotMemberId / StoredSnapshotMemberId, "sm"; }
containers::define_id31! { pub struct ContextElemId / StoredContextElemId, "ce"; }
containers::define_id31! { pub struct TermChildId / StoredTermChildId, "tc"; }
containers::define_id31! { pub struct ReachBlockId / StoredReachBlockId, "rb"; }
containers::define_id31! { pub struct OrStatsId / StoredOrStatsId, "os"; }
containers::define_id31! { pub struct AndStatsId / StoredAndStatsId, "as"; }
containers::define_id31! { pub struct OrEdgeStatId / StoredOrEdgeStatId, "oes"; }
containers::define_id31! { pub struct AndChildStatId / StoredAndChildStatId, "acs"; }

/// The 31-bit AU id family. Used by `DefaultConfig`.
pub struct AuIds31;
impl crate::config::AuIds for AuIds31 {
    type Index = u32;
    type Class = AuClassId;
    type Scc = SccId;
    type Or = space::OrId;
    type Action = space::ActionId;
    type Context = space::CtxId;
    type Term = terms::TermId;
    type OrStats = OrStatsId;
    type AndStats = AndStatsId;
    type OrEdgeStat = OrEdgeStatId;
    type AndChildStat = AndChildStatId;
    type SnapshotMember = SnapshotMemberId;
    type ContextElem = ContextElemId;
    type TermChild = TermChildId;
    type ReachBlock = ReachBlockId;
}

// --- 63-bit AU id family (Config64) ---

containers::define_id63! { pub struct AuClassId64 / StoredAuClassId64, "auc64"; }
containers::define_id63! { pub struct SccId64 / StoredSccId64, "scc64"; }
containers::define_id63! { pub struct OrId64 / StoredOrId64, "or64"; }
containers::define_id63! { pub struct ActionId64 / StoredActionId64, "act64"; }
containers::define_id63! { pub struct CtxId64 / StoredCtxId64, "ctx64"; }
containers::define_id63! { pub struct TermId64 / StoredTermId64, "t64"; }
containers::define_id63! { pub struct OrStatsId64 / StoredOrStatsId64, "os64"; }
containers::define_id63! { pub struct AndStatsId64 / StoredAndStatsId64, "as64"; }
containers::define_id63! { pub struct OrEdgeStatId64 / StoredOrEdgeStatId64, "oes64"; }
containers::define_id63! { pub struct AndChildStatId64 / StoredAndChildStatId64, "acs64"; }
containers::define_id63! { pub struct SnapshotMemberId64 / StoredSnapshotMemberId64, "sm64"; }
containers::define_id63! { pub struct ContextElemId64 / StoredContextElemId64, "ce64"; }
containers::define_id63! { pub struct TermChildId64 / StoredTermChildId64, "tc64"; }
containers::define_id63! { pub struct ReachBlockId64 / StoredReachBlockId64, "rb64"; }

/// The 63-bit AU id family. Used by `Config64`.
pub struct AuIds64;
impl crate::config::AuIds for AuIds64 {
    type Index = u64;
    type Class = AuClassId64;
    type Scc = SccId64;
    type Or = OrId64;
    type Action = ActionId64;
    type Context = CtxId64;
    type Term = TermId64;
    type OrStats = OrStatsId64;
    type AndStats = AndStatsId64;
    type OrEdgeStat = OrEdgeStatId64;
    type AndChildStat = AndChildStatId64;
    type SnapshotMember = SnapshotMemberId64;
    type ContextElem = ContextElemId64;
    type TermChild = TermChildId64;
    type ReachBlock = ReachBlockId64;
}

// ---------------------------------------------------------------------------
// Config-projected type aliases (readability in Cfg-generic signatures)
// ---------------------------------------------------------------------------

/// The AU class id selected by a config.
pub type ClassOf<Cfg> = <<Cfg as crate::config::EGraphConfig>::Au as crate::config::AuIds>::Class;
/// The OR-node id selected by a config.
pub type OrOf<Cfg> = <<Cfg as crate::config::EGraphConfig>::Au as crate::config::AuIds>::Or;
/// The term id selected by a config.
pub type TermOf<Cfg> = <<Cfg as crate::config::EGraphConfig>::Au as crate::config::AuIds>::Term;

/// A typed span into a flattened persistent pool: `start` is a typed position
/// in the target pool (so spans cannot be applied to the wrong pool), `len`
/// is in the configured index width. All conversions are checked.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span<I: containers::DenseId> {
    pub start: I,
    pub len: I::Index,
}

impl<I: containers::DenseId> Span<I> {
    /// Build a span from usize bounds, panicking if either exceeds the
    /// configured AU capacity.
    #[inline]
    pub fn new(start: usize, len: usize) -> Self {
        use crate::containers::IndexLike;
        Span {
            start: I::from_usize(start),
            len: I::Index::try_from_usize(len).expect("span length exceeds configured AU capacity"),
        }
    }

    #[inline]
    pub fn start_usize(&self) -> usize {
        self.start.to_usize()
    }

    #[inline]
    pub fn len_usize(&self) -> usize {
        use crate::containers::IndexLike;
        self.len.as_usize()
    }

    #[inline]
    pub fn end_usize(&self) -> usize {
        self.start_usize() + self.len_usize()
    }
}

/// Errors surfaced while building an AU snapshot (§4.1).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AuError {
    /// A class transitively needed by a root has no admissible finite member
    /// after filtering `FLAG_SUBSUMED` nodes. The payload is the raw dense
    /// class index, carried as `u64` for DIAGNOSTIC DISPLAY ONLY: it is not a
    /// typed id and must never flow back into AU indexing operations.
    NoFiniteRepresentative(u64),
    /// A multiplicity did not fit in `u32` during snapshot construction.
    MultiplicityOverflow,
    /// A session method received a config whose cycle mode differs from the
    /// mode the session's search space was created with. The space's cycle
    /// contexts are derived under one mode; mixing modes would silently
    /// corrupt cycle filtering.
    CycleModeMismatch,
}

impl core::fmt::Display for AuError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AuError::NoFiniteRepresentative(c) => {
                write!(f, "class auc{c} has no admissible finite member")
            }
            AuError::MultiplicityOverflow => write!(f, "multiplicity does not fit in u32"),
            AuError::CycleModeMismatch => write!(
                f,
                "config cycle mode differs from the session's search-space mode"
            ),
        }
    }
}

impl std::error::Error for AuError {}
