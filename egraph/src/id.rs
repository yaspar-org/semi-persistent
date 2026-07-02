// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Concrete e-graph identifier types.

pub use semi_persistent_containers::id::{SparseSetId, UseListId, UseNodeId};

semi_persistent_containers::define_id31! {
    /// A 31-bit e-node identifier.
    pub struct ENodeId / StoredENodeId, "e";
}

semi_persistent_containers::define_id31! {
    /// A 31-bit sort identifier (Bool, Int, Real, …).
    pub struct SortId / StoredSortId, "sort";
}

semi_persistent_containers::define_id31! {
    /// A 31-bit operator identifier (+, ×, and, or, =, ite, …).
    pub struct OpId / StoredOpId, "op";
}

semi_persistent_containers::define_id15! {
    /// A 15-bit rule identifier (indexes into the rule registry).
    pub struct RuleId / StoredRuleId, "r";
}

semi_persistent_containers::define_id15! {
    /// A 15-bit axiom identifier (user-asserted equalities).
    pub struct AxiomId / StoredAxiomId, "ax";
}

/// The ten node kinds. Stored in a routing table indexed by [`ENodeId`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum ENodeKind {
    /// Nullary (constant, no children).
    Plain0 = 0,
    /// Unary (1 inline child).
    Plain1 = 1,
    /// Binary (2 inline children).
    Plain2 = 2,
    /// Ternary (3 inline children).
    Plain3 = 3,
    /// N-ary ordered (N > 3, children in pool).
    PlainN = 4,
    /// Commutative sorted pair (2 inline children).
    C = 5,
    /// Associative flattened list (variadic, pool).
    A = 6,
    /// Associative-commutative sorted multiset (variadic, pool). Multiset child
    /// representation `(G, mult)`; the AC algebra in Kapur's AC-CC terms. Stores plain AC
    /// (`Clamp::None`) AND nilpotent (`Clamp::Nilpotent`) ops — nilpotent keeps true
    /// multiplicities here for the completion-time mod-n reduction (a `Set` dedup would
    /// destroy them). The op's `Clamp` (on `OpKind`) says which.
    MSet = 7,
    /// Associative-commutative-idempotent sorted set (variadic, pool). Set child
    /// representation (bare `G`, {0,1} counts). Idempotent ops only (`Clamp::Idempotent`):
    /// dedup is the sound build/recanonize canonize rule for them. Nilpotent ops do NOT
    /// live here (see `MSet`).
    Set = 8,
    /// Literal leaf (no children, has value).
    Lit = 9,
}
