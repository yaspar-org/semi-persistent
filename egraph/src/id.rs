// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Concrete e-graph identifier types.

pub use semi_persistent_containers::{SparseSetId, UseListId, UseNodeId};

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

/// Mint the dense id for an arena or log position, checked.
///
/// Use this wherever an id is derived from a container position. A position and its
/// id share a word (`D::Index`) but NOT a range: a bit-stealing id reserves the top
/// bit, so `D::Index` spans twice the id space and a position at or past
/// `D::id_bound()` has no id at all. [`DenseId::from_usize`] rejects such a
/// position; this helper centralizes the fallible check and the e-graph-specific
/// exhaustion message before any owning structure is mutated.
///
/// These cases are reachable in practice: [`RuleId`] and [`AxiomId`] are 15-bit,
/// so the 32769th registered rule has no representable ID.
#[inline]
pub fn id_at<D: crate::containers::DenseId>(pos: usize) -> D {
    D::try_new(pos).unwrap_or_else(|| panic!("position {pos} has no id: the id space is exhausted"))
}

/// [`id_at`] for a position already in the container's index word.
#[inline]
pub fn id_at_index<D: crate::containers::DenseId>(pos: D::Index) -> D {
    use crate::containers::IndexLike;
    id_at(pos.as_usize())
}

/// The ids for positions `0..n`, with the bound checked once.
///
/// The loop form of [`id_at`]. Scanning a population by position needs one check, not
/// one per step: positions are contiguous, so only the last can be out of range. This
/// panics before yielding anything rather than producing a valid prefix and then
/// failing partway through a long scan.
///
/// Use this when the caller cannot show `n` is within the id space. When it can — most
/// often because the container is indexed *by* `D`, so its own capacity guard is the id
/// bound — the bare [`DenseId::from_usize`] is correct and the reason belongs in a
/// comment at the loop.
#[inline]
pub fn ids_upto<D: crate::containers::DenseId>(n: usize) -> impl Iterator<Item = D> {
    if n > 0 {
        let _ = id_at::<D>(n - 1);
    }
    (0..n).map(D::from_usize)
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
    SPair = 5,
    /// Associative flattened list (variadic, pool).
    Seq = 6,
    /// Associative-commutative sorted multiset (variadic, pool). Multiset child
    /// representation `(G, mult)`; the AC algebra in Kapur's AC-CC terms. Stores plain AC
    /// (`Clamp::None`) AND nilpotent (`Clamp::Nilpotent`) ops — nilpotent keeps true
    /// multiplicities here for the build/recanonize mod-n reduction (a `Set` dedup would
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::containers::DenseId;

    /// `id_at` accepts exactly the positions that have an id. `RuleId` is 15-bit, so
    /// the boundary is reachable in a test — see `registry::tests` for the registry
    /// path that used to alias across it.
    #[test]
    fn id_at_covers_the_whole_id_space() {
        let bound = 1usize << 15; // RuleId is define_id15!
        assert_eq!(id_at::<RuleId>(0).to_usize(), 0);
        assert_eq!(id_at::<RuleId>(bound - 1).to_usize(), bound - 1);
    }

    #[test]
    #[should_panic(expected = "the id space is exhausted")]
    fn id_at_rejects_a_position_with_no_id() {
        // Representable as a `u16` index word, but past `RuleId`'s 15-bit bound.
        let _ = id_at::<RuleId>(1usize << 15);
    }

    /// `id_at_index` is the same check, entered from a container's index word.
    #[test]
    fn id_at_index_agrees_with_id_at() {
        let pos: <RuleId as DenseId>::Index = 7;
        assert_eq!(id_at_index::<RuleId>(pos), id_at::<RuleId>(7));
    }

    #[test]
    #[should_panic(expected = "the id space is exhausted")]
    fn id_at_index_rejects_a_position_with_no_id() {
        let pos: <RuleId as DenseId>::Index = 1u16 << 15;
        let _ = id_at_index::<RuleId>(pos);
    }

    #[test]
    fn ids_upto_yields_every_position_in_order() {
        let ids: Vec<usize> = ids_upto::<RuleId>(4).map(|r| r.to_usize()).collect();
        assert_eq!(ids, vec![0, 1, 2, 3]);
        assert_eq!(ids_upto::<RuleId>(0).count(), 0);
    }

    /// The whole id space scans, so the check is on the last position and not one past it.
    #[test]
    fn ids_upto_accepts_a_full_id_space() {
        let bound = 1usize << 15;
        assert_eq!(ids_upto::<RuleId>(bound).count(), bound);
    }

    /// The panic lands before the first item, not partway through: an iterator that
    /// yielded 32768 good ids and then aliased would corrupt whatever it fed.
    #[test]
    #[should_panic(expected = "the id space is exhausted")]
    fn ids_upto_rejects_a_population_larger_than_the_id_space() {
        let _ = ids_upto::<RuleId>((1usize << 15) + 1);
    }
}
