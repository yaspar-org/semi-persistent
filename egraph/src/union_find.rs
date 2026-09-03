// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent union-find with optional proof tracking.

use crate::containers::{DenseId, Tagged};

/// Why two e-nodes were unified.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Justification<G: DenseId> {
    /// No-op filler used to default-initialize slots (e.g. as the
    /// `resize_default` filler during restore, and the initial entry from
    /// `make_set`). Never carries proof information; never observed as a real
    /// justification.
    #[default]
    Filler,
    Rewrite {
        rule_id: crate::id::RuleId,
    },
    Congruence {
        node_a: G,
        node_b: G,
    },
    Axiom {
        axiom_id: crate::id::AxiomId,
    },
    /// AC completion: a critical-pair superposition between two rules sharing a child class.
    /// The merge equates the normalized reducts. (Kapur Def 3.2.)
    ACSuperposition {
        node_a: G,
        node_b: G,
    },
    /// A completion inter-reduction merge (Kapur Algo 1 step 4): an AC
    /// monomial's sub-multiset substituted by a class's minimal monomial, or
    /// an A-only sequence's contiguous subsequence substituted by the
    /// shortlex-least spelling (`a_round`). `node_a` is the rewritten node,
    /// `node_b` its normal form.
    ACInterReduction {
        node_a: G,
        node_b: G,
    },
    /// Semantic-axiom critical pair (Kapur §4 per-rule): idempotent/nilpotent axiom critical
    /// pair, or an identity-drop / degeneracy merge derived during completion normalization.
    ACAxiomCP {
        node_a: G,
        node_b: G,
    },
    /// Cancellative closure: `x∘z = y∘z ⟹ x = y` (Kapur §5.2).
    Cancellative {
        node_a: G,
        node_b: G,
    },
    /// Inverse-pair cancellation: `x ∘ inv(x) = e` recognized and merged.
    InverseCancel {
        node_a: G,
        node_b: G,
    },
    /// External assumption: a companion solver (the `satcore` crate's EUF
    /// layer) asserted an equality atom true, and this merge is that
    /// assertion. The payload is an opaque word of the configuration's index
    /// width, so it is capacity-coupled to the id family like every scaling
    /// id (see `config.rs`); the client crate owns the encoding and maps the
    /// word back to its own literal type when proof extraction surfaces it
    /// as a leaf antecedent. That crossing is what lets conflict analysis
    /// move from an e-graph explanation into the client's Boolean domain.
    Assumption {
        lit: <G as DenseId>::Index,
    },
}

impl<G: DenseId> Tagged for Justification<G> {
    type Repr = crate::containers::BoolTagged<Justification<G>>;

    fn into_repr(self) -> Self::Repr {
        crate::containers::BoolTagged::new(self)
    }
    fn from_repr(stored: &Self::Repr) -> Self {
        stored.value
    }
    fn tag(stored: &Self::Repr) -> bool {
        stored.tagged
    }
    fn set_tag(stored: &mut Self::Repr) {
        stored.tagged = true;
    }
    fn clear_tag(stored: &mut Self::Repr) {
        stored.tagged = false;
    }
}

/// Semi-persistent union-find: the VERIFIED kernel, with this crate's
/// [`Justification`] as the proof payload. The implementation lives in
/// `containers-verus/src/union_find.rs`: dual fast/proof forests under
/// `PROOFS`, by-rank and directed unions, two-pass path-compressing `find`,
/// re-rooting proof edges, LCA `explain`, with W1 (the partition invariant)
/// machine-checked (`containers-verus/doc/design/egraph-class-layer.md`).
pub type UnionFind<T, const TRACK: bool = true, const PROOFS: bool = false> =
    crate::containers::union_find::UnionFind<T, Justification<T>, TRACK, PROOFS>;

/// Opaque token for [`UnionFind::mark`] / [`UnionFind::restore`].
pub type UnionFindToken = crate::containers::union_find::UnionFindToken;

/// Reusable scratch buffers for proof extraction (the kernel's, with this
/// crate's justification payload).
pub type ProofBuf<T> = crate::containers::union_find::ProofBuf<T, Justification<T>>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::ENodeId;

    type UF = UnionFind<ENodeId, false, false>;

    fn uf(n: u32) -> UF {
        let mut uf = UF::new();
        for i in 0..n {
            uf.make_set(ENodeId::new(i));
        }
        uf
    }

    #[test]
    fn union_directed_forces_survivor() {
        let mut uf = uf(2);
        let a = ENodeId::new(0);
        let b = ENodeId::new(1);
        // prefer_a = true keeps a's root as the survivor.
        let (survivor, absorbed) = uf.union_directed(a, b, true).unwrap();
        assert_eq!(survivor, a);
        assert_eq!(absorbed, b);
        assert_eq!(uf.find(a), a);
        assert_eq!(uf.find(b), a);
    }

    #[test]
    fn union_directed_other_survivor() {
        let mut uf = uf(2);
        let a = ENodeId::new(0);
        let b = ENodeId::new(1);
        // prefer_a = false keeps b's root as the survivor.
        let (survivor, absorbed) = uf.union_directed(a, b, false).unwrap();
        assert_eq!(survivor, b);
        assert_eq!(absorbed, a);
        assert_eq!(uf.find(a), b);
        assert_eq!(uf.find(b), b);
    }

    #[test]
    fn justification_named_repr_preserves_value_when_tagged() {
        let just = Justification::<ENodeId>::Congruence {
            node_a: ENodeId::new(1),
            node_b: ENodeId::new(2),
        };
        let mut repr = just.into_repr();
        assert!(!Justification::<ENodeId>::tag(&repr));
        Justification::<ENodeId>::set_tag(&mut repr);
        assert!(Justification::<ENodeId>::tag(&repr));
        assert_eq!(Justification::<ENodeId>::from_repr(&repr), just);
        Justification::<ENodeId>::clear_tag(&mut repr);
        assert!(!Justification::<ENodeId>::tag(&repr));
    }

    #[test]
    fn union_directed_can_force_against_rank() {
        // Build a taller tree rooted at `tall`, then a singleton `small`, and force `small`
        // to survive even though it is the shorter tree. `find` must still resolve correctly
        // (the rank stays a valid height upper bound, see `union_inner`).
        let mut uf = uf(4);
        let (n0, n1, n2, small) = (
            ENodeId::new(0),
            ENodeId::new(1),
            ENodeId::new(2),
            ENodeId::new(3),
        );
        // n0,n1 then merge in n2 to bump rank at n0's root.
        uf.union(n0, n1);
        uf.union(n0, n2);
        let tall = uf.find(n0);
        // Force the singleton `small` to be the survivor of (tall ∪ small).
        let (survivor, absorbed) = uf.union_directed(tall, small, false).unwrap();
        assert_eq!(survivor, small);
        assert_eq!(absorbed, tall);
        // Every original element now resolves to `small`.
        for n in [n0, n1, n2, small] {
            assert_eq!(uf.find(n), small);
        }
    }

    #[test]
    fn union_directed_idempotent_when_same_class() {
        let mut uf = uf(2);
        let a = ENodeId::new(0);
        let b = ENodeId::new(1);
        uf.union(a, b);
        // Already merged: a directed union returns None regardless of preference.
        assert!(uf.union_directed(a, b, true).is_none());
        assert!(uf.union_directed(a, b, false).is_none());
    }
}
