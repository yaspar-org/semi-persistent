// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent union-find with optional proof tracking.

use crate::containers::{DenseId, Tagged};

/// The `inst` of a [`Justification::Rewrite`] for which no rule instance was
/// recorded: the step's premises are unknown, and explanation consumers must
/// not treat it as a leaf.
pub const NO_INSTANCE: u32 = u32::MAX;

/// Why two e-nodes were unified.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Justification<G: DenseId> {
    /// No-op filler used to default-initialize slots (e.g. as the
    /// `resize_default` filler during restore, and the initial entry from
    /// `make_set`). Never carries proof information; never observed as a real
    /// justification.
    #[default]
    Filler,
    /// A rule application. `inst` names the rule instance whose premise pairs
    /// (the equalities the match and the right-hand side's construction used)
    /// `explain_deep` expands, as it expands a congruence step's children;
    /// [`NO_INSTANCE`] when the caller recorded none.
    Rewrite {
        rule_id: crate::id::RuleId,
        inst: u32,
    },
    Congruence {
        node_a: G,
        node_b: G,
    },
    /// An axiom: a `union` command or another caller-supplied equality.
    /// `axiom_id` is the index word of the configuration's axiom id
    /// (`EGraphConfig::A`), so its width follows the id family's, as
    /// `Assumption`'s does; [`Justification::axiom`] and
    /// [`Justification::axiom_id`] convert to and from the typed id.
    Axiom {
        axiom_id: <G as DenseId>::Index,
    },
    /// A node equal to its normal form under the operator's laws, where the
    /// normal form is one child's class (`and(a, a) = a`, `x + 0 = x`) or the
    /// unit (`xor(a, a) = 0`). The premises are the equalities among the
    /// node's original children and between them and `normal` or the unit:
    /// `explain_deep` expands them.
    Normalize {
        node: G,
        normal: G,
    },
    /// A client's set, AC or associative term, kept as an evidence node
    /// holding the children it was given, merged with the node it is stored
    /// as. The build `find`s, flattens (splicing a same-operator node of a
    /// child's class into the list) and normalizes the children; `inst` names
    /// the splices as `(child, spliced node)` pairs, and `explain_deep`
    /// explains them together with every class equality among the given
    /// children, the spliced nodes' children and the stored node's children.
    Build {
        node: G,
        inst: u32,
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

impl<G: DenseId> Justification<G> {
    /// The `Axiom` step for axiom `a`.
    pub fn axiom<A: DenseId<Index = G::Index>>(a: A) -> Self {
        Justification::Axiom {
            axiom_id: a.to_index(),
        }
    }

    /// The axiom an `Axiom` step names, as the typed id `A`; `None` for any
    /// other step.
    pub fn axiom_id<A: DenseId<Index = G::Index>>(&self) -> Option<A> {
        match *self {
            Justification::Axiom { axiom_id } => Some(crate::id::id_at_index::<A>(axiom_id)),
            _ => None,
        }
    }
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

    /// The axiom id follows the configuration's word: the 64-bit
    /// configurations use the 63-bit `AxiomId63`, and an axiom step carries an
    /// id above `u32::MAX` intact.
    #[test]
    fn axiom_id_has_the_configurations_width() {
        use crate::config::EGraphConfig;
        use crate::nodes::{Config64, DefaultConfig, ENodeId64};
        assert_eq!(
            std::mem::size_of::<<DefaultConfig as EGraphConfig>::A>(),
            std::mem::size_of::<u32>()
        );
        assert_eq!(
            std::mem::size_of::<<Config64 as EGraphConfig>::A>(),
            std::mem::size_of::<u64>()
        );
        let big = crate::id::AxiomId63::new(1u64 << 40);
        let j = Justification::<ENodeId64>::axiom(big);
        assert_eq!(j.axiom_id::<crate::id::AxiomId63>(), Some(big));
        assert_eq!(
            Justification::<ENodeId64>::Congruence {
                node_a: ENodeId64::new(0),
                node_b: ENodeId64::new(1)
            }
            .axiom_id::<crate::id::AxiomId63>(),
            None
        );
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
