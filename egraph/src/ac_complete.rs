// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! AC congruence completion: superposition + inter-reduction during rebuild.
//!
//! This restores AC congruence completeness, which canonization alone cannot
//! provide: recanonicalizing an AC node substitutes equal *atoms* but never
//! equal *sub-sums*, so equalities like `+(a,b)=c ∧ +(b,d)=e ⊨ +(c,d)=+(a,e)`
//! are missed. See `doc/design/ac-congruence-completeness.md` for the theory and
//! `doc/future/ac-congruence-completeness-plan.md` for this implementation.
//!
//! The completion is owned by `rebuild()` (plan §2, Option A): after the existing
//! worklist closure drains, we build the [`AcPartnerSnapshot`] over the live AC
//! nodes and run a per-AC-op critical-pair round against it, materializing new
//! nodes and pushing merges back through the worklist, to a joint fixpoint.
//!
//! This file currently contains the snapshot (T3). The completion round (T4/T5)
//! lands here next.

use crate::canon::{ACCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::literal::LitVal;
use std::collections::HashMap;

/// A per-round search index over the live AC nodes, restricted to AC ops.
///
/// This is the narrow slice of [`crate::index::IndexStore`] that the completion
/// search needs: the spec's candidate set `⋃_{x ∈ distinct(M)} by_contains[x] ∩
/// by_op[f]` (plan §5). We pre-intersect with `by_op[f]` by keying on
/// `(op, child_repr)`, so a lookup directly yields the AC nodes of op `f` that
/// contain child class `x` — no separate `by_op` intersection at use time.
///
/// Unlike `IndexStore`, this is built *during* `rebuild()` (the matcher's
/// `IndexStore` is built afterwards), it covers only AC ops, and it carries no
/// `by_repr`/`by_child_pos`. Subsumed nodes are skipped, matching `IndexStore`.
///
/// Node ids in each bucket are sorted and deduplicated.
pub struct AcPartnerSnapshot<Cfg: EGraphConfig> {
    /// `(op, child_repr) → sorted, deduped AC node ids of that op containing the child`.
    by_op_contains: HashMap<(Cfg::O, Cfg::G), Vec<Cfg::G>>,
    /// All live (non-subsumed) AC node ids, sorted — the set of completion targets/rules.
    ac_nodes: Vec<Cfg::G>,
}

impl<Cfg: EGraphConfig> AcPartnerSnapshot<Cfg>
where
    ACCanon: VarCanon<Cfg::G, Cfg::C>,
{
    /// Build the snapshot from the current e-graph state. Walks every node once,
    /// keeping only AC nodes (`ops.is_ac`), skipping subsumed nodes.
    pub fn build<L: LitVal, const TRACK: bool, const PROOFS: bool>(
        eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    ) -> Self {
        let mut by_op_contains: HashMap<(Cfg::O, Cfg::G), Vec<Cfg::G>> = HashMap::new();
        let mut ac_nodes: Vec<Cfg::G> = Vec::new();

        // Active AC nodes only: skip user-subsumed (not matchable) and AC-collapsed
        // (reducible by a smaller rule) — neither is a completion rule. See §6b.
        let inactive = crate::node_types::FLAG_SUBSUMED | crate::node_types::FLAG_AC_COLLAPSED;
        for i in 0..eg.node_count() {
            let gid = Cfg::G::from_usize(i);
            if eg.node_flags(gid) & inactive != 0 {
                continue;
            }
            let op = eg.node_op(gid);
            if !eg.ops().is_ac(op) {
                continue;
            }
            ac_nodes.push(gid);

            // Bucket this node under each distinct child class it contains.
            let mut seen: Vec<Cfg::G> = Vec::new();
            eg.for_each_child(gid, |child, _mult| {
                let cr = eg.class_repr(child);
                if !seen.contains(&cr) {
                    seen.push(cr);
                    by_op_contains.entry((op, cr)).or_default().push(gid);
                }
            });
        }

        for v in by_op_contains.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
        ac_nodes.sort_unstable();
        ac_nodes.dedup();

        Self {
            by_op_contains,
            ac_nodes,
        }
    }

    /// All live AC node ids (sorted). These are the completion targets — each is
    /// both a node `+M = d` to complete and a rule `+M → d` to complete against.
    pub fn ac_nodes(&self) -> &[Cfg::G] {
        &self.ac_nodes
    }

    /// AC nodes of op `op` that contain child class `child_repr` (sorted, deduped).
    /// This is the spec's `by_contains[child_repr] ∩ by_op[op]`, pre-intersected.
    pub fn partners(&self, op: Cfg::O, child_repr: Cfg::G) -> &[Cfg::G] {
        self.by_op_contains
            .get(&(op, child_repr))
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

    /// Brute-force reference: AC nodes of `op` whose `ac_children` contain `cr`.
    fn ref_partners(
        eg: &EGraph31<NiraLitVal, false, false>,
        op: crate::id::OpId,
        cr: crate::id::ENodeId,
    ) -> Vec<crate::id::ENodeId> {
        let mut out = Vec::new();
        let mut buf = Vec::new();
        let inactive = crate::node_types::FLAG_SUBSUMED | crate::node_types::FLAG_AC_COLLAPSED;
        for i in 0..eg.node_count() {
            let gid = crate::id::ENodeId::new(i as u32);
            if eg.node_flags(gid) & inactive != 0 {
                continue;
            }
            if eg.node_op(gid) != op || !eg.ops().is_ac(op) {
                continue;
            }
            eg.ac_children(gid, &mut buf);
            if buf.iter().any(|&(c, _)| eg.class_repr(c) == cr) {
                out.push(gid);
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    #[test]
    fn snapshot_matches_by_contains_variadic_fixture() {
        // Mirror of index.rs `by_contains_variadic`, but through the AC snapshot.
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let plus = eg.register_ac("plus", int, int);
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);
        let z_op = eg.register_op0("z", int);

        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        let z = eg.add(z_op, &[]);
        let pxy = eg.add(plus, &[x, y]);
        let pxz = eg.add(plus, &[x, z]);

        let snap = AcPartnerSnapshot::build(&eg);

        // x is contained in both pxy and pxz.
        let mut cx = snap.partners(plus, x).to_vec();
        cx.sort_unstable();
        assert_eq!(cx, vec![pxy.min(pxz), pxy.max(pxz)]);

        // y is contained only in pxy.
        assert_eq!(snap.partners(plus, y), &[pxy]);

        // ac_nodes lists exactly the two AC sums (not the op0 leaves).
        assert_eq!(snap.ac_nodes(), &[pxy.min(pxz), pxy.max(pxz)]);
    }

    #[test]
    fn snapshot_only_indexes_ac_ops() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let plus = eg.register_ac("plus", int, int);
        let f = eg.register_op1("f", int, int); // Normal — must not appear
        let x_op = eg.register_op0("x", int);

        let x = eg.add(x_op, &[]);
        let fx = eg.add(f, &[x]);
        let pfx = eg.add(plus, &[x, fx]);

        let snap = AcPartnerSnapshot::build(&eg);

        // Only the AC node is a completion target.
        assert_eq!(snap.ac_nodes(), &[pfx]);
        // The plain node f(x) is not bucketed even though it contains x.
        assert!(snap.partners(f, eg.class_repr(x)).is_empty());
        // The AC sum is found under both its children.
        assert_eq!(snap.partners(plus, eg.class_repr(x)), &[pfx]);
        assert_eq!(snap.partners(plus, eg.class_repr(fx)), &[pfx]);
    }

    #[test]
    fn snapshot_agrees_with_brute_force_after_merge() {
        // Multiplicities + a merge that changes class reprs.
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let plus = eg.register_ac("plus", int, int);
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let d_op = eg.register_op0("d", int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let d = eg.add(d_op, &[]);
        let _ab = eg.add(plus, &[a, b]);
        let _bd = eg.add(plus, &[b, d]);
        let _abb = eg.add(plus, &[a, b, b]); // multiplicity > 1 on b

        // Merge a and d, then rebuild so reprs settle.
        eg.merge(a, d);
        eg.rebuild();

        let snap = AcPartnerSnapshot::build(&eg);

        // For every (AC op, child class) the snapshot must equal the brute-force set.
        for x in [a, b, d] {
            let cr = eg.class_repr(x);
            let mut got = snap.partners(plus, cr).to_vec();
            got.sort_unstable();
            assert_eq!(
                got,
                ref_partners(&eg, plus, cr),
                "mismatch for child {cr:?}"
            );
        }
    }

    #[test]
    fn ac_collapsed_leaves_completion_set_but_stays_matchable() {
        // FLAG_AC_COLLAPSED and FLAG_SUBSUMED are distinct (design §6b): a collapsed node
        // drops out of completion's active set but remains visible to the matcher's index.
        use crate::index::IndexStore;
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let plus = eg.register_ac("plus", int, int);
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let pab = eg.add(plus, &[a, b]);

        // Baseline: pab is both a completion candidate and in the matcher index.
        assert_eq!(AcPartnerSnapshot::build(&eg).ac_nodes(), &[pab]);
        assert!(IndexStore::build(&eg).by_op[&plus].data.contains(&pab));

        // Collapse it (the completion-internal retirement).
        eg.set_ac_collapsed(pab);

        // Gone from completion's active set...
        assert!(
            AcPartnerSnapshot::build(&eg).ac_nodes().is_empty(),
            "AC-collapsed node must leave the completion active set"
        );
        // ...but still matchable: present in the index and still in its class.
        assert!(
            IndexStore::build(&eg).by_op[&plus].data.contains(&pab),
            "AC-collapsed node must stay visible to the matcher (not subsumed)"
        );
        assert_eq!(eg.class_repr(pab), eg.class_repr(pab));

        // Contrast: user subsume DOES hide it from the matcher.
        eg.subsume(pab);
        assert!(
            !IndexStore::build(&eg)
                .by_op
                .get(&plus)
                .is_some_and(|v| v.data.contains(&pab)),
            "subsumed node must be hidden from the matcher index"
        );
    }
}
