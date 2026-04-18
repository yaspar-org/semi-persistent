// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Transient sorted indices for leapfrog triejoin, bulk-rebuilt from e-graph state.

use crate::canon::{ACCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::DenseId;
use crate::egraph::EGraph;
use crate::literal::LitVal;
use std::collections::HashMap;

/// Sorted index over node ids, backed by a contiguous `Vec<G>`.
/// Supports O(log n) seek and O(1) step for leapfrog join.
#[derive(Clone, Debug)]
pub struct SortedVec<G> {
    pub data: Vec<G>,
}

impl<G: DenseId> SortedVec<G> {
    pub fn len(&self) -> usize {
        self.data.len()
    }
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
    pub fn iter(&self) -> SortedVecIter<'_, G> {
        SortedVecIter::new(&self.data)
    }
}

/// Cursor into a `SortedVec<G>`. Implements seek/step for leapfrog.
pub struct SortedVecIter<'a, G> {
    data: &'a [G],
    pos: usize,
}

impl<'a, G: DenseId> SortedVecIter<'a, G> {
    pub fn new(data: &'a [G]) -> Self {
        Self { data, pos: 0 }
    }

    #[inline]
    pub fn is_valid(&self) -> bool {
        self.pos < self.data.len()
    }

    #[inline]
    pub fn key(&self) -> G {
        self.data[self.pos]
    }

    #[inline]
    pub fn step(&mut self) {
        self.pos += 1;
    }

    /// Advance to the first element >= target. O(log n).
    #[inline]
    pub fn seek(&mut self, target: G) {
        let remaining = &self.data[self.pos..];
        self.pos += remaining.partition_point(|x| *x < target);
    }
}

/// All sorted indices for leapfrog join, bulk-rebuilt after each e-graph rebuild.
pub struct IndexStore<Cfg: EGraphConfig> {
    /// by_op[op] → sorted vec of node ids with that operator
    pub by_op: HashMap<Cfg::O, SortedVec<Cfg::G>>,
    /// by_repr[repr] → sorted vec of node ids in that e-class
    pub by_repr: HashMap<Cfg::G, SortedVec<Cfg::G>>,
    /// by_child_pos[(child_repr, position)] → sorted vec of parent node ids
    pub by_child_pos: HashMap<(Cfg::G, u32), SortedVec<Cfg::G>>,
    /// by_contains[child_repr] → sorted vec of variadic parent node ids (A/AC/ACI/PlainN)
    pub by_contains: HashMap<Cfg::G, SortedVec<Cfg::G>>,
}

impl<Cfg: EGraphConfig> IndexStore<Cfg>
where
    ACCanon: VarCanon<Cfg::G, Cfg::C>,
{
    /// Bulk-rebuild all indices from the current e-graph state.
    /// Call after `eg.rebuild()`.
    pub fn build<L: LitVal, const TRACK: bool, const PROOFS: bool>(
        eg: &EGraph<Cfg, L, TRACK, PROOFS>,
    ) -> Self {
        let n = eg.node_count();

        let mut by_op: HashMap<Cfg::O, Vec<Cfg::G>> = HashMap::new();
        let mut by_repr: HashMap<Cfg::G, Vec<Cfg::G>> = HashMap::new();
        let mut by_child_pos: HashMap<(Cfg::G, u32), Vec<Cfg::G>> = HashMap::new();
        let mut by_contains: HashMap<Cfg::G, Vec<Cfg::G>> = HashMap::new();

        for i in 0..n {
            let gid = Cfg::G::from_usize(i);
            if eg.node_flags(gid) & crate::node_types::FLAG_SUBSUMED != 0 {
                continue;
            }
            let op = eg.node_op(gid);
            let repr = eg.class_repr(gid);

            by_op.entry(op).or_default().push(gid);
            by_repr.entry(repr).or_default().push(gid);

            let mut pos = 0u32;
            let is_variadic = eg.for_each_child(gid, |child, _mult| {
                let child_repr = eg.class_repr(child);
                by_child_pos.entry((child_repr, pos)).or_default().push(gid);
                pos += 1;
            });
            // For variadic nodes (arity > 0 from PlainN/A/AC/ACI), also populate by_contains
            if is_variadic > 3
                || matches!(
                    eg.node_ref(gid),
                    crate::typed_routing::NodeRef::A(_)
                        | crate::typed_routing::NodeRef::AC(_)
                        | crate::typed_routing::NodeRef::ACI(_)
                        | crate::typed_routing::NodeRef::PlainN(_)
                )
            {
                let mut seen = Vec::new(); // dedup within one node
                eg.for_each_child(gid, |child, _mult| {
                    let cr = eg.class_repr(child);
                    if !seen.contains(&cr) {
                        seen.push(cr);
                        by_contains.entry(cr).or_default().push(gid);
                    }
                });
            }
        }

        fn finalize<K: Eq + std::hash::Hash, G: DenseId>(
            map: HashMap<K, Vec<G>>,
        ) -> HashMap<K, SortedVec<G>> {
            map.into_iter()
                .map(|(k, mut v)| {
                    v.sort_unstable();
                    v.dedup();
                    (k, SortedVec { data: v })
                })
                .collect()
        }

        Self {
            by_op: finalize(by_op),
            by_repr: finalize(by_repr),
            by_child_pos: finalize(by_child_pos),
            by_contains: finalize(by_contains),
        }
    }

    /// Get an iterator over nodes with the given operator.
    pub fn iter_by_op(&self, op: Cfg::O) -> SortedVecIter<'_, Cfg::G> {
        match self.by_op.get(&op) {
            Some(sv) => SortedVecIter::new(&sv.data),
            None => SortedVecIter::new(&[]),
        }
    }

    /// Get an iterator over nodes in the given e-class.
    pub fn iter_by_repr(&self, repr: Cfg::G) -> SortedVecIter<'_, Cfg::G> {
        match self.by_repr.get(&repr) {
            Some(sv) => SortedVecIter::new(&sv.data),
            None => SortedVecIter::new(&[]),
        }
    }

    /// Get an iterator over parent nodes that have `child_repr` at position `pos`.
    pub fn iter_by_child_pos(&self, child_repr: Cfg::G, pos: u32) -> SortedVecIter<'_, Cfg::G> {
        match self.by_child_pos.get(&(child_repr, pos)) {
            Some(sv) => SortedVecIter::new(&sv.data),
            None => SortedVecIter::new(&[]),
        }
    }

    /// Get an iterator over variadic nodes containing `child_repr`.
    pub fn iter_by_contains(&self, child_repr: Cfg::G) -> SortedVecIter<'_, Cfg::G> {
        match self.by_contains.get(&child_repr) {
            Some(sv) => SortedVecIter::new(&sv.data),
            None => SortedVecIter::new(&[]),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraph31;
    use crate::literal::NiraLitVal;

    #[test]
    fn by_op_index() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let g = eg.register_op1("g", int, int);
        let x_op = eg.register_op0("x", int);

        let x = eg.add(x_op, &[]);
        let fx = eg.add(f, &[x]);
        let gx = eg.add(g, &[x]);
        let ffx = eg.add(f, &[fx]);

        let idx = IndexStore::build(&eg);

        // Two f-nodes: fx, ffx
        let f_nodes = &idx.by_op[&f];
        assert_eq!(f_nodes.len(), 2);
        assert!(f_nodes.data.contains(&fx));
        assert!(f_nodes.data.contains(&ffx));

        // One g-node
        assert_eq!(idx.by_op[&g].len(), 1);
        assert!(idx.by_op[&g].data.contains(&gx));

        // One x-node
        assert_eq!(idx.by_op[&x_op].len(), 1);
    }

    #[test]
    fn by_repr_after_merge() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);

        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        eg.merge(x, y);
        eg.rebuild();

        let idx = IndexStore::build(&eg);
        let repr = eg.class_repr(x);
        let class_nodes = &idx.by_repr[&repr];
        assert_eq!(class_nodes.len(), 2);
    }

    #[test]
    fn by_child_pos_index() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let g = eg.register_op2("g", int, int, int);
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);

        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        let fx = eg.add(f, &[x]);
        let gxy = eg.add(g, &[x, y]);

        let idx = IndexStore::build(&eg);

        // x is child at pos 0 of both fx and gxy
        let parents_x_0 = &idx.by_child_pos[&(x, 0)];
        assert_eq!(parents_x_0.len(), 2);
        assert!(parents_x_0.data.contains(&fx));
        assert!(parents_x_0.data.contains(&gxy));

        // y is child at pos 1 of gxy only
        let parents_y_1 = &idx.by_child_pos[&(y, 1)];
        assert_eq!(parents_y_1.len(), 1);
        assert!(parents_y_1.data.contains(&gxy));
    }

    #[test]
    fn seek_and_step() {
        let data = vec![
            crate::id::ENodeId::from_usize(2),
            crate::id::ENodeId::from_usize(5),
            crate::id::ENodeId::from_usize(8),
            crate::id::ENodeId::from_usize(12),
        ];
        let mut it = SortedVecIter::new(&data);
        assert!(it.is_valid());
        assert_eq!(it.key().to_usize(), 2);

        it.seek(crate::id::ENodeId::from_usize(5));
        assert_eq!(it.key().to_usize(), 5);

        it.seek(crate::id::ENodeId::from_usize(7));
        assert_eq!(it.key().to_usize(), 8);

        it.step();
        assert_eq!(it.key().to_usize(), 12);

        it.step();
        assert!(!it.is_valid());
    }

    #[test]
    fn by_child_pos_after_merge() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let f = eg.register_op1("f", int, int);
        let x_op = eg.register_op0("x", int);
        let y_op = eg.register_op0("y", int);

        let x = eg.add(x_op, &[]);
        let y = eg.add(y_op, &[]);
        let fx = eg.add(f, &[x]);
        let _fy = eg.add(f, &[y]);
        eg.merge(x, y);
        eg.rebuild();

        let idx = IndexStore::build(&eg);
        let repr = eg.class_repr(x);

        // Both fx and fy should appear under the canonical repr at pos 0
        let parents = &idx.by_child_pos[&(repr, 0)];
        // After merge, fx and fy are congruent — same node. So 1 entry.
        assert!(parents.data.contains(&eg.find_const(fx)));
    }

    #[test]
    fn by_contains_variadic() {
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

        let idx = IndexStore::build(&eg);

        // x is contained in both pxy and pxz
        let contains_x = &idx.by_contains[&x];
        assert_eq!(contains_x.len(), 2);
        assert!(contains_x.data.contains(&pxy));
        assert!(contains_x.data.contains(&pxz));

        // y is contained only in pxy
        let contains_y = &idx.by_contains[&y];
        assert_eq!(contains_y.len(), 1);
    }
}
