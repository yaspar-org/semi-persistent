// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Result-term pool (§4.4): hash-consed arena of anti-unifier terms.
//!
//! Terms are `(TermOp, children)` where children are spans into a shared pool.
//! `Variants` nodes have two children (left, right projections). Size counts 1
//! per ordinary node and 0 for each `Variants` node (its children are counted).

use crate::canon::{MSetCanon, VarCanon};
use crate::config::EGraphConfig;
use crate::containers::{AppendOnlyVec, DenseId, Map, MapToken, ShrinkPolicy, VecToken};
use crate::literal::LitVal;

use super::AuClassId;
use super::egraph_api::AuSnapshot;

crate::containers::define_id31! {
    /// Index of a term in the hash-consed term pool.
    pub struct TermId / StoredTermId, "t";
}

/// The operator of a term node.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TermOp<O: DenseId, V: DenseId> {
    /// An e-graph operator (from the original e-graph).
    EGraph(O),
    /// A literal value.
    Literal(O, V),
    /// A `Variants(left, right)` node: where left and right differ.
    Variants,
}

/// Hash-consed term pool. Structurally equal terms get the same `TermId`.
/// All fields are semi-persistent (AppendOnlyVec/Map); mark/restore truncates.
pub struct TermPool<O: DenseId, V: DenseId> {
    ops: AppendOnlyVec<TermOp<O, V>>,
    child_spans: AppendOnlyVec<(u32, u32)>,
    child_pool: AppendOnlyVec<TermId>,
    sizes: AppendOnlyVec<u32>,
    vmasses: AppendOnlyVec<u32>,
    by_structure: Map<(TermOp<O, V>, Vec<TermId>), TermId>,
}

/// Token for restoring a `TermPool` to a previous state.
#[derive(Clone, Copy, Debug)]
pub struct TermPoolToken {
    ops: VecToken,
    child_spans: VecToken,
    child_pool: VecToken,
    sizes: VecToken,
    vmasses: VecToken,
    by_structure: MapToken,
}

impl<O: DenseId + core::hash::Hash, V: DenseId + core::hash::Hash> TermPool<O, V> {
    pub fn new() -> Self {
        TermPool {
            ops: AppendOnlyVec::new(),
            child_spans: AppendOnlyVec::new(),
            child_pool: AppendOnlyVec::new(),
            sizes: AppendOnlyVec::new(),
            vmasses: AppendOnlyVec::new(),
            by_structure: Map::new(),
        }
    }

    /// Number of interned terms.
    pub fn len(&self) -> usize {
        self.ops.len()
    }

    pub fn is_empty(&self) -> bool {
        self.ops.is_empty()
    }

    /// Intern a term. Returns the existing id if structurally equal term exists.
    pub fn intern(&mut self, op: TermOp<O, V>, children: &[TermId]) -> TermId {
        let key = (op.clone(), children.to_vec());
        if let Some(log_idx) = self.by_structure.id_of(&key) {
            return *self.by_structure.get(log_idx);
        }

        let id = TermId::from_usize(self.ops.len());
        let start = self.child_pool.len() as u32;
        for &c in children {
            self.child_pool.push(c);
        }
        let len = children.len() as u32;

        let child_size_sum: u32 = children
            .iter()
            .map(|&c| *self.sizes.get(c.to_usize()))
            .sum();
        let (size, vmass) = match &op {
            TermOp::Variants => (child_size_sum, child_size_sum),
            _ => {
                let vm = children
                    .iter()
                    .map(|&c| *self.vmasses.get(c.to_usize()))
                    .sum::<u32>();
                (1 + child_size_sum, vm)
            }
        };

        self.ops.push(op);
        self.child_spans.push((start, len));
        self.sizes.push(size);
        self.vmasses.push(vmass);
        self.by_structure.insert(key, id);
        id
    }

    /// Intern the result term of one action.
    ///
    /// `commutative` MUST be true exactly for operators whose canonical node kind is
    /// commutative (SPair, MSet, Set): their children are sorted into canonical
    /// structural order. For ordered operators (Plain*, Seq) it MUST be false: the
    /// pair order of the action is positional semantics and is preserved verbatim.
    pub fn intern_action_result(
        &mut self,
        op: TermOp<O, V>,
        children_with_counts: &[(TermId, u32)],
        commutative: bool,
    ) -> TermId {
        // Expand counts into repeated children.
        let mut expanded: Vec<TermId> = Vec::new();
        for &(child, count) in children_with_counts {
            for _ in 0..count {
                expanded.push(child);
            }
        }
        if commutative {
            // Canonical structural order: allocation-independent, so the same
            // semantic result interns identically regardless of construction order.
            expanded.sort_by(|&a, &b| self.structural_cmp(a, b));
        }
        self.intern(op, &expanded)
    }

    /// Total structural order on terms, independent of allocation order:
    /// operator variant rank, then operator/value ids, then arity, then children
    /// lexicographically. Equal ids are structurally equal (hash-consing), so this
    /// returns `Equal` only for identical ids.
    pub fn structural_cmp(&self, a: TermId, b: TermId) -> core::cmp::Ordering {
        use core::cmp::Ordering;
        if a == b {
            return Ordering::Equal;
        }
        fn rank<O: DenseId, V: DenseId>(op: &TermOp<O, V>) -> u8 {
            match op {
                TermOp::EGraph(_) => 0,
                TermOp::Literal(_, _) => 1,
                TermOp::Variants => 2,
            }
        }
        let (oa, ob) = (self.op(a), self.op(b));
        let ord = rank(oa).cmp(&rank(ob));
        if ord != Ordering::Equal {
            return ord;
        }
        let ord = match (oa, ob) {
            (TermOp::EGraph(x), TermOp::EGraph(y)) => x.to_usize().cmp(&y.to_usize()),
            (TermOp::Literal(x, v), TermOp::Literal(y, w)) => x
                .to_usize()
                .cmp(&y.to_usize())
                .then(v.to_usize().cmp(&w.to_usize())),
            _ => Ordering::Equal,
        };
        if ord != Ordering::Equal {
            return ord;
        }
        let (ca, cb) = (self.children(a), self.children(b));
        let ord = ca.len().cmp(&cb.len());
        if ord != Ordering::Equal {
            return ord;
        }
        for (&x, &y) in ca.iter().zip(cb.iter()) {
            let ord = self.structural_cmp(x, y);
            if ord != Ordering::Equal {
                return ord;
            }
        }
        Ordering::Equal
    }

    /// Get the size of a term.
    #[inline]
    pub fn size(&self, id: TermId) -> u32 {
        *self.sizes.get(id.to_usize())
    }

    /// Get the variant mass of a term: concrete nodes under `Variants` nodes.
    /// `size - variant_mass` is the backbone (shared structure) size.
    #[inline]
    pub fn variant_mass(&self, id: TermId) -> u32 {
        *self.vmasses.get(id.to_usize())
    }

    /// The lexicographic quality key `(size, variant_mass)`. Lower is better:
    /// primary objective is minimum size; at equal size the term with less
    /// variant mass has more backbone (more factored structure) and wins.
    #[inline]
    pub fn quality(&self, id: TermId) -> (u32, u32) {
        (
            *self.sizes.get(id.to_usize()),
            *self.vmasses.get(id.to_usize()),
        )
    }

    /// Get the operator of a term.
    #[inline]
    pub fn op(&self, id: TermId) -> &TermOp<O, V> {
        self.ops.get(id.to_usize())
    }

    /// Get the children of a term.
    #[inline]
    pub fn children(&self, id: TermId) -> &[TermId] {
        let &(start, len) = self.child_spans.get(id.to_usize());
        if len == 0 {
            return &[];
        }
        unsafe {
            let ptr = self.child_pool.get(start as usize) as *const TermId;
            std::slice::from_raw_parts(ptr, len as usize)
        }
    }

    pub fn mark(&mut self) -> TermPoolToken {
        TermPoolToken {
            ops: self.ops.mark(ShrinkPolicy::Never),
            child_spans: self.child_spans.mark(ShrinkPolicy::Never),
            child_pool: self.child_pool.mark(ShrinkPolicy::Never),
            sizes: self.sizes.mark(ShrinkPolicy::Never),
            vmasses: self.vmasses.mark(ShrinkPolicy::Never),
            by_structure: self.by_structure.mark(ShrinkPolicy::Never),
        }
    }

    pub fn restore(&mut self, token: TermPoolToken) {
        self.by_structure.restore(token.by_structure);
        self.vmasses.restore(token.vmasses);
        self.sizes.restore(token.sizes);
        self.child_pool.restore(token.child_pool);
        self.child_spans.restore(token.child_spans);
        self.ops.restore(token.ops);
    }

    /// Project one side of the anti-unifier: replace every `Variants` node —
    /// at any depth — by its left (side 0) or right (side 1) child, recursively.
    /// The result contains no `Variants` node (§1: variant projection must land
    /// in the source class). New nodes may be interned for rebuilt spines.
    pub fn project(&mut self, id: TermId, side: usize) -> TermId {
        debug_assert!(side < 2);
        match self.op(id).clone() {
            TermOp::Variants => {
                let chosen = self.children(id)[side];
                // The chosen arm may itself contain nested Variants.
                self.project(chosen, side)
            }
            op => {
                let children = self.children(id).to_vec();
                let mut changed = false;
                let mut new_children = Vec::with_capacity(children.len());
                for c in children {
                    let pc = self.project(c, side);
                    changed |= pc != c;
                    new_children.push(pc);
                }
                if changed {
                    self.intern(op, &new_children)
                } else {
                    id
                }
            }
        }
    }

    /// Does this term contain any `Variants` node (at any depth)?
    pub fn has_variants(&self, id: TermId) -> bool {
        if matches!(self.op(id), TermOp::Variants) {
            return true;
        }
        self.children(id).iter().any(|&c| self.has_variants(c))
    }
}

impl<O: DenseId + core::hash::Hash, V: DenseId + core::hash::Hash> Default for TermPool<O, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: DenseId, V: DenseId> core::fmt::Debug for TermPool<O, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("TermPool")
            .field("len", &self.ops.len())
            .finish()
    }
}

/// Build the syntactic seed of two best-terms (§A.3): recursively zip, emit
/// `Variants` at every mismatch.
pub fn syntactic_seed<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &mut TermPool<Cfg::O, Cfg::V>,
    l: AuClassId,
    r: AuClassId,
) -> TermId
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    if l == r {
        return build_best_term(snap, pool, l);
    }
    let l_term = build_best_term(snap, pool, l);
    let r_term = build_best_term(snap, pool, r);
    seed_zip(pool, l_term, r_term)
}

/// Build the best (smallest) concrete term for a class, interned in the pool.
pub fn build_best_term<Cfg: EGraphConfig, L: LitVal, const T: bool, const P: bool>(
    snap: &AuSnapshot<Cfg, L, T, P>,
    pool: &mut TermPool<Cfg::O, Cfg::V>,
    class: AuClassId,
) -> TermId
where
    MSetCanon: VarCanon<Cfg::G, Cfg::C>,
{
    let eg = snap.egraph();
    let best_id = snap.best_node(class);
    let op = eg.node_op(best_id);

    // Check if it's a literal.
    if let Some(val_id) = eg.get_lit_val_id(best_id) {
        return pool.intern(TermOp::Literal(op, val_id), &[]);
    }

    // Collect children (respecting multiplicities for AC nodes).
    let mut children: Vec<TermId> = Vec::new();
    eg.for_each_child(best_id, |child, mult| {
        let child_class = snap.class_of(child).unwrap();
        let child_term = build_best_term(snap, pool, child_class);
        for _ in 0..mult {
            children.push(child_term);
        }
    });

    pool.intern(TermOp::EGraph(op), &children)
}

/// Zip two terms: if same op and same arity, recurse positionally; otherwise Variants.
fn seed_zip<O: DenseId + core::hash::Hash, V: DenseId + core::hash::Hash>(
    pool: &mut TermPool<O, V>,
    l_term: TermId,
    r_term: TermId,
) -> TermId {
    if l_term == r_term {
        return l_term;
    }

    let l_op = pool.op(l_term).clone();
    let r_op = pool.op(r_term).clone();

    if l_op != r_op {
        return pool.intern(TermOp::Variants, &[l_term, r_term]);
    }

    let l_children = pool.children(l_term).to_vec();
    let r_children = pool.children(r_term).to_vec();

    if l_children.len() != r_children.len() {
        return pool.intern(TermOp::Variants, &[l_term, r_term]);
    }

    // Same op and arity: zip children.
    let mut new_children: Vec<TermId> = Vec::with_capacity(l_children.len());
    for i in 0..l_children.len() {
        new_children.push(seed_zip(pool, l_children[i], r_children[i]));
    }

    pool.intern(l_op, &new_children)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraph31;
    use crate::id::OpId;
    use crate::literal::NiraLitVal;

    #[test]
    fn term_pool_dedup() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let op = OpId::from_usize(0);

        let leaf = pool.intern(TermOp::EGraph(op), &[]);
        let leaf2 = pool.intern(TermOp::EGraph(op), &[]);
        assert_eq!(leaf, leaf2);
        assert_eq!(pool.size(leaf), 1);
    }

    #[test]
    fn term_size_variants_zero() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let op = OpId::from_usize(0);

        let left = pool.intern(TermOp::EGraph(op), &[]);
        let right = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
        let variants = pool.intern(TermOp::Variants, &[left, right]);

        // Variants costs 0, children cost 1 each.
        assert_eq!(pool.size(variants), 2);
    }

    #[test]
    fn syntactic_seed_identical() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let a = eg.add(a_op, &[]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let ac = snap.class_of(a).unwrap();

        let mut pool = TermPool::new();
        let seed = syntactic_seed(&snap, &mut pool, ac, ac);
        assert_eq!(pool.size(seed), 1);
        assert_eq!(*pool.op(seed), TermOp::EGraph(a_op));
    }

    #[test]
    fn syntactic_seed_mismatch() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let ac = snap.class_of(a).unwrap();
        let bc = snap.class_of(b).unwrap();

        let mut pool = TermPool::new();
        let seed = syntactic_seed(&snap, &mut pool, ac, bc);
        // Variants(a, b) -> size 2 (1+1, Variants itself costs 0).
        assert_eq!(pool.size(seed), 2);
        assert_eq!(*pool.op(seed), TermOp::Variants);
    }

    /// P1 regression: projection must descend below ordinary operators.
    /// project(f(a, Variants(b,c)), 0) = f(a, b); side 1 = f(a, c).
    #[test]
    fn projection_is_deep() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let f = OpId::from_usize(0);
        let a = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
        let b = pool.intern(TermOp::EGraph(OpId::from_usize(2)), &[]);
        let c = pool.intern(TermOp::EGraph(OpId::from_usize(3)), &[]);
        let v = pool.intern(TermOp::Variants, &[b, c]);
        let root = pool.intern(TermOp::EGraph(f), &[a, v]);

        let left = pool.project(root, 0);
        let right = pool.project(root, 1);

        assert!(!pool.has_variants(left));
        assert!(!pool.has_variants(right));
        assert_eq!(pool.children(left), &[a, b]);
        assert_eq!(pool.children(right), &[a, c]);

        // Nested Variants inside a chosen arm are resolved too.
        let v2 = pool.intern(TermOp::Variants, &[v, a]);
        let root2 = pool.intern(TermOp::EGraph(f), &[v2, a]);
        let l2 = pool.project(root2, 0);
        assert!(!pool.has_variants(l2));
        assert_eq!(pool.children(l2), &[b, a]);
    }

    /// P0 regression: ordered operators preserve positional child order even
    /// when the positional order disagrees with TermId order.
    #[test]
    fn ordered_children_not_sorted() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let f = OpId::from_usize(0);
        // Allocate `b` FIRST so its TermId sorts before the Variants node.
        let b = pool.intern(TermOp::EGraph(OpId::from_usize(2)), &[]);
        let a = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
        let c = pool.intern(TermOp::EGraph(OpId::from_usize(3)), &[]);
        let v = pool.intern(TermOp::Variants, &[a, c]);

        // Ordered: f(Variants(a,c), b) must keep the Variants first.
        let ordered = pool.intern_action_result(TermOp::EGraph(f), &[(v, 1), (b, 1)], false);
        assert_eq!(pool.children(ordered), &[v, b]);

        // Commutative: children are sorted structurally (EGraph ops rank before
        // Variants), independent of allocation order.
        let comm = pool.intern_action_result(TermOp::EGraph(f), &[(v, 1), (b, 1)], true);
        assert_eq!(pool.children(comm), &[b, v]);
    }

    /// Variant mass: backbone nodes are excluded; everything under Variants counts.
    #[test]
    fn variant_mass_arithmetic() {
        let mut pool = TermPool::<OpId, crate::id::ENodeId>::new();
        let f = OpId::from_usize(0);
        let x = pool.intern(TermOp::EGraph(OpId::from_usize(1)), &[]);
        let y = pool.intern(TermOp::EGraph(OpId::from_usize(2)), &[]);
        let fy = pool.intern(TermOp::EGraph(f), &[y]);

        // Variants(x, f(y)): size 3, all variant mass.
        let bare = pool.intern(TermOp::Variants, &[x, fy]);
        assert_eq!(pool.quality(bare), (3, 3));

        // f(Variants(x, y)): size 3, variant mass 2 — one backbone node.
        let v = pool.intern(TermOp::Variants, &[x, y]);
        let factored = pool.intern(TermOp::EGraph(f), &[v]);
        assert_eq!(pool.quality(factored), (3, 2));

        // The factored form is strictly better in the lexicographic order.
        assert!(pool.quality(factored) < pool.quality(bare));
    }

    #[test]
    fn syntactic_seed_partial_overlap() {
        let mut eg = EGraph31::<NiraLitVal, false, false>::new();
        let int = eg.intern_sort("Int");
        let a_op = eg.register_op0("a", int);
        let b_op = eg.register_op0("b", int);
        let c_op = eg.register_op0("c", int);
        let f_op = eg.register_op2("f", int, int, int);

        let a = eg.add(a_op, &[]);
        let b = eg.add(b_op, &[]);
        let c = eg.add(c_op, &[]);
        let fab = eg.add(f_op, &[a, b]);
        let fac = eg.add(f_op, &[a, c]);
        eg.rebuild();

        let snap = AuSnapshot::new(&eg).unwrap();
        let lc = snap.class_of(fab).unwrap();
        let rc = snap.class_of(fac).unwrap();

        let mut pool = TermPool::new();
        let seed = syntactic_seed(&snap, &mut pool, lc, rc);
        // f(a, Variants(b, c)) -> 1(f) + 1(a) + 0(V) + 1(b) + 1(c) = 4
        assert_eq!(pool.size(seed), 4);
        assert_eq!(*pool.op(seed), TermOp::EGraph(f_op));
    }
}
