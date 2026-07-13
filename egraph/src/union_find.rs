// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent union-find with optional proof tracking.

use crate::containers::IndexLike;
use crate::containers::Tagged;
use crate::containers::dense_id::DenseId;
use crate::containers::{self, ShrinkPolicy, VecToken};
use std::collections::HashSet;

/// Reusable scratch buffers for proof extraction. Allocate once, reuse across queries.
pub struct ProofBuf<T: DenseId> {
    pub steps: Vec<(T, T, Justification<T>)>,
    path_a: Vec<T>,
    path_b: Vec<T>,
    seen: HashSet<usize>,
    rev: Vec<(T, T, Justification<T>)>,
    // explain_deep scratch
    pub(crate) children_a: Vec<T>,
    pub(crate) children_b: Vec<T>,
    pub(crate) group_a: Vec<T>,
    pub(crate) group_b: Vec<T>,
}

impl<T: DenseId> Default for ProofBuf<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: DenseId> ProofBuf<T> {
    pub fn new() -> Self {
        Self {
            steps: Vec::new(),
            path_a: Vec::new(),
            path_b: Vec::new(),
            seen: HashSet::new(),
            rev: Vec::new(),
            children_a: Vec::new(),
            children_b: Vec::new(),
            group_a: Vec::new(),
            group_b: Vec::new(),
        }
    }
    pub fn clear(&mut self) {
        self.steps.clear();
    }
}

/// Why two e-nodes were unified.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Justification<G: Copy> {
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
    /// AC completion: inter-reduction collapsed a rule's monomial to a smaller normal form,
    /// merging it with the materialized reduct. (Kapur Algo 1 step 4.)
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
}

impl<G: Copy + Clone + core::fmt::Debug + PartialEq + Eq> Tagged for Justification<G> {
    type Repr = (bool, Justification<G>);

    fn into_repr(self) -> Self::Repr {
        (false, self)
    }
    fn from_repr(stored: &Self::Repr) -> Self {
        stored.1
    }
    fn tag(stored: &Self::Repr) -> bool {
        stored.0
    }
    fn set_tag(stored: &mut Self::Repr) {
        stored.0 = true;
    }
    fn clear_tag(stored: &mut Self::Repr) {
        stored.0 = false;
    }
}

/// Semi-persistent union-find. All vectors use VecI (inline capture).
pub struct UnionFind<T: DenseId, const TRACK: bool = true, const PROOFS: bool = false> {
    parent_fast: containers::VecI<T, T::Index, TRACK>,
    // Rank is an upper bound on tree height. It only increments when two
    // equal-rank trees merge, so max rank = ⌊log₂(n)⌋. Even with 2^63
    // elements the rank cannot exceed 63; u8 (max 255) is more than enough.
    rank: containers::VecI<u8, T::Index, TRACK>,
    // Only allocated when PROOFS=true
    parent_proof: Option<containers::VecI<T, T::Index, TRACK>>,
    justification: Option<containers::VecI<Justification<T>, T::Index, TRACK>>,
}

impl<T: DenseId, const TRACK: bool, const PROOFS: bool> UnionFind<T, TRACK, PROOFS> {
    pub fn new() -> Self {
        Self {
            parent_fast: containers::VecI::new(),
            rank: containers::VecI::new(),
            parent_proof: if PROOFS {
                Some(containers::VecI::new())
            } else {
                None
            },
            justification: if PROOFS {
                Some(containers::VecI::new())
            } else {
                None
            },
        }
    }

    pub fn len(&self) -> T::Index {
        self.parent_fast.len()
    }

    pub fn is_empty(&self) -> bool {
        self.parent_fast.is_empty()
    }

    pub fn make_set(&mut self, id: T) {
        assert!(
            id.to_usize() == self.parent_fast.len().as_usize(),
            "UnionFind::make_set: id must be sequential"
        );
        self.parent_fast.push(id);
        self.rank.push(0);
        if let Some(pp) = &mut self.parent_proof {
            pp.push(id);
        }
        if let Some(j) = &mut self.justification {
            j.push(Justification::<T>::Filler);
        }
    }

    pub fn find(&mut self, x: T) -> T {
        let mut root = x;
        loop {
            let p = self.parent_fast.get(root);
            if p == root {
                break;
            }
            root = p;
        }
        let mut cur = x;
        while cur != root {
            let p = self.parent_fast.get(cur);
            self.parent_fast.set(cur, root);
            cur = p;
        }
        root
    }

    pub fn find_const(&self, x: T) -> T {
        let mut cur = x;
        loop {
            let p = self.parent_fast.get(cur);
            if p == cur {
                return cur;
            }
            cur = p;
        }
    }

    /// Union without justification. Only available when `PROOFS=false`.
    pub fn union(&mut self, a: T, b: T) -> Option<(T, T)> {
        assert!(
            !PROOFS,
            "union() called on a PROOFS=true UnionFind; use union_justified() instead"
        );
        self.union_inner(a, b, None, None)
    }

    /// Union with justification. Only meaningful when PROOFS=true.
    pub fn union_justified(&mut self, a: T, b: T, just: Justification<T>) -> Option<(T, T)> {
        self.union_inner(a, b, Some(just), None)
    }

    /// Union with an explicit survivor preference: `prefer_a == true` forces `find(a)`'s root
    /// to be the survivor, `false` forces `find(b)`'s. This overrides the union-by-rank choice
    /// so a caller can keep (say) the class with the larger parent use-list as the
    /// representative, minimizing the recanonicalization work that follows a merge. Sound: the
    /// classes and the proof forest are unaffected by which root is chosen; only the
    /// representative id and tree shape change. The rank is still maintained as a valid height
    /// upper bound (see `union_inner`), so `find` stays correct, but forcing against rank gives
    /// up union-by-rank's height optimality (ranks can climb faster), so `find` may be slower;
    /// path compression still applies.
    pub fn union_directed(&mut self, a: T, b: T, prefer_a: bool) -> Option<(T, T)> {
        assert!(
            !PROOFS,
            "union_directed() called on a PROOFS=true UnionFind; use union_justified_directed()"
        );
        self.union_inner(a, b, None, Some(prefer_a))
    }

    /// Justified counterpart of [`union_directed`].
    pub fn union_justified_directed(
        &mut self,
        a: T,
        b: T,
        just: Justification<T>,
        prefer_a: bool,
    ) -> Option<(T, T)> {
        self.union_inner(a, b, Some(just), Some(prefer_a))
    }

    fn union_inner(
        &mut self,
        a: T,
        b: T,
        just: Option<Justification<T>>,
        prefer_a: Option<bool>,
    ) -> Option<(T, T)> {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return None;
        }
        let rank_a = self.rank.get(ra);
        let rank_b = self.rank.get(rb);
        let (survivor, absorbed) = match prefer_a {
            // Default: union by rank (attach the shorter tree under the taller).
            None => {
                if rank_a >= rank_b {
                    (ra, rb)
                } else {
                    (rb, ra)
                }
            }
            // Forced survivor (e.g. larger use-list); may go against rank.
            Some(true) => (ra, rb),
            Some(false) => (rb, ra),
        };
        self.parent_fast.set(absorbed, survivor);
        // Keep `rank[survivor]` a valid upper bound on the merged tree's height. With
        // union-by-rank this only fires on a tie (rank_survivor == rank_absorbed); with a
        // forced survivor it also fires when the survivor was the shorter tree, so the
        // absorbed subtree (height ≤ rank_absorbed) hanging under it needs rank_absorbed + 1.
        let rank_surv = self.rank.get(survivor);
        let rank_abs = self.rank.get(absorbed);
        if rank_surv <= rank_abs {
            self.rank.set(survivor, rank_abs + 1);
        }
        // Proof tree: link the original nodes, not representatives.
        // This keeps the full chain: a—b is recorded directly.
        // We re-root b's proof tree so b points to a.
        if let (Some(pp), Some(j)) = (&mut self.parent_proof, &mut self.justification) {
            // Make b's proof-parent point to a with the given justification.
            // If b was already a proof-root (pp[b]==b), this just sets it.
            // If b had a parent, we need to reverse the path from b to its proof-root
            // so that b becomes the child of a.
            Self::reroot_proof(pp, j, b);
            pp.set(b, a);
            if let Some(just) = just {
                j.set(b, just);
            }
        }
        Some((survivor, absorbed))
    }

    /// Reverse the parent_proof path from `x` to its root, making `x` the new root.
    fn reroot_proof(
        pp: &mut containers::VecI<T, T::Index, TRACK>,
        j: &mut containers::VecI<Justification<T>, T::Index, TRACK>,
        x: T,
    ) {
        let mut path = vec![x];
        let mut cur = x;
        loop {
            let p = pp.get(cur);
            if p == cur {
                break;
            }
            path.push(p);
            cur = p;
        }
        // path = [x, ..., root]. Reverse the edges.
        for i in (0..path.len() - 1).rev() {
            let child = path[i + 1];
            let parent = path[i];
            pp.set(child, parent);
            j.set(child, j.get(parent));
        }
        // x is now the root
        pp.set(x, x);
    }

    /// Explain why `a ≡ b` by walking the proof tree.
    /// Appends steps to `buf.steps`. Returns false if not equivalent or `PROOFS=false`.
    pub fn explain(&self, a: T, b: T, buf: &mut ProofBuf<T>) -> bool {
        if !PROOFS {
            return false;
        }
        if self.find_const(a) != self.find_const(b) {
            return false;
        }
        let pp = self.parent_proof.as_ref().unwrap();
        let j = self.justification.as_ref().unwrap();

        // Walk a → root into path_a
        buf.path_a.clear();
        Self::walk_to_root(pp, a, &mut buf.path_a);

        // Walk b → root into path_b
        buf.path_b.clear();
        Self::walk_to_root(pp, b, &mut buf.path_b);

        // Find LCA
        buf.seen.clear();
        for id in &buf.path_a {
            buf.seen.insert(id.as_usize());
        }
        let mut lca = self.find_const(a);
        for &node in &buf.path_b {
            if buf.seen.contains(&node.as_usize()) {
                lca = node;
                break;
            }
        }

        // a → lca
        let mut cur = a;
        while cur != lca {
            let parent = pp.get(cur);
            let just = j.get(cur);
            buf.steps.push((cur, parent, just));
            cur = parent;
        }
        // lca → b (collect reversed into rev, then extend steps)
        let rev_start = buf.rev.len();
        cur = b;
        while cur != lca {
            let parent = pp.get(cur);
            let just = j.get(cur);
            buf.rev.push((parent, cur, just));
            cur = parent;
        }
        buf.rev[rev_start..].reverse();
        buf.steps.extend_from_slice(&buf.rev[rev_start..]);
        buf.rev.truncate(rev_start);
        true
    }

    fn walk_to_root(pp: &containers::VecI<T, T::Index, TRACK>, x: T, path: &mut Vec<T>) {
        path.push(x);
        let mut cur = x;
        loop {
            let p = pp.get(cur);
            if p == cur {
                break;
            }
            path.push(p);
            cur = p;
        }
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> UnionFindToken {
        assert!(TRACK, "mark() called on untracked UnionFind");
        UnionFindToken {
            parent_fast: self.parent_fast.mark(shrink),
            rank: self.rank.mark(shrink),
            parent_proof: self.parent_proof.as_mut().map(|v| v.mark(shrink)),
            justification: self.justification.as_mut().map(|v| v.mark(shrink)),
        }
    }

    pub fn restore(&mut self, token: UnionFindToken) {
        self.parent_fast.restore(token.parent_fast);
        self.rank.restore(token.rank);
        if let (Some(pp), Some(tok)) = (&mut self.parent_proof, token.parent_proof) {
            pp.restore(tok);
        }
        if let (Some(j), Some(tok)) = (&mut self.justification, token.justification) {
            j.restore(tok);
        }
    }
}

impl<T: DenseId, const TRACK: bool, const PROOFS: bool> Default for UnionFind<T, TRACK, PROOFS> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct UnionFindToken {
    parent_fast: VecToken,
    rank: VecToken,
    parent_proof: Option<VecToken>,
    justification: Option<VecToken>,
}

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
