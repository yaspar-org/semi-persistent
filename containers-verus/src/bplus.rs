// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent B+tree set (verification in progress — milestone 1).
//!
//! Port of production's `BPlusTreeSet` ([`containers/src/bplus.rs`]). The full
//! design and proof plan live in
//! [`doc/future/bplus-tree-design.md`](../../doc/future/bplus-tree-design.md);
//! this module builds it up milestone by milestone, leaving the tree verifying
//! at each step.
//!
//! **Milestone 1 (this commit): model + `wf` + `new`/`is_empty`/`len`.**
//! A node arena (`Vec<BNode>` over the verified `ParallelStore`) plus a ghost
//! header (`root`, key count). The well-formedness invariant and abstract model
//! are introduced in the minimal form the empty tree needs; later milestones
//! (`contains`, `insert`, split propagation) extend both. The whole structure
//! is semi-persistent for free via the inner `Vec`'s `mark`/`restore`.
//!
//! Simplifications vs. production, all documented in the design doc:
//!   - one fixed node geometry (leaf/internal capacities are spec constants)
//!     rather than the generic `NodeLayout`; the proof is about tree structure,
//!     not byte packing.
//!   - `usize` keys and arena indices; `NIL == usize::MAX`.
//!   - INSERT-ONLY (production has no `remove`).

use vstd::prelude::*;

use crate::parallel_store::ParallelStore;
use crate::vec::{ShrinkPolicy, Vec as SpVec, VecToken};

verus! {

/// Max keys in a leaf node. (Internal-node capacities arrive with the split
/// milestones; milestone 1 only allocates the empty root leaf.)
pub spec const LEAF_CAP: nat = 14;

/// A B+tree node. `is_leaf` distinguishes the two readings of `keys`:
///   - leaf: `keys[0..count]` are the sorted keys; `link` is the next leaf
///     (arena index, `NIL` at the rightmost);
///   - internal: `keys[0..count]` are separators (children arrive later).
/// Milestone 1 stores a small fixed key buffer as a `Seq`-backed model; the
/// production packed `[Word; N]` layout is a later, non-observable refinement.
#[derive(Copy)]
pub struct BNode {
    pub is_leaf: bool,
    pub count: usize,
    /// Key slots. Only `keys[0..count]` are meaningful.
    pub keys: [usize; 14],
    /// Leaf: next-leaf arena index (`NIL` if last). Internal: unused for now.
    pub link: usize,
}

impl Clone for BNode {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

impl core::default::Default for BNode {
    fn default() -> (r: BNode)
        ensures r.is_leaf, r.count == 0,
    {
        BNode { is_leaf: true, count: 0, keys: [0; 14], link: usize::MAX }
    }
}

impl BNode {
    /// A fresh empty leaf, with the fields needed by `wf`/`model` exposed.
    pub fn empty_leaf() -> (r: BNode)
        ensures r.is_leaf, r.count == 0,
    {
        BNode { is_leaf: true, count: 0, keys: [0; 14], link: usize::MAX }
    }
}

/// Token for mark/restore (delegates to the inner vector's token).
#[derive(Copy, Clone)]
pub struct BPlusToken {
    pub nodes: VecToken,
}

pub struct BPlusTreeSet<const TRACK: bool> {
    pub nodes: SpVec<BNode, usize, ParallelStore<BNode, usize>, TRACK>,
    /// Arena index of the root node.
    pub root: usize,
    /// Number of keys in the set (cached; equals `model().len()`).
    pub nkeys: usize,
}

impl<const TRACK: bool> BPlusTreeSet<TRACK> {
    pub open spec fn nodes_view(&self) -> Seq<BNode> {
        self.nodes.view()
    }

    pub open spec fn n_nodes(&self) -> nat {
        self.nodes.view().len()
    }

    /// NIL sentinel for arena indices.
    pub open spec fn nil_spec() -> nat {
        usize::MAX as nat
    }

    /// The keys of a single leaf node, as a sequence (`keys[0..count]`).
    pub open spec fn leaf_keys(node: BNode) -> Seq<usize> {
        Seq::new(node.count as nat, |i: int| node.keys[i])
    }

    /// **Milestone-1 well-formedness.** The arena is a valid `Vec`; the root is
    /// an in-range leaf; and (the only structural fact the empty tree needs)
    /// every node's `count` is within `LEAF_CAP` and its keys are sorted.
    ///
    /// Later milestones extend this to the full seven-clause invariant of the
    /// design doc (cross-node ordering, balance/height, leaf-link consistency,
    /// internal children). It is deliberately stated so those are monotone
    /// additions, not rewrites.
    pub open spec fn wf(&self) -> bool {
        &&& self.nodes.wf()
        &&& self.root < self.n_nodes()
        &&& self.nodes_view()[self.root as int].is_leaf
        &&& (forall|k: int| 0 <= k < self.n_nodes() ==>
                (#[trigger] self.nodes_view()[k]).count <= LEAF_CAP)
        &&& (forall|k: int| 0 <= k < self.n_nodes() ==>
                sorted_strict(Self::leaf_keys(#[trigger] self.nodes_view()[k])))
    }

    /// The abstract model: the sorted key set, as a sequence. **Milestone 1**:
    /// the tree is a single root leaf, so the model is that leaf's keys. (Once
    /// internal nodes and the leaf-link arrive, this becomes the in-order leaf
    /// concatenation; the single-leaf tree is the base case of that.)
    pub open spec fn model(&self) -> Seq<usize> {
        Self::leaf_keys(self.nodes_view()[self.root as int])
    }

    pub fn new() -> (t: Self)
        ensures t.wf(), t.model() == Seq::<usize>::empty(),
    {
        let mut nodes = SpVec::<BNode, usize, ParallelStore<BNode, usize>, TRACK>::new();
        let root = nodes.len();
        let leaf = BNode::empty_leaf();
        nodes.push(leaf);
        let t = BPlusTreeSet { nodes, root, nkeys: 0 };
        proof {
            assert(t.root == 0);
            assert(t.nodes_view()[0] == leaf);          // push appended `leaf` at index 0
            assert(t.nodes_view()[0].is_leaf);
            assert(t.nodes_view()[0].count == 0);
            // empty leaf: leaf_keys is empty, vacuously sorted, count <= cap.
            assert(Self::leaf_keys(t.nodes_view()[0]) =~= Seq::<usize>::empty());
            assert forall|k: int| 0 <= k < t.n_nodes() implies
                sorted_strict(Self::leaf_keys(#[trigger] t.nodes_view()[k])) by {
                assert(k == 0);
                assert(Self::leaf_keys(t.nodes_view()[k]) =~= Seq::<usize>::empty());
            }
            assert(t.model() =~= Seq::<usize>::empty());
        }
        t
    }

    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b == (self.model().len() == 0),
    {
        let r = self.nodes.get(self.root);
        proof {
            assert(r == self.nodes_view()[self.root as int]);
            assert(self.model().len() == r.count as nat);
        }
        r.count == 0
    }

    pub fn len(&self) -> (n: usize)
        requires self.wf(),
        ensures n == self.model().len(),
    {
        let r = self.nodes.get(self.root);
        proof { assert(self.model().len() == r.count as nat); }
        r.count
    }
}

/// A `usize` sequence is strictly increasing (the per-node key-order invariant).
pub open spec fn sorted_strict(s: Seq<usize>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> (#[trigger] s[i]) < (#[trigger] s[j])
}

} // verus!
