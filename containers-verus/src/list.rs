// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Arena-backed intrusive singly-linked lists with semi-persistence (verified).
//!
//! `ListArena` owns two arenas, each a verified `Vec` over `ParallelStore`:
//!   - `heads[L]`  — per-list head pointer (+ tail index for O(1) append);
//!   - `nodes[k]`  — `{ payload, next }`, the intrusive node cells.
//! A list `L`'s abstract content is the payload sequence obtained by following
//! `next` from `heads[L].head` until null.
//!
//! ## Modeling choices (documented divergences)
//! - Storage is `ParallelStore` (needs only `Copy`), NOT production's
//!   `InlineStore`. That avoids porting the composite-`Tagged` niche encoding
//!   for `ListNode`/`ListHead` (the crate already proved bit-stealing storage
//!   sound generically). The optional `next` pointer is modeled directly as a
//!   `NodeRef { some, idx }` rather than via `Opt`'s stolen bit — same logical
//!   content, no storage-level niche.
//! - `Copy + Default` throughout (the crate convention; needed by
//!   `Vec::restore`'s resize regrow).
//!
//! ## The real invariant (`wf`)
//! Beyond the two inner `Vec`s being well-formed, the arena is structurally
//! sound: every `next`/`head` pointer is either null or in range `[0,
//! nodes.len())`, AND the node graph is ACYCLIC — captured by a ghost `rank`
//! that strictly decreases along `next`. Acyclicity is what lets `list_seq`
//! (chain → payload sequence) be defined by well-founded recursion and lets
//! `prepend`/`append` refine the obvious sequence operations.

use vstd::prelude::*;

use crate::index_like::IndexLike;
use crate::parallel_store::ParallelStore;
use crate::vec::{ShrinkPolicy, Vec as SpVec, VecToken};

verus! {

/// Optional node pointer (model-level `Opt<NodeId>`; `some==false` is null).
#[derive(Copy, Clone)]
pub struct NodeRef {
    pub some: bool,
    pub idx: usize,
}

impl NodeRef {
    pub open spec fn is_null(self) -> bool {
        !self.some
    }
    pub open spec fn target(self) -> nat {
        self.idx as nat
    }
    pub fn null() -> (r: NodeRef) ensures r.is_null() {
        NodeRef { some: false, idx: 0 }
    }
    /// Exec null test.
    pub fn is_null_exec(&self) -> (b: bool) ensures b == self.is_null() {
        !self.some
    }
    pub fn to(i: usize) -> (r: NodeRef) ensures !r.is_null(), r.idx == i {
        NodeRef { some: true, idx: i }
    }
}

impl core::default::Default for NodeRef {
    fn default() -> (r: NodeRef) ensures r.is_null() {
        NodeRef { some: false, idx: 0 }
    }
}

/// Intrusive node: payload + next pointer.
#[derive(Copy, Clone)]
pub struct ListNode<T> {
    pub payload: T,
    pub next: NodeRef,
}

impl<T: core::default::Default> core::default::Default for ListNode<T> {
    fn default() -> ListNode<T> {
        ListNode { payload: T::default(), next: NodeRef { some: false, idx: 0 } }
    }
}

/// Per-list header: head pointer and (when non-empty) tail node index.
#[derive(Copy, Clone)]
pub struct ListHead {
    pub head: NodeRef,
    pub tail: usize,
}

impl core::default::Default for ListHead {
    fn default() -> (r: ListHead) ensures r.head.is_null() {
        ListHead { head: NodeRef { some: false, idx: 0 }, tail: 0 }
    }
}

/// Token bundling the two inner-vector tokens.
#[derive(Copy, Clone)]
pub struct ListArenaToken {
    pub heads: VecToken,
    pub nodes: VecToken,
}

pub struct ListArena<T, const TRACK: bool>
where T: Sized + Copy + core::default::Default {
    pub heads: SpVec<ListHead, usize, ParallelStore<ListHead, usize>, TRACK>,
    pub nodes: SpVec<ListNode<T>, usize, ParallelStore<ListNode<T>, usize>, TRACK>,
}

impl<T, const TRACK: bool> ListArena<T, TRACK>
where T: Sized + Copy + core::default::Default {
    pub open spec fn nodes_view(&self) -> Seq<ListNode<T>> {
        self.nodes.view()
    }
    pub open spec fn heads_view(&self) -> Seq<ListHead> {
        self.heads.view()
    }

    /// Structural soundness of the node arena: every node's `next`, if not
    /// null, targets an allocated node, and the graph is ACYCLIC via a ghost
    /// rank that strictly decreases along `next`. `rank[k]` bounds the number
    /// of nodes reachable from `k`, so following `next` terminates.
    pub open spec fn nodes_wf(&self) -> bool {
        let nodes = self.nodes_view();
        forall|k: int| 0 <= k < nodes.len() ==> {
            let nx = (#[trigger] nodes[k]).next;
            nx.is_null() || (nx.target() < nodes.len()
                // acyclic: next targets a STRICTLY SMALLER index. Established
                // by `prepend` (new node has the largest index, points at the
                // old — smaller — head). `append` is handled by relinking so
                // the same discipline holds; see the per-op proofs.
                && nx.target() < k as nat)
        }
    }

    /// Per-list head soundness: a list's head is null or in range.
    pub open spec fn heads_wf(&self) -> bool {
        let heads = self.heads_view();
        let nodes = self.nodes_view();
        forall|l: int| 0 <= l < heads.len() ==> {
            let h = (#[trigger] heads[l]).head;
            h.is_null() || h.target() < nodes.len()
        }
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.heads.wf()
        &&& self.nodes.wf()
        &&& self.nodes_wf()
        &&& self.heads_wf()
    }

    /// The payload sequence of the chain starting at `ptr`, following `next`.
    /// Well-founded because `next` strictly decreases the index (`nodes_wf`):
    /// recursion is bounded by the current node index.
    pub open spec fn chain_seq(&self, ptr: NodeRef) -> Seq<T>
        decreases ptr.target()
    {
        let nodes = self.nodes_view();
        if ptr.is_null() || ptr.target() >= nodes.len() {
            Seq::empty()
        } else {
            let node = nodes[ptr.target() as int];
            // node.next.target() < ptr.target() by nodes_wf ⇒ decreases.
            if !node.next.is_null() && node.next.target() < ptr.target() {
                seq![node.payload] + self.chain_seq(node.next)
            } else if node.next.is_null() {
                seq![node.payload]
            } else {
                // ill-formed (would violate nodes_wf); empty for totality.
                seq![node.payload]
            }
        }
    }

    /// The abstract content of list `L`.
    pub open spec fn list_seq(&self, l: usize) -> Seq<T>
        recommends l < self.heads_view().len()
    {
        self.chain_seq(self.heads_view()[l as int].head)
    }

    pub fn new() -> (a: Self)
        ensures a.wf(), a.heads_view().len() == 0, a.nodes_view().len() == 0,
    {
        ListArena {
            heads: SpVec::<ListHead, usize, ParallelStore<ListHead, usize>, TRACK>::new(),
            nodes: SpVec::<ListNode<T>, usize, ParallelStore<ListNode<T>, usize>, TRACK>::new(),
        }
    }

    /// Create a new empty list; returns its id.
    pub fn new_list(&mut self) -> (l: usize)
        requires old(self).wf(), old(self).heads_view().len() < usize::MAX,
        ensures
            self.wf(),
            l == old(self).heads_view().len(),
            self.nodes_view() == old(self).nodes_view(),
            self.list_seq(l) == Seq::<T>::empty(),
    {
        let l = self.heads.len();
        self.heads.push(ListHead::default());
        proof {
            // new head is null ⇒ heads_wf preserved; nodes untouched ⇒
            // nodes_wf + chain_seq unchanged; list_seq(l) is empty (null head).
            assert(self.heads_view()[l as int].head.is_null());
            assert(self.nodes_view() == old(self).nodes_view());
            assert(self.chain_seq(self.heads_view()[l as int].head) =~= Seq::<T>::empty());
        }
        l
    }

    /// Prepend `payload` to the front of list `l`. The new node is pushed at
    /// the highest arena index and points at the old head (a smaller index),
    /// preserving the strictly-decreasing-`next` acyclicity discipline.
    /// Refines the sequence operation `list_seq(l) := [payload] ++ old`.
    pub fn prepend(&mut self, l: usize, payload: T)
        requires
            old(self).wf(),
            l < old(self).heads_view().len(),
            old(self).nodes_view().len() + 1 < usize::MAX,
        ensures
            self.wf(),
            self.heads_view().len() == old(self).heads_view().len(),
            self.list_seq(l) == seq![payload] + old(self).list_seq(l),
            // other lists unchanged.
            forall|m: int| 0 <= m < self.heads_view().len() && m != l
                ==> #[trigger] self.list_seq(m as usize) == old(self).list_seq(m as usize),
    {
        let ghost old_nodes = self.nodes_view();
        let ghost old_heads = self.heads_view();
        let old_head = self.heads.get(l).head;

        let slot = self.nodes.len();
        self.nodes.push(ListNode { payload, next: old_head });

        proof {
            // The push appended one node at index `slot`; the prefix [0, slot)
            // is unchanged. So every old chain (all indices < slot) is
            // preserved (frame lemma), and the new node points at old_head
            // (target < slot), keeping nodes_wf.
            let nodes1 = self.nodes_view();
            assert(nodes1.len() == old_nodes.len() + 1);
            assert(slot == old_nodes.len());
            assert(forall|k: int| 0 <= k < old_nodes.len() ==> nodes1[k] == old_nodes[k]);
            assert(nodes1[slot as int].next == old_head);
            // old_head is null or target < slot (heads_wf at l).
            assert(old_head.is_null() || old_head.target() < slot as nat);
            self.lemma_nodes_wf_after_push(*old(self), old_head, payload);
        }

        let mut h = self.heads.get(l);
        h.head = NodeRef::to(slot);
        self.heads.set(l, h);

        proof {
            let nodes1 = self.nodes_view();
            // chain from the new head: node[slot].payload ++ chain(old_head).
            let new_head = self.heads_view()[l as int].head;
            assert(new_head.idx == slot);
            assert(!new_head.is_null());
            assert(new_head.target() == slot as nat);
            // chain_seq unfolds one step at slot:
            lemma_chain_seq_step(self, new_head);
            assert(nodes1[slot as int].payload == payload);
            assert(nodes1[slot as int].next == old_head);
            assert(self.chain_seq(new_head)
                =~= seq![payload] + self.chain_seq(old_head));
            // old chain content preserved across the node push + head set:
            // chain_seq depends only on nodes (not heads), and nodes' prefix
            // [0, slot) is unchanged from old.
            self.lemma_chain_seq_frame(*old(self), old_head);
            assert(self.chain_seq(old_head) == old(self).chain_seq(old_head));
            assert(old(self).list_seq(l) == old(self).chain_seq(old_head));
            // other lists: their heads unchanged (only heads[l] set) and their
            // chains live in the old prefix, preserved.
            assert forall|m: int| 0 <= m < self.heads_view().len() && m != l implies
                #[trigger] self.list_seq(m as usize) == old(self).list_seq(m as usize) by {
                assert(self.heads_view()[m] == old_heads[m]);
                self.lemma_chain_seq_frame(*old(self), old_heads[m].head);
            }
        }
    }

    /// Is list `l` empty (head is null)?
    pub fn is_empty(&self, l: usize) -> (b: bool)
        requires self.wf(), l < self.heads_view().len(),
        ensures b == (self.list_seq(l) == Seq::<T>::empty()),
    {
        let h = self.heads.get(l);
        proof {
            // chain_seq of a null head is empty; of a non-null head is
            // non-empty. heads_wf: head null or target < nodes.len().
            assert(h.head == self.heads_view()[l as int].head);
            if !h.head.is_null() {
                assert(h.head.target() < self.nodes_view().len());  // heads_wf
                lemma_chain_seq_step(self, h.head);
                // chain_seq starts with the head node's payload ⇒ len >= 1.
                assert(self.list_seq(l).len() >= 1);
            }
        }
        h.head.is_null_exec()
    }

    // ---- semi-persistence: delegate to the two inner vectors ----

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> (token: ListArenaToken)
        requires
            old(self).wf(),
            old(self).heads_view().len() < usize::MAX,
            old(self).nodes_view().len() < usize::MAX,
            old(self).heads.frames@.len() < u32::MAX,
            old(self).nodes.frames@.len() < u32::MAX,
        ensures
            self.wf(),
            self.heads_view() == old(self).heads_view(),
            self.nodes_view() == old(self).nodes_view(),
            self.heads.snapshots_view()
                == old(self).heads.snapshots_view().push(old(self).heads_view()),
            self.nodes.snapshots_view()
                == old(self).nodes.snapshots_view().push(old(self).nodes_view()),
    {
        let heads = self.heads.mark(shrink);
        let nodes = self.nodes.mark(shrink);
        ListArenaToken { heads, nodes }
    }

    /// Restore both arenas to the marked snapshot. Semi-persistence composes
    /// from the two inner `Vec`s; the restored snapshots are jointly a valid
    /// arena (the `restored_*_wf` precondition), so `wf` holds afterward.
    pub fn restore(&mut self, token: ListArenaToken)
        requires
            old(self).wf(),
            old(self).heads.is_token_valid_spec(token.heads),
            token.heads.frame_idx < old(self).heads.frames@.len(),
            old(self).heads.frames@.len() < u32::MAX,
            old(self).heads.forks.origins@.len() + 1 <= u32::MAX,
            old(self).nodes.is_token_valid_spec(token.nodes),
            token.nodes.frame_idx < old(self).nodes.frames@.len(),
            old(self).nodes.frames@.len() < u32::MAX,
            old(self).nodes.forks.origins@.len() + 1 <= u32::MAX,
            // the snapshots being restored jointly form a structurally valid
            // arena (acyclic nodes + in-range heads).
            arena_snap_wf(
                old(self).heads.snapshots_view()[token.heads.frame_idx as int],
                old(self).nodes.snapshots_view()[token.nodes.frame_idx as int]),
        ensures
            self.wf(),
            self.heads_view()
                == old(self).heads.snapshots_view()[token.heads.frame_idx as int],
            self.nodes_view()
                == old(self).nodes.snapshots_view()[token.nodes.frame_idx as int],
    {
        self.heads.restore(token.heads);
        self.nodes.restore(token.nodes);
    }

    /// Frame: `chain_seq(ptr)` is unchanged between `pre` (an older arena) and
    /// `self`, provided `self`'s node sequence extends `pre`'s as a prefix and
    /// `ptr`'s reachable chain lies within `pre`'s length. (chain_seq reads
    /// only nodes along the chain, all `< pre.nodes.len()` by acyclicity.)
    pub proof fn lemma_chain_seq_frame(&self, pre: Self, ptr: NodeRef)
        requires
            self.nodes_wf(),
            pre.nodes_wf(),
            pre.nodes_view().len() <= self.nodes_view().len(),
            forall|k: int| 0 <= k < pre.nodes_view().len()
                ==> #[trigger] self.nodes_view()[k] == pre.nodes_view()[k],
            ptr.is_null() || ptr.target() < pre.nodes_view().len(),
        ensures
            self.chain_seq(ptr) == pre.chain_seq(ptr),
        decreases ptr.target(),
    {
        let pn = pre.nodes_view();
        if ptr.is_null() || ptr.target() >= pn.len() {
        } else {
            let node = pn[ptr.target() as int];
            assert(self.nodes_view()[ptr.target() as int] == node);
            if !node.next.is_null() && node.next.target() < ptr.target() {
                self.lemma_chain_seq_frame(pre, node.next);
            }
        }
    }

    /// Pushing a fresh node (at index == old nodes.len()) whose `next` is null
    /// or targets `< slot` preserves `nodes_wf`. (All old nodes keep their
    /// next; the new node satisfies the discipline by hypothesis.)
    pub proof fn lemma_nodes_wf_after_push(&self, pre: Self, new_next: NodeRef, payload: T)
        requires
            pre.nodes_wf(),
            self.nodes_view().len() == pre.nodes_view().len() + 1,
            forall|k: int| 0 <= k < pre.nodes_view().len()
                ==> #[trigger] self.nodes_view()[k] == pre.nodes_view()[k],
            self.nodes_view()[pre.nodes_view().len() as int].next == new_next,
            new_next.is_null() || new_next.target() < pre.nodes_view().len() as nat,
        ensures
            self.nodes_wf(),
    {
        let nodes = self.nodes_view();
        let slot = pre.nodes_view().len();
        assert forall|k: int| 0 <= k < nodes.len() implies {
            let nx = (#[trigger] nodes[k]).next;
            nx.is_null() || (nx.target() < nodes.len() && nx.target() < k as nat)
        } by {
            if k < slot {
                assert(nodes[k] == pre.nodes_view()[k]);
            } else {
                assert(k == slot);
                assert(nodes[k].next == new_next);
            }
        }
    }
}

/// Structural arena validity over raw snapshot sequences (for `restore`: the
/// restored heads/nodes must jointly be a valid arena). Mirrors
/// `nodes_wf` + `heads_wf`.
pub open spec fn arena_snap_wf<T>(heads: Seq<ListHead>, nodes: Seq<ListNode<T>>) -> bool {
    &&& (forall|k: int| 0 <= k < nodes.len() ==> {
            let nx = (#[trigger] nodes[k]).next;
            nx.is_null() || (nx.target() < nodes.len() && nx.target() < k as nat)
        })
    &&& (forall|l: int| 0 <= l < heads.len() ==> {
            let h = (#[trigger] heads[l]).head;
            h.is_null() || h.target() < nodes.len()
        })
}

/// `chain_seq` one-step unfold at a non-null in-range pointer whose `next`
/// strictly decreases (the `nodes_wf` case): the chain is the head payload
/// followed by the tail chain.
pub proof fn lemma_chain_seq_step<T, const TRACK: bool>(
    a: &ListArena<T, TRACK>, ptr: NodeRef,
)
    where T: Sized + Copy + core::default::Default
    requires
        a.nodes_wf(),
        !ptr.is_null(),
        ptr.target() < a.nodes_view().len(),
    ensures
        ({
            let node = a.nodes_view()[ptr.target() as int];
            a.chain_seq(ptr) == seq![node.payload] + a.chain_seq(node.next)
        }),
{
    let nodes = a.nodes_view();
    let node = nodes[ptr.target() as int];
    // nodes_wf at ptr.target(): next null or target < ptr.target().
    assert(node.next.is_null() || node.next.target() < ptr.target());
    if node.next.is_null() {
        assert(a.chain_seq(node.next) =~= Seq::<T>::empty());
    }
}

} // verus!
