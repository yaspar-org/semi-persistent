// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Arena-backed intrusive singly-linked lists with semi-persistence (verified).
//!
//! `ListArena` owns two arenas, each a verified `Vec` over `ParallelStore`:
//!   - `heads[L]`  — per-list head pointer (+ tail index for O(1) append);
//!   - `nodes[k]`  — `{ payload, next }`, the intrusive node cells.
//! This is the *parent use-list* of the e-graph (production: `list.rs`'s
//! `ListArena`), supporting O(1) `prepend`, O(1) `append` (via the cached
//! tail), and O(1) `splice` (link dst's tail to src's head).
//!
//! ## The invariant: a ghost model list (NOT index ordering)
//!
//! Each list `l` carries a **ghost `Seq<usize>`** — the indices of its nodes in
//! list order — kept in `model@[l]`. The abstract content `list_seq(l)` is the
//! payload read off that finite sequence, so it is defined without any
//! recursion over `next` and needs no termination measure. The physical
//! pointers are a *cache* of the model, tied to it by `wf`:
//!   - `heads[l].head` is null iff `model[l]` is empty, else points at
//!     `model[l][0]`; `heads[l].tail` is `model[l].last()`;
//!   - for each list position `p`, `nodes[model[l][p]].next` points at
//!     `model[l][p+1]` (null at the end).
//! The only constraint on a `next`/`head` target is that it is **in range**
//! `[0, nodes.len())` — there is deliberately NO "next points to a smaller
//! index" discipline (that earlier crutch made the chain-walk terminate by a
//! decreasing index, but it is false for `append`/`splice`, which link a node
//! forward to a freshly-pushed — larger — index). A global **disjointness**
//! invariant (each node index occurs in at most one list, at most once) makes
//! the models partition a subset of `[0, nodes.len())`; from it, every list is
//! at most as long as the arena, and relinking one list frames the others.
//!
//! ## Modeling choices (documented divergences)
//! - Storage is `ParallelStore` (needs only `Copy`), NOT production's
//!   `InlineStore`; the optional `next` pointer is a `NodeRef { some, idx }`
//!   rather than a stolen niche bit — same logical content.
//! - `Copy + Default` throughout (the crate convention; `Vec::restore` regrow).

use vstd::prelude::*;

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
#[derive(Copy)]
pub struct ListNode<T> {
    pub payload: T,
    pub next: NodeRef,
}

// Hand-written `Clone` (a plain copy); the autoderived `Clone` on a generic
// struct emits a "clone is not a copy" warning under Verus otherwise.
impl<T: Copy> Clone for ListNode<T> {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
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
    /// Ghost model: `model@[l]` is the in-order node indices of list `l`.
    pub model: Ghost<Seq<Seq<usize>>>,
}

impl<T, const TRACK: bool> ListArena<T, TRACK>
where T: Sized + Copy + core::default::Default {
    pub open spec fn nodes_view(&self) -> Seq<ListNode<T>> {
        self.nodes.view()
    }
    pub open spec fn heads_view(&self) -> Seq<ListHead> {
        self.heads.view()
    }
    pub open spec fn model_view(&self) -> Seq<Seq<usize>> {
        self.model@
    }

    /// In-range: every node index named by any list is allocated. (The ONLY
    /// constraint on a list-membership index — no ordering.)
    pub open spec fn model_in_range(&self) -> bool {
        let model = self.model@;
        let nodes = self.nodes_view();
        forall|l: int, p: int|
            0 <= l < model.len() && 0 <= p < (#[trigger] model[l]).len()
                ==> #[trigger] model[l][p] < nodes.len()
    }

    /// Disjointness: a node index occurs in at most one list at one position.
    /// Makes the models partition a subset of `[0, nodes.len())`, so each list
    /// is at most as long as the arena and relinking one list frames the rest.
    pub open spec fn model_disjoint(&self) -> bool {
        let model = self.model@;
        forall|l1: int, p1: int, l2: int, p2: int|
            0 <= l1 < model.len() && 0 <= p1 < model[l1].len()
                && 0 <= l2 < model.len() && 0 <= p2 < model[l2].len()
                && (#[trigger] model[l1][p1]) == (#[trigger] model[l2][p2])
                    ==> l1 == l2 && p1 == p2
    }

    /// Cache consistency: `head`/`tail`/`next` match the model's endpoints.
    pub open spec fn cache_ok(&self) -> bool {
        let model = self.model@;
        let heads = self.heads_view();
        let nodes = self.nodes_view();
        &&& (forall|l: int| 0 <= l < model.len() ==> {
                let h = (#[trigger] heads[l]).head;
                if model[l].len() == 0 {
                    h.is_null()
                } else {
                    !h.is_null() && h.target() == model[l][0]
                }
            })
        &&& (forall|l: int| 0 <= l < model.len() && (#[trigger] model[l]).len() > 0
                ==> heads[l].tail == model[l][model[l].len() - 1])
        &&& (forall|l: int, p: int|
                0 <= l < model.len() && 0 <= p < model[l].len() ==> {
                    let nx = nodes[#[trigger] model[l][p] as int].next;
                    if p == model[l].len() - 1 {
                        nx.is_null()
                    } else {
                        !nx.is_null() && nx.target() == model[l][p + 1]
                    }
                })
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.heads.wf()
        &&& self.nodes.wf()
        &&& self.model@.len() == self.heads_view().len()
        &&& self.model_in_range()
        &&& self.model_disjoint()
        &&& self.cache_ok()
    }

    /// The abstract content of list `l`: payloads read off the model, in order.
    /// No recursion over `next` — defined directly on the finite model seq.
    pub open spec fn list_seq(&self, l: int) -> Seq<T> {
        let model = self.model@;
        let nodes = self.nodes_view();
        Seq::new(model[l].len(), |p: int| nodes[model[l][p] as int].payload)
    }

    pub fn new() -> (a: Self)
        ensures a.wf(), a.heads_view().len() == 0, a.nodes_view().len() == 0,
            a.model_view().len() == 0,
    {
        ListArena {
            heads: SpVec::<ListHead, usize, ParallelStore<ListHead, usize>, TRACK>::new(),
            nodes: SpVec::<ListNode<T>, usize, ParallelStore<ListNode<T>, usize>, TRACK>::new(),
            model: Ghost(Seq::empty()),
        }
    }

    /// Create a new empty list; returns its id.
    pub fn new_list(&mut self) -> (l: usize)
        requires old(self).wf(), old(self).heads_view().len() < usize::MAX,
        ensures
            self.wf(),
            l == old(self).heads_view().len(),
            self.nodes_view() == old(self).nodes_view(),
            self.model_view() == old(self).model_view().push(Seq::<usize>::empty()),
            self.list_seq(l as int) == Seq::<T>::empty(),
            // existing lists unchanged.
            forall|m: int| 0 <= m < old(self).model_view().len()
                ==> #[trigger] self.list_seq(m) == old(self).list_seq(m),
    {
        let l = self.heads.len();
        self.heads.push(ListHead::default());
        self.model = Ghost(self.model@.push(Seq::empty()));
        proof {
            let model = self.model@;
            assert(model[l as int].len() == 0);
            assert(self.heads_view()[l as int].head.is_null());
            assert(self.list_seq(l as int) =~= Seq::<T>::empty());
            // existing lists: model + nodes unchanged, head[m] unchanged.
            assert forall|m: int| 0 <= m < old(self).model_view().len() implies
                #[trigger] self.list_seq(m) == old(self).list_seq(m) by {
                assert(model[m] == old(self).model_view()[m]);
                assert(self.list_seq(m) =~= old(self).list_seq(m));
            }
            // disjointness preserved: the new list is empty (no indices).
            assert(self.model_disjoint());
        }
        l
    }

    /// Prepend `payload` to the front of list `l`. Pushes a fresh node (at the
    /// arena's end — a *larger* index than anything in the list, which the old
    /// index-ordering crutch forbade and is now simply fine), links it to the
    /// old head, and makes it the new model[l][0].
    pub fn prepend(&mut self, l: usize, payload: T)
        requires
            old(self).wf(),
            (l as int) < old(self).model_view().len(),
            old(self).nodes_view().len() + 1 < usize::MAX,
        ensures
            self.wf(),
            self.model_view().len() == old(self).model_view().len(),
            self.list_seq(l as int) == seq![payload] + old(self).list_seq(l as int),
            forall|m: int| 0 <= m < self.model_view().len() && m != l as int
                ==> #[trigger] self.list_seq(m) == old(self).list_seq(m),
    {
        let ghost old_nodes = self.nodes_view();
        let ghost old_model = self.model@;
        let old_head = self.heads.get(l).head;
        let was_empty = old_head.is_null_exec();

        let slot = self.nodes.len();
        self.nodes.push(ListNode { payload, next: old_head });

        // model[l] := [slot] ++ model[l]
        self.model = Ghost(self.model@.update(l as int, seq![slot] + self.model@[l as int]));

        let mut h = self.heads.get(l);
        h.head = NodeRef::to(slot);
        if was_empty {
            h.tail = slot;
        }
        self.heads.set(l, h);

        proof {
            let model = self.model@;
            let nodes = self.nodes_view();
            let heads = self.heads_view();
            assert(nodes.len() == old_nodes.len() + 1);
            assert(slot == old_nodes.len());
            // node prefix [0, slot) unchanged by the push.
            assert(forall|k: int| 0 <= k < old_nodes.len() ==> nodes[k] == old_nodes[k]);
            // model[l] = [slot] ++ old_model[l]; other lists unchanged.
            assert(model[l as int] =~= seq![slot] + old_model[l as int]);
            assert(forall|m: int| 0 <= m < model.len() && m != l as int ==> model[m] == old_model[m]);
            // old in_range gives: every OLD index < old_nodes.len() == slot.
            assert(forall|l2: int, p: int|
                0 <= l2 < old_model.len() && 0 <= p < old_model[l2].len()
                    ==> old_model[l2][p] < slot);

            // --- in_range
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies
                #[trigger] model[l2][p] < nodes.len() by {
                if l2 == l as int && p == 0 {
                } else if l2 == l as int {
                    assert(model[l2][p] == old_model[l as int][p - 1]);
                } else {
                    assert(model[l2][p] == old_model[l2][p]);
                }
            }

            // --- disjoint: every entry except (l,0) maps to a distinct old entry
            // (< slot); (l,0) holds the fresh slot, present nowhere old.
            assert forall|l1: int, p1: int, l2: int, p2: int|
                0 <= l1 < model.len() && 0 <= p1 < model[l1].len()
                    && 0 <= l2 < model.len() && 0 <= p2 < model[l2].len()
                    && (#[trigger] model[l1][p1]) == (#[trigger] model[l2][p2])
                implies l1 == l2 && p1 == p2 by {
                let fresh1 = l1 == l as int && p1 == 0;
                let fresh2 = l2 == l as int && p2 == 0;
                if fresh1 && fresh2 {
                } else if fresh1 {
                    // model[l1][p1]==slot but model[l2][p2] is an old index < slot.
                    assert(model[l2][p2] < slot);
                } else if fresh2 {
                    assert(model[l1][p1] < slot);
                } else {
                    // both old: source positions, then old disjointness.
                    let s1 = if l1 == l as int { p1 - 1 } else { p1 };
                    let s2 = if l2 == l as int { p2 - 1 } else { p2 };
                    assert(model[l1][p1] == old_model[l1][s1]);
                    assert(model[l2][p2] == old_model[l2][s2]);
                    assert(l1 == l2 && s1 == s2);  // old_disjoint
                }
            }

            // --- cache_ok nexts
            assert(heads[l as int].head.target() == slot);
            assert(nodes[slot as int].next == old_head);
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies {
                    let nx = nodes[#[trigger] model[l2][p] as int].next;
                    if p == model[l2].len() - 1 { nx.is_null() }
                    else { !nx.is_null() && nx.target() == model[l2][p + 1] }
                } by {
                if l2 == l as int && p == 0 {
                    // node[slot].next == old_head == old model[l][0] (or null if empty).
                    if old_model[l as int].len() == 0 {
                        assert(old_head.is_null());
                    } else {
                        assert(!old_head.is_null());
                        assert(old_head.target() == old_model[l as int][0]);  // old cache_ok head
                        assert(model[l as int][1] == old_model[l as int][0]);
                    }
                } else if l2 == l as int {
                    // shifted old node; its next is old's, model shifted by 1.
                    assert(model[l2][p] == old_model[l as int][p - 1]);
                    assert(nodes[model[l2][p] as int] == old_nodes[model[l2][p] as int]);
                } else {
                    assert(model[l2][p] == old_model[l2][p]);
                    assert(nodes[model[l2][p] as int] == old_nodes[model[l2][p] as int]);
                }
            }

            // --- cache_ok heads/tails
            assert forall|l2: int| 0 <= l2 < model.len() implies {
                let hh = (#[trigger] heads[l2]).head;
                if model[l2].len() == 0 { hh.is_null() }
                else { !hh.is_null() && hh.target() == model[l2][0] }
            } by {
                if l2 != l as int { assert(heads[l2] == old(self).heads_view()[l2]); }
            }
            assert forall|l2: int| #![auto] 0 <= l2 < model.len() && model[l2].len() > 0 implies
                heads[l2].tail == model[l2][model[l2].len() - 1] by {
                if l2 != l as int { assert(heads[l2] == old(self).heads_view()[l2]); }
                else if !was_empty {
                    assert(model[l as int][model[l as int].len() - 1]
                        == old_model[l as int][old_model[l as int].len() - 1]);
                }
            }

            // --- list_seq(l): payload prepended.
            assert(self.list_seq(l as int) =~= seq![payload] + old(self).list_seq(l as int)) by {
                let post_seq = self.list_seq(l as int);
                let pre_seq = old(self).list_seq(l as int);
                assert(post_seq.len() == pre_seq.len() + 1);
                assert(post_seq[0] == payload);
                assert forall|p: int| 1 <= p < post_seq.len() implies
                    post_seq[p] == pre_seq[p - 1] by {
                    assert(model[l as int][p] == old_model[l as int][p - 1]);
                    assert(nodes[model[l as int][p] as int]
                        == old_nodes[old_model[l as int][p - 1] as int]);
                }
            }
            // --- list_seq(others): unchanged.
            assert forall|m: int| 0 <= m < model.len() && m != l as int implies
                #[trigger] self.list_seq(m) == old(self).list_seq(m) by {
                assert(model[m] == old_model[m]);
                assert(self.list_seq(m) =~= old(self).list_seq(m)) by {
                    assert forall|p: int| #![auto] 0 <= p < model[m].len() implies
                        nodes[model[m][p] as int].payload == old_nodes[old_model[m][p] as int].payload by {
                        assert(model[m][p] == old_model[m][p]);
                        assert(model[m][p] < slot);  // old index, unchanged node
                    }
                }
            }
        }
    }

    /// Append `payload` to the back of list `l` in O(1) via the cached tail.
    /// Pushes a fresh node (null next), then — if the list was non-empty —
    /// relinks the OLD TAIL node's `next` *forward* to the new (larger-index)
    /// node. This forward link is exactly what the old index-ordering crutch
    /// could not represent; the ghost model makes it routine.
    pub fn append(&mut self, l: usize, payload: T)
        requires
            old(self).wf(),
            (l as int) < old(self).model_view().len(),
            old(self).nodes_view().len() + 1 < usize::MAX,
        ensures
            self.wf(),
            self.model_view().len() == old(self).model_view().len(),
            self.list_seq(l as int) == old(self).list_seq(l as int).push(payload),
            forall|m: int| 0 <= m < self.model_view().len() && m != l as int
                ==> #[trigger] self.list_seq(m) == old(self).list_seq(m),
    {
        let ghost old_nodes = self.nodes_view();
        let ghost old_model = self.model@;
        let h0 = self.heads.get(l);
        let was_empty = h0.head.is_null_exec();

        let slot = self.nodes.len();
        self.nodes.push(ListNode { payload, next: NodeRef::null() });

        if !was_empty {
            // relink old tail node forward to slot.
            let old_tail = h0.tail;
            let mut tnode = self.nodes.get(old_tail);
            tnode.next = NodeRef::to(slot);
            self.nodes.set(old_tail, tnode);
        }

        // model[l] := model[l] ++ [slot]
        self.model = Ghost(self.model@.update(l as int, self.model@[l as int].push(slot)));

        let mut h = self.heads.get(l);
        if was_empty {
            h.head = NodeRef::to(slot);
        }
        h.tail = slot;
        self.heads.set(l, h);

        proof {
            let model = self.model@;
            let nodes = self.nodes_view();
            let heads = self.heads_view();
            let ghost old_tail = old_model[l as int].len() > 0;
            assert(slot == old_nodes.len());
            assert(model[l as int] =~= old_model[l as int].push(slot));
            assert(forall|m: int| 0 <= m < model.len() && m != l as int ==> model[m] == old_model[m]);
            assert(forall|l2: int, p: int|
                0 <= l2 < old_model.len() && 0 <= p < old_model[l2].len()
                    ==> old_model[l2][p] < slot);

            // --- in_range
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies
                #[trigger] model[l2][p] < nodes.len() by {
                if l2 == l as int && p == model[l as int].len() - 1 {
                } else if l2 == l as int {
                    assert(model[l2][p] == old_model[l as int][p]);
                } else {
                    assert(model[l2][p] == old_model[l2][p]);
                }
            }

            // --- disjoint: fresh slot only at (l, last); others map to old.
            assert forall|l1: int, p1: int, l2: int, p2: int|
                0 <= l1 < model.len() && 0 <= p1 < model[l1].len()
                    && 0 <= l2 < model.len() && 0 <= p2 < model[l2].len()
                    && (#[trigger] model[l1][p1]) == (#[trigger] model[l2][p2])
                implies l1 == l2 && p1 == p2 by {
                let last = model[l as int].len() - 1;
                let fresh1 = l1 == l as int && p1 == last;
                let fresh2 = l2 == l as int && p2 == last;
                if fresh1 && fresh2 {
                } else if fresh1 {
                    assert(model[l2][p2] < slot);
                } else if fresh2 {
                    assert(model[l1][p1] < slot);
                } else {
                    assert(model[l1][p1] == old_model[l1][p1]);
                    assert(model[l2][p2] == old_model[l2][p2]);
                }
            }

            // --- cache_ok nexts. The only mutated node-next is the old tail
            // (now -> slot) and the new node slot (null). All others unchanged.
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies {
                    let nx = nodes[#[trigger] model[l2][p] as int].next;
                    if p == model[l2].len() - 1 { nx.is_null() }
                    else { !nx.is_null() && nx.target() == model[l2][p + 1] }
                } by {
                if l2 == l as int {
                    let last = model[l as int].len() - 1;
                    if p == last {
                        // node slot: pushed with null next; not the relinked tail.
                        assert(model[l as int][p] == slot);
                        assert(nodes[slot as int].next.is_null());
                    } else if p == last - 1 {
                        // old tail position: relinked to slot == model[l][last].
                        assert(model[l as int][p] == old_model[l as int][p]);
                        assert(model[l as int][p] == h0.tail);  // old cache: tail == old last
                        assert(nodes[model[l as int][p] as int].next.target() == slot);
                        assert(model[l as int][p + 1] == slot);
                    } else {
                        // interior old node, untouched.
                        assert(model[l as int][p] == old_model[l as int][p]);
                        assert(model[l as int][p] != h0.tail);
                        assert(nodes[model[l as int][p] as int] == old_nodes[old_model[l as int][p] as int]);
                        assert(model[l as int][p + 1] == old_model[l as int][p + 1]);
                    }
                } else {
                    // other list: its nodes are disjoint from l's tail and slot.
                    assert(model[l2][p] == old_model[l2][p]);
                    assert(model[l2][p] != slot);
                    assert(was_empty || model[l2][p] != h0.tail);  // disjoint from l's tail
                    assert(nodes[model[l2][p] as int] == old_nodes[old_model[l2][p] as int]);
                }
            }

            // --- cache_ok heads/tails
            assert forall|l2: int| 0 <= l2 < model.len() implies {
                let hh = (#[trigger] heads[l2]).head;
                if model[l2].len() == 0 { hh.is_null() }
                else { !hh.is_null() && hh.target() == model[l2][0] }
            } by {
                if l2 != l as int { assert(heads[l2] == old(self).heads_view()[l2]); }
                else if was_empty {
                    assert(model[l as int][0] == slot);
                } else {
                    assert(model[l as int][0] == old_model[l as int][0]);
                }
            }
            assert forall|l2: int| #![auto] 0 <= l2 < model.len() && model[l2].len() > 0 implies
                heads[l2].tail == model[l2][model[l2].len() - 1] by {
                if l2 != l as int { assert(heads[l2] == old(self).heads_view()[l2]); }
            }

            // --- list_seq(l): payload appended.
            assert(self.list_seq(l as int) =~= old(self).list_seq(l as int).push(payload)) by {
                let post_seq = self.list_seq(l as int);
                let pre_seq = old(self).list_seq(l as int);
                assert(post_seq.len() == pre_seq.len() + 1);
                assert forall|p: int| 0 <= p < pre_seq.len() implies post_seq[p] == pre_seq[p] by {
                    assert(model[l as int][p] == old_model[l as int][p]);
                    assert(model[l as int][p] < slot);
                    // node may be the relinked tail, but only its `next` changed,
                    // not its payload.
                    assert(nodes[model[l as int][p] as int].payload
                        == old_nodes[old_model[l as int][p] as int].payload);
                }
                assert(post_seq[pre_seq.len() as int] == payload);
            }
            // --- list_seq(others): unchanged (their nodes' payloads untouched).
            assert forall|m: int| 0 <= m < model.len() && m != l as int implies
                #[trigger] self.list_seq(m) == old(self).list_seq(m) by {
                assert(model[m] == old_model[m]);
                assert(self.list_seq(m) =~= old(self).list_seq(m)) by {
                    assert forall|p: int| #![auto] 0 <= p < model[m].len() implies
                        nodes[model[m][p] as int].payload == old_nodes[old_model[m][p] as int].payload by {
                        assert(model[m][p] == old_model[m][p]);
                        assert(model[m][p] < slot);
                        assert(was_empty || model[m][p] != h0.tail);
                    }
                }
            }
        }
    }

    /// Is list `l` empty?
    pub fn is_empty(&self, l: usize) -> (b: bool)
        requires self.wf(), (l as int) < self.model_view().len(),
        ensures b == (self.list_seq(l as int) == Seq::<T>::empty()),
    {
        let h = self.heads.get(l);
        proof {
            // head null iff model[l] empty (cache_ok); list_seq empty iff model empty.
            assert(h.head == self.heads_view()[l as int].head);
            if self.model@[l as int].len() == 0 {
                assert(self.list_seq(l as int) =~= Seq::<T>::empty());
            } else {
                assert(self.list_seq(l as int).len() == self.model@[l as int].len());
            }
        }
        h.head.is_null_exec()
    }

    /// Splice `src` onto the back of `dst`: `dst` becomes `dst ++ src`, and
    /// `src` is cleared to empty. O(1): link `dst`'s tail node forward to
    /// `src`'s head (a single `next` mutation across arbitrary indices — the
    /// general case the old invariant could not model), then concatenate the
    /// models. Disjointness (the two lists share no node) is what makes the
    /// concatenation a valid list and lets `src` clear without dangling.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(400)]
    pub fn splice(&mut self, dst: usize, src: usize)
        requires
            old(self).wf(),
            (dst as int) < old(self).model_view().len(),
            (src as int) < old(self).model_view().len(),
            dst != src,
        ensures
            self.wf(),
            self.model_view().len() == old(self).model_view().len(),
            self.list_seq(dst as int)
                == old(self).list_seq(dst as int) + old(self).list_seq(src as int),
            self.list_seq(src as int) == Seq::<T>::empty(),
            forall|m: int| 0 <= m < self.model_view().len()
                && m != dst as int && m != src as int
                ==> #[trigger] self.list_seq(m) == old(self).list_seq(m),
    {
        let ghost old_nodes = self.nodes_view();
        let ghost old_model = self.model@;
        let hd = self.heads.get(dst);
        let hs = self.heads.get(src);
        let dst_empty = hd.head.is_null_exec();
        let src_empty = hs.head.is_null_exec();

        if !src_empty {
            if dst_empty {
                // dst takes over src's head/tail.
                let mut h = self.heads.get(dst);
                h.head = hs.head;
                h.tail = hs.tail;
                self.heads.set(dst, h);
            } else {
                // link dst's tail node forward to src's head.
                let dtail = hd.tail;
                let mut tnode = self.nodes.get(dtail);
                tnode.next = hs.head;
                self.nodes.set(dtail, tnode);
                let mut h = self.heads.get(dst);
                h.tail = hs.tail;
                self.heads.set(dst, h);
            }
        }
        // clear src.
        self.heads.set(src, ListHead::default());

        // model: dst := dst ++ src; src := [].
        self.model = Ghost(
            self.model@
                .update(dst as int, old_model[dst as int] + old_model[src as int])
                .update(src as int, Seq::empty()));

        proof {
            let model = self.model@;
            let nodes = self.nodes_view();
            let heads = self.heads_view();
            assert(nodes.len() == old_nodes.len());
            assert(model[dst as int] =~= old_model[dst as int] + old_model[src as int]);
            assert(model[src as int] =~= Seq::<usize>::empty());
            assert(forall|m: int| 0 <= m < model.len() && m != dst as int && m != src as int
                ==> model[m] == old_model[m]);

            // helper: position p of model[dst] sources to old dst (p < |dst|) or
            // old src (p - |dst|).
            let dlen = old_model[dst as int].len();

            // --- in_range: all indices are old indices (no node pushed).
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies
                #[trigger] model[l2][p] < nodes.len() by {
                if l2 == dst as int {
                    if p < dlen { assert(model[l2][p] == old_model[dst as int][p]); }
                    else { assert(model[l2][p] == old_model[src as int][p - dlen]); }
                } else {
                    assert(model[l2][p] == old_model[l2][p]);
                }
            }

            // --- disjoint: dst++src concatenates two OLD-disjoint lists; every
            // entry still maps to a distinct old (list,pos), and src is now empty.
            assert forall|l1: int, p1: int, l2: int, p2: int|
                0 <= l1 < model.len() && 0 <= p1 < model[l1].len()
                    && 0 <= l2 < model.len() && 0 <= p2 < model[l2].len()
                    && (#[trigger] model[l1][p1]) == (#[trigger] model[l2][p2])
                implies l1 == l2 && p1 == p2 by {
                // source-position maps into the OLD model (which was disjoint).
                let src1 = splice_src(old_model, dst as int, src as int, l1, p1);
                let src2 = splice_src(old_model, dst as int, src as int, l2, p2);
                assert(model[l1][p1] == old_model[src1.0][src1.1]);
                assert(model[l2][p2] == old_model[src2.0][src2.1]);
                // old disjointness ⇒ same old source; map back to (l,p).
                assert(src1.0 == src2.0 && src1.1 == src2.1);
            }

            // --- cache_ok nexts: only dst's old tail node was relinked
            // (its next -> src's head); every other node-next is unchanged.
            assert forall|l2: int, p: int|
                0 <= l2 < model.len() && 0 <= p < model[l2].len() implies {
                    let nx = nodes[#[trigger] model[l2][p] as int].next;
                    if p == model[l2].len() - 1 { nx.is_null() }
                    else { !nx.is_null() && nx.target() == model[l2][p + 1] }
                } by {
                splice_cache_node(*old(self), self, dst as int, src as int,
                    hd.tail, hs.head, dst_empty, src_empty, l2, p);
            }

            // --- cache_ok heads/tails
            assert forall|l2: int| 0 <= l2 < model.len() implies {
                let hh = (#[trigger] heads[l2]).head;
                if model[l2].len() == 0 { hh.is_null() }
                else { !hh.is_null() && hh.target() == model[l2][0] }
            } by {
                if l2 == src as int {
                } else if l2 == dst as int {
                    if old_model[dst as int].len() > 0 {
                        assert(model[dst as int][0] == old_model[dst as int][0]);
                    } else if old_model[src as int].len() > 0 {
                        assert(model[dst as int][0] == old_model[src as int][0]);
                    }
                } else {
                    assert(heads[l2] == old(self).heads_view()[l2]);
                }
            }
            assert forall|l2: int| #![auto] 0 <= l2 < model.len() && model[l2].len() > 0 implies
                heads[l2].tail == model[l2][model[l2].len() - 1] by {
                if l2 == dst as int {
                    if old_model[src as int].len() > 0 {
                        assert(model[dst as int][model[dst as int].len() - 1]
                            == old_model[src as int][old_model[src as int].len() - 1]);
                    } else {
                        assert(model[dst as int][model[dst as int].len() - 1]
                            == old_model[dst as int][old_model[dst as int].len() - 1]);
                    }
                } else if l2 != src as int {
                    assert(heads[l2] == old(self).heads_view()[l2]);
                }
            }

            // --- list_seq
            assert(self.list_seq(src as int) =~= Seq::<T>::empty());
            assert(self.list_seq(dst as int)
                =~= old(self).list_seq(dst as int) + old(self).list_seq(src as int)) by {
                let post = self.list_seq(dst as int);
                let pre_d = old(self).list_seq(dst as int);
                let pre_s = old(self).list_seq(src as int);
                assert(post.len() == pre_d.len() + pre_s.len());
                assert forall|p: int| #![auto] 0 <= p < post.len() implies
                    post[p] == (if p < pre_d.len() { pre_d[p] } else { pre_s[p - pre_d.len()] }) by {
                    if p < dlen {
                        assert(model[dst as int][p] == old_model[dst as int][p]);
                    } else {
                        assert(model[dst as int][p] == old_model[src as int][p - dlen]);
                    }
                }
            }
            assert forall|m: int| 0 <= m < model.len() && m != dst as int && m != src as int implies
                #[trigger] self.list_seq(m) == old(self).list_seq(m) by {
                assert(model[m] == old_model[m]);
                assert(self.list_seq(m) =~= old(self).list_seq(m)) by {
                    assert forall|p: int| #![auto] 0 <= p < model[m].len() implies
                        nodes[model[m][p] as int].payload == old_nodes[old_model[m][p] as int].payload by {
                        assert(model[m][p] == old_model[m][p]);
                        // m's nodes are disjoint from dst's relinked tail.
                        assert(dst_empty || model[m][p] != hd.tail);
                    }
                }
            }
        }
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
            self.model_view() == old(self).model_view(),
    {
        let heads = self.heads.mark(shrink);
        let nodes = self.nodes.mark(shrink);
        ListArenaToken { heads, nodes }
    }

    /// Restore both arenas to the marked snapshot. The restored snapshots must
    /// jointly form a valid arena *for the current ghost model* — i.e. the
    /// model still describes them (`arena_model_wf`). Semi-persistence composes
    /// from the two inner `Vec`s.
    pub fn restore(&mut self, token: ListArenaToken, Ghost(snap_model): Ghost<Seq<Seq<usize>>>)
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
            // the snapshots being restored, together with `snap_model`, form a
            // valid arena (the ghost model that was live at the mark).
            arena_model_wf(
                snap_model,
                old(self).heads.snapshots_view()[token.heads.frame_idx as int],
                old(self).nodes.snapshots_view()[token.nodes.frame_idx as int]),
        ensures
            self.wf(),
            self.heads_view()
                == old(self).heads.snapshots_view()[token.heads.frame_idx as int],
            self.nodes_view()
                == old(self).nodes.snapshots_view()[token.nodes.frame_idx as int],
            self.model_view() == snap_model,
    {
        self.heads.restore(token.heads);
        self.nodes.restore(token.nodes);
        self.model = Ghost(snap_model);
    }
}

/// Structural arena validity over raw snapshot sequences *plus* the ghost model
/// that was live at the mark (for `restore`): the restored heads/nodes, with
/// `model`, must satisfy the same in-range + disjoint + cache clauses as `wf`.
pub open spec fn arena_model_wf<T>(
    model: Seq<Seq<usize>>, heads: Seq<ListHead>, nodes: Seq<ListNode<T>>,
) -> bool {
    &&& model.len() == heads.len()
    &&& (forall|l: int, p: int|
            0 <= l < model.len() && 0 <= p < (#[trigger] model[l]).len()
                ==> #[trigger] model[l][p] < nodes.len())
    &&& (forall|l1: int, p1: int, l2: int, p2: int|
            0 <= l1 < model.len() && 0 <= p1 < model[l1].len()
                && 0 <= l2 < model.len() && 0 <= p2 < model[l2].len()
                && (#[trigger] model[l1][p1]) == (#[trigger] model[l2][p2])
                    ==> l1 == l2 && p1 == p2)
    &&& (forall|l: int| 0 <= l < model.len() ==> {
            let h = (#[trigger] heads[l]).head;
            if model[l].len() == 0 { h.is_null() }
            else { !h.is_null() && h.target() == model[l][0] }
        })
    &&& (forall|l: int| 0 <= l < model.len() && (#[trigger] model[l]).len() > 0
            ==> heads[l].tail == model[l][model[l].len() - 1])
    &&& (forall|l: int, p: int|
            0 <= l < model.len() && 0 <= p < model[l].len() ==> {
                let nx = nodes[#[trigger] model[l][p] as int].next;
                if p == model[l].len() - 1 { nx.is_null() }
                else { !nx.is_null() && nx.target() == model[l][p + 1] }
            })
}

/// Source position of `model[lx][px]` after `splice(dst, src)` (model =
/// dst++src at dst, [] at src): maps each post-position back to its OLD
/// `(list, pos)`. Used to discharge disjointness via the old global disjointness.
pub open spec fn splice_src(
    old_model: Seq<Seq<usize>>, dst: int, src: int, lx: int, px: int,
) -> (int, int) {
    if lx == dst {
        if px < old_model[dst].len() { (dst, px) } else { (src, px - old_model[dst].len()) }
    } else {
        (lx, px)
    }
}

/// Cache-consistency of a single node's `next` after `splice`. Only `dst`'s old
/// tail node was relinked (to `src`'s head); all others are unchanged.
pub proof fn splice_cache_node<T, const TRACK: bool>(
    pre: ListArena<T, TRACK>, post: &ListArena<T, TRACK>,
    dst: int, src: int, dtail: usize, shead: NodeRef,
    dst_empty: bool, src_empty: bool, l2: int, p: int,
)
    where T: Sized + Copy + core::default::Default
    requires
        pre.wf(),
        0 <= dst < pre.model_view().len(),
        0 <= src < pre.model_view().len(),
        dst != src,
        0 <= l2 < post.model_view().len(),
        0 <= p < post.model_view()[l2].len(),
        post.nodes_view().len() == pre.nodes_view().len(),
        post.model_view().len() == pre.model_view().len(),
        // post model = dst++src at dst, [] at src, else unchanged.
        post.model_view()[dst]
            == pre.model_view()[dst] + pre.model_view()[src],
        post.model_view()[src] == Seq::<usize>::empty(),
        forall|m: int| 0 <= m < post.model_view().len() && m != dst && m != src
            ==> post.model_view()[m] == pre.model_view()[m],
        dst_empty == (pre.model_view()[dst].len() == 0),
        src_empty == (pre.model_view()[src].len() == 0),
        // nodes: only dtail relinked to shead (when both non-empty); else equal.
        !dst_empty && !src_empty ==> {
            &&& dtail == pre.model_view()[dst][pre.model_view()[dst].len() - 1]
            &&& shead == pre.heads_view()[src].head
            &&& post.nodes_view()[dtail as int].next == shead
            &&& (forall|k: int| 0 <= k < post.nodes_view().len() && k != dtail as int
                    ==> post.nodes_view()[k] == pre.nodes_view()[k])
        },
        (dst_empty || src_empty) ==>
            (forall|k: int| 0 <= k < post.nodes_view().len()
                ==> post.nodes_view()[k] == pre.nodes_view()[k]),
    ensures
        ({
            let nx = post.nodes_view()[post.model_view()[l2][p] as int].next;
            if p == post.model_view()[l2].len() - 1 { nx.is_null() }
            else { !nx.is_null() && nx.target() == post.model_view()[l2][p + 1] }
        }),
{
    let pm = pre.model_view();
    let pn = pre.nodes_view();
    let pom = post.model_view();
    let pon = post.nodes_view();
    let dlen = pm[dst].len();
    let idx = pom[l2][p];

    if l2 == dst && !dst_empty && !src_empty {
        // dst's concatenated list: [old dst nodes][old src nodes].
        if p < dlen - 1 {
            // interior of old dst (not the tail): node & its successor unchanged
            // from old dst's cache; idx != dtail since dtail is dst's LAST.
            assert(pom[l2][p] == pm[dst][p]);
            assert(pm[dst][p] != dtail);  // dtail is the last of dst, p < dlen-1
            assert(pon[idx as int] == pn[idx as int]);
            // old cache_ok for dst at p: next -> pm[dst][p+1] == pom[l2][p+1].
            assert(pom[l2][p + 1] == pm[dst][p + 1]);
        } else if p == dlen - 1 {
            // dst's old tail, relinked to src's head == old src[0] == pom[l2][dlen].
            assert(pm[dst][p] == dtail);
            assert(pon[dtail as int].next == shead);
            assert(shead.target() == pm[src][0]);          // old cache: src head
            assert(pom[l2][p + 1] == pm[src][0]);
        } else {
            // src portion: index p maps to old src[p - dlen]; nodes unchanged
            // (only dtail relinked, and src nodes != dtail by disjointness).
            assert(pom[l2][p] == pm[src][p - dlen]);
            assert(pm[src][p - dlen] != dtail);            // disjoint: src ∩ dst = ∅
            assert(pon[idx as int] == pn[idx as int]);
            if p == pom[l2].len() - 1 {
                // last of src: old src cache says null.
                assert(p - dlen == pm[src].len() - 1);
            } else {
                assert(pom[l2][p + 1] == pm[src][p + 1 - dlen]);
            }
        }
    } else if l2 == dst {
        // dst empty or src empty: model[dst] is whichever was non-empty (or
        // empty), nodes fully unchanged.
        assert(pom[l2][p] == pm[dst][p] || pom[l2][p] == pm[src][p - dlen]);
        assert(pon[idx as int] == pn[idx as int]);
    } else {
        // other list (incl. src, which is now empty so vacuous): unchanged model,
        // and its nodes are disjoint from dtail.
        assert(pom[l2] == pm[l2]);
        assert(pm[l2][p] != dtail || dst_empty || src_empty);
        assert(pon[idx as int] == pn[idx as int]);
    }
}

} // verus!
