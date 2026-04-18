// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Arena-backed intrusive singly-linked lists with semi-persistence.
//!
//! `ListArena<T, L, N, TRACK>` owns both list headers and list nodes.
//! - `L: DenseId` — list identifier (indexes into heads vec)
//! - `N: DenseId` — node identifier (indexes into nodes vec)
//! - `T: Tagged` — payload type stored in each node
//!
//! Lists are identified by opaque `L` handles. All mutation goes through
//! the arena. Internal encoding is not exposed.

use crate::IndexLike;
use crate::dense_id::DenseId;
use crate::tagged::{Opt, Tagged};
use crate::{ShrinkPolicy, VecToken};

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct ListNode<T: Tagged, N: DenseId> {
    payload: T,
    next_repr: <N as Tagged>::Repr,
}

impl<T: Tagged, N: DenseId> ListNode<T, N> {
    fn new(payload: T, next: Opt<N>) -> Self {
        Self {
            payload,
            next_repr: next.into_raw(),
        }
    }

    fn next(&self) -> Opt<N> {
        Opt::from_raw(self.next_repr)
    }

    fn set_next(&mut self, next: Opt<N>) {
        self.next_repr = next.into_raw();
    }
}

impl<T: Tagged, N: DenseId> Tagged for ListNode<T, N> {
    type Repr = (T::Repr, <N as Tagged>::Repr);

    fn into_repr(self) -> Self::Repr {
        (self.payload.into_repr(), self.next_repr)
    }
    fn from_repr(r: &Self::Repr) -> Self {
        Self {
            payload: T::from_repr(&r.0),
            next_repr: r.1,
        }
    }
    fn tag(r: &Self::Repr) -> bool {
        T::tag(&r.0)
    }
    fn set_tag(r: &mut Self::Repr) {
        T::set_tag(&mut r.0);
    }
    fn clear_tag(r: &mut Self::Repr) {
        T::clear_tag(&mut r.0);
    }
}

/// Head/tail pointers. Head is `Opt<N>` (tag = None). Tail is raw `N`
/// (tag = VecI capture). Tail is only read when head is Some.
#[derive(Clone, Copy)]
struct ListHead<N: DenseId> {
    head_repr: <N as Tagged>::Repr,
    tail_repr: <N as Tagged>::Repr,
}

impl<N: DenseId> ListHead<N> {
    fn empty() -> Self {
        Self {
            head_repr: Opt::<N>::none().into_raw(),
            tail_repr: N::default().into_repr(),
        }
    }

    fn head(&self) -> Opt<N> {
        Opt::from_raw(self.head_repr)
    }

    fn is_empty(&self) -> bool {
        N::tag(&self.head_repr)
    }
}

/// Tagged delegates to tail_repr (first in Repr tuple). VecI steals that bit.
impl<N: DenseId> Tagged for ListHead<N> {
    type Repr = (<N as Tagged>::Repr, <N as Tagged>::Repr);

    fn into_repr(self) -> Self::Repr {
        (self.tail_repr, self.head_repr)
    }
    fn from_repr(r: &Self::Repr) -> Self {
        Self {
            tail_repr: r.0,
            head_repr: r.1,
        }
    }
    fn tag(r: &Self::Repr) -> bool {
        N::tag(&r.0)
    }
    fn set_tag(r: &mut Self::Repr) {
        N::set_tag(&mut r.0);
    }
    fn clear_tag(r: &mut Self::Repr) {
        N::clear_tag(&mut r.0);
    }
}

// ---------------------------------------------------------------------------
// ListArena
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub struct ListArenaToken {
    heads: VecToken,
    nodes: VecToken,
}

pub struct ListArena<T: Tagged, L: DenseId, N: DenseId, const TRACK: bool> {
    heads: crate::VecI<ListHead<N>, L::Index, TRACK>,
    nodes: crate::VecI<ListNode<T, N>, N::Index, TRACK>,
}

impl<T: Tagged, L: DenseId, N: DenseId, const TRACK: bool> Default for ListArena<T, L, N, TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Tagged, L: DenseId, N: DenseId, const TRACK: bool> ListArena<T, L, N, TRACK> {
    pub fn new() -> Self {
        Self {
            heads: crate::VecI::new(),
            nodes: crate::VecI::new(),
        }
    }

    /// Create a new empty list.
    pub fn new_list(&mut self) -> L {
        let id = L::from_usize(self.heads.len().as_usize());
        self.heads.push(ListHead::empty());
        id
    }

    /// Prepend a payload to the front of the list.
    pub fn prepend(&mut self, list: L, payload: T) {
        let mut h = self.heads.get(list.into());
        let was_empty = h.is_empty();
        let slot = N::from_usize(self.nodes.len().as_usize());
        self.nodes.push(ListNode::new(payload, h.head()));
        h.head_repr = Opt::some(slot).into_raw();
        if was_empty {
            h.tail_repr = slot.into_repr();
        }
        self.heads.set(list.into(), h);
    }

    /// Append a payload to the back of the list.
    pub fn append(&mut self, list: L, payload: T) {
        let mut h = self.heads.get(list.into());
        let slot = N::from_usize(self.nodes.len().as_usize());
        self.nodes.push(ListNode::new(payload, Opt::none()));
        if h.is_empty() {
            h.head_repr = Opt::some(slot).into_raw();
        } else {
            let old_tail = N::from_repr(&h.tail_repr);
            let mut tail_node = self.nodes.get(old_tail.into());
            tail_node.set_next(Opt::some(slot));
            self.nodes.set(old_tail.into(), tail_node);
        }
        h.tail_repr = slot.into_repr();
        self.heads.set(list.into(), h);
    }

    /// Splice `src` after `dst`: dst becomes dst ++ src.
    /// `src` is cleared to empty — the handle remains valid but reads as empty.
    pub fn splice(&mut self, dst: L, src: L) {
        let src_h = self.heads.get(src.into());
        if src_h.is_empty() {
            return;
        }
        let mut dst_h = self.heads.get(dst.into());
        if dst_h.is_empty() {
            dst_h.head_repr = src_h.head_repr;
            dst_h.tail_repr = src_h.tail_repr;
        } else {
            // Link dst's tail → src's head
            let dst_tail = N::from_repr(&dst_h.tail_repr);
            let mut tail_node = self.nodes.get(dst_tail.into());
            tail_node.set_next(src_h.head());
            self.nodes.set(dst_tail.into(), tail_node);
            dst_h.tail_repr = src_h.tail_repr;
        }
        self.heads.set(dst.into(), dst_h);
        // Clear src to empty
        self.heads.set(src.into(), ListHead::empty());
    }

    /// Is the list empty?
    pub fn is_empty(&self, list: L) -> bool {
        self.heads.get(list.into()).is_empty()
    }

    /// Iterate payloads in list order.
    pub fn iter(&self, list: L) -> ListIter<'_, T, N, TRACK> {
        let h = self.heads.get(list.into());
        ListIter {
            nodes: &self.nodes,
            current: h.head(),
        }
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> ListArenaToken {
        ListArenaToken {
            heads: self.heads.mark(shrink),
            nodes: self.nodes.mark(shrink),
        }
    }

    pub fn restore(&mut self, token: ListArenaToken) {
        self.heads.restore(token.heads);
        self.nodes.restore(token.nodes);
    }
}

pub struct ListIter<'a, T: Tagged, N: DenseId, const TRACK: bool> {
    nodes: &'a crate::VecI<ListNode<T, N>, N::Index, TRACK>,
    current: Opt<N>,
}

impl<T: Tagged, N: DenseId, const TRACK: bool> Iterator for ListIter<'_, T, N, TRACK> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let n = self.current.get()?;
        let node = self.nodes.get(n.into());
        self.current = node.next();
        Some(node.payload)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
#[allow(dead_code)]
mod tests {
    use super::*;
    use crate::id::{UseListId, UseNodeId};

    crate::define_id31! {
        /// Test-only e-node ID.
        struct TestNodeId / StoredTestNodeId, "t";
    }

    type Arena = ListArena<TestNodeId, UseListId, UseNodeId, false>;
    type ArenaT = ListArena<TestNodeId, UseListId, UseNodeId, true>;

    fn collect(arena: &Arena, list: UseListId) -> Vec<u32> {
        arena.iter(list).map(|e| e.raw()).collect()
    }

    #[test]
    fn empty_list() {
        let mut a = Arena::new();
        let l = a.new_list();
        assert!(a.is_empty(l));
        assert_eq!(collect(&a, l), Vec::<u32>::new());
    }

    #[test]
    fn prepend_one() {
        let mut a = Arena::new();
        let l = a.new_list();
        a.prepend(l, TestNodeId::new(42));
        assert!(!a.is_empty(l));
        assert_eq!(collect(&a, l), vec![42]);
    }

    #[test]
    fn prepend_three() {
        let mut a = Arena::new();
        let l = a.new_list();
        a.prepend(l, TestNodeId::new(1));
        a.prepend(l, TestNodeId::new(2));
        a.prepend(l, TestNodeId::new(3));
        assert_eq!(collect(&a, l), vec![3, 2, 1]);
    }

    #[test]
    fn append_three() {
        let mut a = Arena::new();
        let l = a.new_list();
        a.append(l, TestNodeId::new(1));
        a.append(l, TestNodeId::new(2));
        a.append(l, TestNodeId::new(3));
        assert_eq!(collect(&a, l), vec![1, 2, 3]);
    }

    #[test]
    fn splice_both_nonempty() {
        let mut a = Arena::new();
        let dst = a.new_list();
        a.prepend(dst, TestNodeId::new(1));
        a.prepend(dst, TestNodeId::new(2));

        let src = a.new_list();
        a.prepend(src, TestNodeId::new(10));
        a.prepend(src, TestNodeId::new(20));

        a.splice(dst, src);
        // dst ++ src: [2, 1, 20, 10]
        assert_eq!(collect(&a, dst), vec![2, 1, 20, 10]);
        assert!(a.is_empty(src));
    }

    #[test]
    fn splice_into_empty() {
        let mut a = Arena::new();
        let dst = a.new_list();
        let src = a.new_list();
        a.prepend(src, TestNodeId::new(5));
        a.splice(dst, src);
        assert_eq!(collect(&a, dst), vec![5]);
    }

    #[test]
    fn splice_empty_src() {
        let mut a = Arena::new();
        let dst = a.new_list();
        a.prepend(dst, TestNodeId::new(1));
        let src = a.new_list();
        a.splice(dst, src);
        assert_eq!(collect(&a, dst), vec![1]);
    }

    #[test]
    fn two_independent_lists() {
        let mut a = Arena::new();
        let l1 = a.new_list();
        let l2 = a.new_list();
        a.prepend(l1, TestNodeId::new(1));
        a.prepend(l2, TestNodeId::new(2));
        assert_eq!(collect(&a, l1), vec![1]);
        assert_eq!(collect(&a, l2), vec![2]);
    }

    #[test]
    fn mark_restore() {
        let mut a = ArenaT::new();
        let l = a.new_list();
        a.prepend(l, TestNodeId::new(1));
        let token = a.mark(ShrinkPolicy::Never);
        a.prepend(l, TestNodeId::new(2));
        a.prepend(l, TestNodeId::new(3));
        assert_eq!(a.iter(l).count(), 3);
        a.restore(token);
        assert_eq!(a.iter(l).map(|e| e.raw()).collect::<Vec<_>>(), vec![1]);
    }

    #[test]
    fn mark_restore_splice() {
        let mut a = ArenaT::new();
        let l1 = a.new_list();
        let l2 = a.new_list();
        a.prepend(l1, TestNodeId::new(1));
        a.prepend(l2, TestNodeId::new(2));
        let token = a.mark(ShrinkPolicy::Never);
        a.splice(l1, l2);
        assert_eq!(a.iter(l1).count(), 2);
        a.restore(token);
        assert_eq!(a.iter(l1).map(|e| e.raw()).collect::<Vec<_>>(), vec![1]);
        assert_eq!(a.iter(l2).map(|e| e.raw()).collect::<Vec<_>>(), vec![2]);
    }
}
