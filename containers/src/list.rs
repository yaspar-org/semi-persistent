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

impl<T: Tagged, N: DenseId> Default for ListNode<T, N> {
    fn default() -> Self {
        // Filler for `resize_default` during restore; never observed.
        Self::new(T::default(), Opt::none())
    }
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

/// Head/tail pointers plus a cached element count. Head is `Opt<N>` (tag = None).
/// Tail is raw `N` (tag = VecI capture). Tail is only read when head is Some.
///
/// `len` is the number of nodes in the list, maintained incrementally on
/// `prepend`/`append` (+1) and `splice` (dst gains src's count, src resets to 0),
/// so `ListArena::len` is O(1) without traversing. It rolls back with the rest of
/// the header: the whole `ListHead` is captured as one `Tagged` value on every
/// `set`, so semi-persistent restore reverts `len` together with the pointers.
///
/// `len: N::Index`, not `u32`. A list's length is bounded by the node arena's
/// population and by nothing else, and that arena is a `VecI<_, N::Index>`, so
/// `N::Index` is the width the quantity actually lives in — a `u32` here capped
/// every list at 4 billion elements no matter how wide `N` was, which is exactly
/// the kind of cap a 63-bit configuration exists to remove.
///
/// The widening is free at both id families, which is why it is unconditional.
/// At a 31-bit `N` the field was already `u32`, so nothing moves. At a 63-bit `N`
/// the header is two `u64` words followed by the count: `(u64, u64, u32)` pads to
/// 24 bytes and `(u64, u64, u64)` *is* 24, so the wider count occupies padding
/// that was there either way. Asserted in `head_is_two_words_plus_a_same_width_count`.
#[derive(Clone, Copy)]
struct ListHead<N: DenseId> {
    head_repr: <N as Tagged>::Repr,
    tail_repr: <N as Tagged>::Repr,
    len: N::Index,
}

impl<N: DenseId> Default for ListHead<N> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<N: DenseId> ListHead<N> {
    fn empty() -> Self {
        Self {
            head_repr: Opt::<N>::none().into_raw(),
            tail_repr: N::default().into_repr(),
            len: N::Index::MIN,
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
/// `len` rides along as a plain `Copy` field; it carries no tag.
impl<N: DenseId> Tagged for ListHead<N> {
    type Repr = (<N as Tagged>::Repr, <N as Tagged>::Repr, N::Index);

    fn into_repr(self) -> Self::Repr {
        (self.tail_repr, self.head_repr, self.len)
    }
    fn from_repr(r: &Self::Repr) -> Self {
        Self {
            tail_repr: r.0,
            head_repr: r.1,
            len: r.2,
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

    /// Bytes consumed by diff tracking only, summed over the two inner vecs.
    /// Diagnostic; forwards `Vec::tracking_bytes`. This is the production side
    /// of the arena memory-parity assertion: the verus `ListArena` now uses
    /// `InlineStore` over typed index columns exactly as this one does, and
    /// `containers-conformance/tests/list_arena_differential.rs` compares the
    /// two implementations through this pair against exact constants.
    pub fn tracking_bytes(&self) -> usize {
        self.heads.tracking_bytes() + self.nodes.tracking_bytes()
    }

    /// Total bytes: both inner vecs (struct + store backing + tracking).
    /// Diagnostic; forwards `Vec::total_bytes`.
    pub fn total_bytes(&self) -> usize {
        self.heads.total_bytes() + self.nodes.total_bytes()
    }

    /// One more element in a list, or a panic.
    ///
    /// Checked rather than a bare `+= 1`, even though the increment cannot in fact
    /// overflow: a list holds distinct nodes of the arena, the arena's population is
    /// capped by `N::from_usize` at `N::MAX`, and `N::MAX` is *half* of
    /// `N::Index::MAX` because the id gives up its top bit to the capture tag. So the
    /// count has a full spare bit of headroom above anything reachable.
    ///
    /// That argument holds only as long as the node ids and the count are drawn from
    /// the same family, which is a property of two other functions, not of this one.
    /// An unchecked `+=` would turn any future divergence into a wrapped length: a
    /// header claiming 0 elements while `head` still points into a live chain, so
    /// `len()` and `iter().count()` disagree and every caller that trusts the O(1)
    /// count reads the list as empty. A panic here says the configuration is too
    /// narrow; a wrap says nothing at all.
    #[inline]
    fn grown(len: N::Index) -> N::Index {
        len.checked_incr()
            .expect("list length exceeds the node index range")
    }

    /// Create a new empty list.
    /// Total-API counterpart (parity with the verified crate's shell): production's
    /// core panics on misuse, so the counterpart always returns Ok and the panic
    /// stays the documented behavior. Exists so shared prod/verus harness
    /// bodies can use one calling convention.
    pub fn try_new_list(&mut self) -> Result<L, &'static str> {
        Ok(self.new_list())
    }

    pub fn new_list(&mut self) -> L {
        let id = L::from_usize(self.heads.len().as_usize());
        self.heads.push(ListHead::empty());
        id
    }

    /// Prepend a payload to the front of the list.
    /// Total-API counterpart (parity with the verified crate's shell): production's
    /// core panics on misuse, so the counterpart always returns Ok and the panic
    /// stays the documented behavior. Exists so shared prod/verus harness
    /// bodies can use one calling convention.
    pub fn try_prepend(&mut self, l: L, payload: T) -> Result<(), &'static str> {
        self.prepend(l, payload);
        Ok(())
    }

    pub fn prepend(&mut self, list: L, payload: T) {
        let mut h = self.heads.get(list.into());
        let was_empty = h.is_empty();
        let slot = N::from_usize(self.nodes.len().as_usize());
        self.nodes.push(ListNode::new(payload, h.head()));
        h.head_repr = Opt::some(slot).into_raw();
        if was_empty {
            h.tail_repr = slot.into_repr();
        }
        h.len = Self::grown(h.len);
        self.heads.set(list.into(), h);
    }

    /// Append a payload to the back of the list.
    /// Total-API counterpart (parity with the verified crate's shell): production's
    /// core panics on misuse, so the counterpart always returns Ok and the panic
    /// stays the documented behavior. Exists so shared prod/verus harness
    /// bodies can use one calling convention.
    pub fn try_append(&mut self, l: L, payload: T) -> Result<(), &'static str> {
        self.append(l, payload);
        Ok(())
    }

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
        h.len = Self::grown(h.len);
        self.heads.set(list.into(), h);
    }

    /// Splice `src` after `dst`: dst becomes dst ++ src.
    /// `src` is cleared to empty — the handle remains valid but reads as empty.
    pub fn splice(&mut self, dst: L, src: L) {
        // Same-list splice would link the tail to its own head (a cycle iter()
        // never exits) and then overwrite the header; the verified counterpart traps
        // this and the misuse suite pins the panic. Keep the crates aligned.
        assert!(
            dst != src,
            "ListArena::splice: dst and src are the same list"
        );
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
        dst_h.len = dst_h
            .len
            .checked_add(src_h.len)
            .expect("spliced list length exceeds the node index range");
        self.heads.set(dst.into(), dst_h);
        // Clear src to empty
        self.heads.set(src.into(), ListHead::empty());
    }

    /// Is the list empty?
    pub fn is_empty(&self, list: L) -> bool {
        self.heads.get(list.into()).is_empty()
    }

    /// Number of elements in the list, O(1) (read from the cached header count).
    ///
    /// Returns `N::Index` — the node arena's index type — because that is what bounds
    /// a list's length. Callers wanting a plain count use `IndexLike::as_usize`.
    pub fn len(&self, list: L) -> N::Index {
        self.heads.get(list.into()).len
    }

    /// Iterate payloads in list order.
    pub fn iter(&self, list: L) -> ListIter<'_, T, N, TRACK> {
        let h = self.heads.get(list.into());
        ListIter {
            nodes: &self.nodes,
            current: h.head(),
        }
    }

    /// Total-API counterpart (parity with the verified crate's shell): production's
    /// core panics on misuse, so the counterpart always returns Ok and the panic
    /// stays the documented behavior. Exists so shared prod/verus harness
    /// bodies can use one calling convention.
    pub fn try_mark(&mut self, policy: ShrinkPolicy) -> Result<ListArenaToken, &'static str> {
        Ok(self.mark(policy))
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> ListArenaToken {
        ListArenaToken {
            heads: self.heads.mark(shrink),
            nodes: self.nodes.mark(shrink),
        }
    }

    /// Total-API counterpart (parity with the verified crate's shell): production's
    /// core panics on misuse, so the counterpart always returns Ok and the panic
    /// stays the documented behavior. Exists so shared prod/verus harness
    /// bodies can use one calling convention.
    pub fn try_restore(&mut self, token: ListArenaToken) -> Result<(), &'static str> {
        self.restore(token);
        Ok(())
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

    crate::define_id63! {
        /// Test-only 63-bit node id, for the header-layout claim below. The rest of this
        /// module runs at 31 bits (`UseNodeId`), where the count's width is invisible.
        struct WideNodeId / StoredWideNodeId, "w";
    }

    /// `len` follows the node id family, and that is free at both of them.
    ///
    /// This is the assertion the field's doc comment points at. It exists because the
    /// widening from `u32` to `N::Index` is *only* observable at 63 bits — at 31 bits the
    /// field was already `u32` — so a test at one width could not tell a correct header
    /// from one that had quietly regained a fixed 4-billion cap.
    ///
    /// 31-bit: `(u32, u32, u32)` = 12. 63-bit: `(u64, u64, u64)` = 24, which is what
    /// `(u64, u64, u32)` padded to as well — the count occupies alignment padding that was
    /// there either way, so nothing is paid for removing the cap.
    #[test]
    fn head_is_two_words_plus_a_same_width_count() {
        use core::mem::size_of;

        assert_eq!(
            size_of::<ListHead<UseNodeId>>(),
            3 * size_of::<u32>(),
            "a 31-bit header is two id words plus an equally wide count"
        );
        assert_eq!(
            size_of::<ListHead<WideNodeId>>(),
            3 * size_of::<u64>(),
            "a 63-bit header is two id words plus an equally wide count"
        );

        // The count really is the *node* index type, not some other width that happens to
        // agree. Stated against the associated type so it cannot drift.
        assert_eq!(size_of::<<UseNodeId as DenseId>::Index>(), size_of::<u32>());
        assert_eq!(
            size_of::<<WideNodeId as DenseId>::Index>(),
            size_of::<u64>()
        );

        // Free, not merely equal: a `u32` count at 63 bits would have padded to the same
        // 24 bytes, which is the whole reason the widening is unconditional rather than
        // gated on the id width.
        assert_eq!(
            size_of::<(u64, u64, u32)>(),
            size_of::<(u64, u64, u64)>(),
            "the wider count lives in padding the header already carried"
        );

        // And `Tagged::Repr` — the form that actually occupies the store's backing vector
        // — tracks the header, since the whole header is captured as one value per write.
        assert_eq!(
            size_of::<<ListHead<UseNodeId> as Tagged>::Repr>(),
            size_of::<ListHead<UseNodeId>>()
        );
        assert_eq!(
            size_of::<<ListHead<WideNodeId> as Tagged>::Repr>(),
            size_of::<ListHead<WideNodeId>>()
        );
    }

    crate::define_id7! {
        /// Test-only 7-bit node id: 128 nodes, so the arena's ceiling is reachable with a
        /// literal number of pushes. At 31 bits the same cases need four billion.
        struct TinyNodeId / StoredTinyNodeId, "y";
    }

    type TinyArena = ListArena<TestNodeId, UseListId, TinyNodeId, false>;

    /// The count has a spare bit above anything the arena can reach, and the arena says so
    /// rather than letting a length wrap.
    ///
    /// This is the argument in `grown`'s doc, asserted instead of assumed: `N::MAX` is
    /// *half* of `N::Index::MAX` because the id gives up its top bit to the capture tag, so
    /// the ids run out a full bit before the count does. What a wrap would look like is a
    /// header claiming 0 elements while `head` still points into a live chain — `len()` and
    /// `iter().count()` disagreeing — which is why both are compared here.
    #[test]
    fn len_has_headroom_above_the_full_arena() {
        let mut a = TinyArena::new();
        let l = a.new_list();
        for i in 0..128u32 {
            a.append(l, TestNodeId::new(i));
        }
        assert_eq!(
            a.len(l).as_usize(),
            128,
            "every 7-bit node id is in the list"
        );
        assert_eq!(
            a.len(l).as_usize(),
            a.iter(l).count(),
            "the cached count and the traversal must agree"
        );
        assert!(
            a.len(l) < <TinyNodeId as DenseId>::Index::MAX,
            "a full arena still leaves the count a spare bit"
        );
    }

    /// One node past the id space panics rather than aliasing two positions onto one id.
    /// The ids are what run out; `grown` is never the thing that refuses.
    #[test]
    #[should_panic(expected = "exceeds range")]
    fn node_id_exhaustion_panics_rather_than_aliasing() {
        let mut a = TinyArena::new();
        let l = a.new_list();
        for i in 0..129u32 {
            a.append(l, TestNodeId::new(i));
        }
    }

    #[test]
    fn len_tracks_prepend_append_splice() {
        let mut a = Arena::new();
        let l = a.new_list();
        assert_eq!(a.len(l), 0);
        a.prepend(l, TestNodeId::new(1));
        a.append(l, TestNodeId::new(2));
        a.prepend(l, TestNodeId::new(3));
        assert_eq!(a.len(l), 3);
        // len matches the actual traversal count.
        assert_eq!(a.len(l).as_usize(), a.iter(l).count());

        let src = a.new_list();
        a.append(src, TestNodeId::new(10));
        a.append(src, TestNodeId::new(20));
        assert_eq!(a.len(src), 2);
        a.splice(l, src);
        // dst gains src's count; src resets to 0.
        assert_eq!(a.len(l), 5);
        assert_eq!(a.len(src), 0);
        assert_eq!(a.len(l).as_usize(), a.iter(l).count());
    }

    #[test]
    fn len_rolls_back_on_restore() {
        let mut a = ArenaT::new();
        let l = a.new_list();
        a.prepend(l, TestNodeId::new(1));
        let token = a.mark(ShrinkPolicy::Never);
        a.append(l, TestNodeId::new(2));
        a.append(l, TestNodeId::new(3));
        assert_eq!(a.len(l), 3);
        a.restore(token);
        // The cached count reverts with the header.
        assert_eq!(a.len(l), 1);
        assert_eq!(a.len(l).as_usize(), a.iter(l).count());
    }

    #[test]
    fn len_rolls_back_on_splice_restore() {
        let mut a = ArenaT::new();
        let l1 = a.new_list();
        let l2 = a.new_list();
        a.prepend(l1, TestNodeId::new(1));
        a.prepend(l2, TestNodeId::new(2));
        let token = a.mark(ShrinkPolicy::Never);
        a.splice(l1, l2);
        assert_eq!(a.len(l1), 2);
        assert_eq!(a.len(l2), 0);
        a.restore(token);
        // Both counts revert: l1 back to 1, l2 back to 1.
        assert_eq!(a.len(l1), 1);
        assert_eq!(a.len(l2), 1);
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
