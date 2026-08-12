// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Generic node types for the e-graph node stores.
//!
//! Three structs cover all ten node kinds:
//! - `FixedArityNode<G, O, K>` — Plain0/1/2/3 and Commutative
//! - `VariableArityNode<G, O>` — PlainN, A, AC, ACI
//! - `LitNode<G, O, V>` — literal leaves
//!
//! `global_id` and `op` are stored as `Repr` types so the tag bits
//! can be manipulated directly via `Tagged` without unsafe casts.
//! `global_id` MSB = VecI capture tag, `op` MSB = has_history flag.
//! `flags` is a per-node u8 bitfield for control bits (subsumption, etc).

use std::hash::{Hash, Hasher};

use crate::containers::DenseId;
use crate::containers::Tagged;

/// Per-node control flags stored in the `flags` field.
///
/// `FLAG_SUBSUMED` and `FLAG_AC_COLLAPSED` are deliberately distinct concepts (see
/// `doc/design/ac-congruence-completeness.md` §6b):
/// - `FLAG_SUBSUMED` — user-level `(subsume …)`: "do not *match* this node." The
///   matcher's indices skip it.
/// - `FLAG_AC_COLLAPSED` — AC completion's inter-reduction: "do not use this node as a
///   completion *rule*" (its child multiset is reducible by a smaller AC rule, so every
///   superposition off it is redundant). The node stays fully **matchable** — its
///   reduced form is in the same class — and stays a legal child of other nodes; only
///   AC completion's active rule set excludes it.
///
/// A node may carry either, both, or neither. Completion's active set is the AC nodes
/// with *neither* flag; the matcher's visible set is the nodes without `FLAG_SUBSUMED`.
pub const FLAG_SUBSUMED: u8 = 1 << 0;
pub const FLAG_CONSTRUCTOR: u8 = 1 << 1;
pub const FLAG_AC_COLLAPSED: u8 = 1 << 2;

// ---------------------------------------------------------------------------
// FixedArityNode<G, O, K>
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub struct FixedArityNode<G: DenseId, O: DenseId, const K: usize> {
    pub global_id: G::Repr,
    pub op: O::Repr,
    pub flags: u8,
    pub children: [G; K],
}

// Filler for `resize_default` during restore; never observed (overwritten by
// the captured diff value). Routes id values through `new`/`into_repr` rather
// than fabricating a raw `Repr`, so the stolen niche bit is cleared.
impl<G: DenseId, O: DenseId, const K: usize> Default for FixedArityNode<G, O, K> {
    fn default() -> Self {
        Self::new(G::default(), O::default(), [G::default(); K])
    }
}

impl<G: DenseId, O: DenseId, const K: usize> FixedArityNode<G, O, K> {
    #[inline]
    pub fn new(global_id: G, op: O, children: [G; K]) -> Self {
        Self {
            global_id: global_id.into_repr(),
            op: op.into_repr(),
            flags: 0,
            children,
        }
    }

    #[inline]
    pub fn global_id(&self) -> G {
        G::from_repr(&self.global_id)
    }

    #[inline]
    pub fn op(&self) -> O {
        O::from_repr(&self.op)
    }

    #[inline]
    pub fn has_history(&self) -> bool {
        O::tag(&self.op)
    }

    #[inline]
    pub fn set_history(&mut self) {
        O::set_tag(&mut self.op);
    }

    #[inline]
    pub fn content_hash(&self) -> u64
    where
        O: Hash,
        G: Hash,
    {
        let mut h = rapidhash::fast::RapidHasher::default();
        self.op().hash(&mut h);
        self.children.hash(&mut h);
        h.finish()
    }

    #[inline]
    pub fn content_eq(&self, other: &Self) -> bool
    where
        O: PartialEq,
        G: PartialEq,
    {
        self.op() == other.op() && self.children == other.children
    }
}

impl<G: DenseId, O: DenseId, const K: usize> Tagged for FixedArityNode<G, O, K> {
    type Repr = Self;
    #[inline(always)]
    fn into_repr(self) -> Self {
        self
    }
    #[inline(always)]
    fn from_repr(stored: &Self) -> Self {
        let mut v = *stored;
        G::clear_tag(&mut v.global_id);
        O::clear_tag(&mut v.op);
        v
    }
    #[inline(always)]
    fn tag(stored: &Self) -> bool {
        G::tag(&stored.global_id)
    }
    #[inline(always)]
    fn set_tag(stored: &mut Self) {
        G::set_tag(&mut stored.global_id);
    }
    #[inline(always)]
    fn clear_tag(stored: &mut Self) {
        G::clear_tag(&mut stored.global_id);
    }
}

// ---------------------------------------------------------------------------
// VariableArityNode<G, O>
// ---------------------------------------------------------------------------

/// A node whose children live in a shared side pool, addressed by a `[start, end)` span.
///
/// `start`/`end` stay `usize` **deliberately**, and this is the one place in the store where
/// that is the right answer rather than an unfixed hardcoding. Everywhere else a stored index
/// drops to the id family's `Index` word, because what it addresses is one-per-id and so its
/// population is bounded by the id capacity — [`ClassData::min_row`] is the pattern: one pool
/// row per class, so a row number cannot outgrow `T::Index`.
///
/// The child pool has no such bound. Its length is the *sum of arities* over every
/// variable-arity node, which no single population bounds: `G::Index` bounds the node count,
/// and nothing at all bounds the per-node arity. Narrowing these two words to `G::Index`
/// would therefore not track a width — it would install a fresh capacity cap at
/// `G::Index::MAX` children *in total*, reachable at the 31-bit config with a few large AC
/// terms, which is exactly the class of cap this store is being audited to remove. Pointer
/// width is the honest width for an offset into a pool whose population is `Σ arity`.
///
/// The size is asserted below, so this choice is priced rather than assumed: two `usize`
/// words are what put the node at 32 bytes.
///
/// [`ClassData::min_row`]: crate::classes::ClassData::min_row
#[derive(Clone, Copy, Debug)]
pub struct VariableArityNode<G: DenseId, O: DenseId> {
    pub global_id: G::Repr,
    pub op: O::Repr,
    /// Inclusive start of this node's span in the child pool. `usize`, not `G::Index` — see
    /// the type doc: the pool's population is `Σ arity`, which the id capacity does not bound.
    pub start: usize,
    /// Exclusive end of this node's span in the child pool. `usize` for the same reason as
    /// [`start`](Self::start).
    pub end: usize,
    pub flags: u8,
}

// Filler for `resize_default` during restore; never observed. Routes ids
// through `make`/`into_repr` so the niche bit is cleared (no raw-Repr fabric).
impl<G: DenseId, O: DenseId> Default for VariableArityNode<G, O> {
    fn default() -> Self {
        Self::make(G::default(), O::default(), 0, 0)
    }
}

impl<G: DenseId, O: DenseId> VariableArityNode<G, O> {
    #[inline]
    pub fn make(global_id: G, op: O, start: usize, end: usize) -> Self {
        Self {
            global_id: global_id.into_repr(),
            op: op.into_repr(),
            start,
            end,
            flags: 0,
        }
    }

    #[inline]
    pub fn global_id(&self) -> G {
        G::from_repr(&self.global_id)
    }

    #[inline]
    pub fn op(&self) -> O {
        O::from_repr(&self.op)
    }

    #[inline]
    pub fn has_history(&self) -> bool {
        O::tag(&self.op)
    }

    #[inline]
    pub fn set_history(&mut self) {
        O::set_tag(&mut self.op);
    }

    #[inline]
    pub fn span(&self) -> (usize, usize) {
        (self.start, self.end)
    }

    #[inline]
    pub fn with_end(self, new_end: usize) -> Self {
        Self {
            end: new_end,
            ..self
        }
    }
}

impl<G: DenseId, O: DenseId> Tagged for VariableArityNode<G, O> {
    type Repr = Self;
    #[inline(always)]
    fn into_repr(self) -> Self {
        self
    }
    #[inline(always)]
    fn from_repr(stored: &Self) -> Self {
        let mut v = *stored;
        G::clear_tag(&mut v.global_id);
        O::clear_tag(&mut v.op);
        v
    }
    #[inline(always)]
    fn tag(stored: &Self) -> bool {
        G::tag(&stored.global_id)
    }
    #[inline(always)]
    fn set_tag(stored: &mut Self) {
        G::set_tag(&mut stored.global_id);
    }
    #[inline(always)]
    fn clear_tag(stored: &mut Self) {
        G::clear_tag(&mut stored.global_id);
    }
}

// ---------------------------------------------------------------------------
// LitNode<G, O, V>
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub struct LitNode<G: DenseId, O: DenseId, V: DenseId> {
    pub global_id: G::Repr,
    pub op: O::Repr,
    pub flags: u8,
    pub lit: V,
}

// Filler for `resize_default` during restore; never observed. Routes ids
// through `new`/`into_repr` so the niche bit is cleared (no raw-Repr fabric).
impl<G: DenseId, O: DenseId, V: DenseId> Default for LitNode<G, O, V> {
    fn default() -> Self {
        Self::new(G::default(), O::default(), V::default())
    }
}

impl<G: DenseId, O: DenseId, V: DenseId> LitNode<G, O, V> {
    #[inline]
    pub fn new(global_id: G, op: O, lit: V) -> Self {
        Self {
            global_id: global_id.into_repr(),
            op: op.into_repr(),
            flags: 0,
            lit,
        }
    }

    #[inline]
    pub fn global_id(&self) -> G {
        G::from_repr(&self.global_id)
    }

    #[inline]
    pub fn op(&self) -> O {
        O::from_repr(&self.op)
    }

    #[inline]
    pub fn has_history(&self) -> bool {
        O::tag(&self.op)
    }

    #[inline]
    pub fn set_history(&mut self) {
        O::set_tag(&mut self.op);
    }

    #[inline]
    pub fn content_hash(&self) -> u64
    where
        O: Hash,
        V: Hash,
    {
        let mut h = rapidhash::fast::RapidHasher::default();
        self.op().hash(&mut h);
        self.lit.hash(&mut h);
        h.finish()
    }

    #[inline]
    pub fn content_eq(&self, other: &Self) -> bool
    where
        O: PartialEq,
        V: PartialEq,
    {
        self.op() == other.op() && self.lit == other.lit
    }
}

impl<G: DenseId, O: DenseId, V: DenseId> Tagged for LitNode<G, O, V> {
    type Repr = Self;
    #[inline(always)]
    fn into_repr(self) -> Self {
        self
    }
    #[inline(always)]
    fn from_repr(stored: &Self) -> Self {
        let mut v = *stored;
        G::clear_tag(&mut v.global_id);
        O::clear_tag(&mut v.op);
        v
    }
    #[inline(always)]
    fn tag(stored: &Self) -> bool {
        G::tag(&stored.global_id)
    }
    #[inline(always)]
    fn set_tag(stored: &mut Self) {
        G::set_tag(&mut stored.global_id);
    }
    #[inline(always)]
    fn clear_tag(stored: &mut Self) {
        G::clear_tag(&mut stored.global_id);
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::id::{ENodeId, OpId};
    use crate::nodes::LitValId;

    #[test]
    fn fixed_arity_sizes() {
        use std::mem::size_of;
        // +4 bytes vs no-flags: u8 flags rounds up to u32 alignment
        assert_eq!(size_of::<FixedArityNode<ENodeId, OpId, 0>>(), 12);
        assert_eq!(size_of::<FixedArityNode<ENodeId, OpId, 1>>(), 16);
        assert_eq!(size_of::<FixedArityNode<ENodeId, OpId, 2>>(), 20);
        assert_eq!(size_of::<FixedArityNode<ENodeId, OpId, 3>>(), 24);
    }

    #[test]
    fn variable_arity_size() {
        use std::mem::size_of;
        // +8 bytes vs no-flags: u8 flags rounds up to usize alignment
        assert_eq!(size_of::<VariableArityNode<ENodeId, OpId>>(), 32);
    }

    #[test]
    fn lit_node_size() {
        use std::mem::size_of;
        assert_eq!(size_of::<LitNode<ENodeId, OpId, LitValId>>(), 16);
    }

    #[test]
    fn tagged_roundtrip() {
        type N = FixedArityNode<ENodeId, OpId, 2>;
        let node = N::new(
            ENodeId::new(42),
            OpId::new(5),
            [ENodeId::new(1), ENodeId::new(2)],
        );
        let mut stored = node.into_repr();
        assert!(!N::tag(&stored));

        N::set_tag(&mut stored);
        assert!(N::tag(&stored));

        let clean = N::from_repr(&stored);
        assert_eq!(clean.global_id(), ENodeId::new(42));
        assert_eq!(clean.op(), OpId::new(5));
        assert_eq!(clean.children, [ENodeId::new(1), ENodeId::new(2)]);
        assert!(!clean.has_history());
    }

    #[test]
    fn history_flag() {
        let mut node = FixedArityNode::<ENodeId, OpId, 1>::new(
            ENodeId::new(10),
            OpId::new(3),
            [ENodeId::new(7)],
        );
        assert!(!node.has_history());
        node.set_history();
        assert!(node.has_history());
        assert_eq!(node.op(), OpId::new(3));
    }

    #[test]
    fn content_eq_ignores_global_id() {
        let a = FixedArityNode::<ENodeId, OpId, 0>::new(ENodeId::new(0), OpId::new(1), []);
        let b = FixedArityNode::<ENodeId, OpId, 0>::new(ENodeId::new(99), OpId::new(1), []);
        assert!(a.content_eq(&b));
    }

    #[test]
    fn history_flag_independent_of_capture() {
        type N = FixedArityNode<ENodeId, OpId, 1>;
        let mut node = N::new(ENodeId::new(10), OpId::new(3), [ENodeId::new(7)]);
        node.set_history();
        let mut stored = node;
        N::set_tag(&mut stored); // set capture tag on global_id MSB

        // Both flags set in stored repr
        assert!(stored.has_history()); // op MSB
        assert!(N::tag(&stored)); // global_id MSB

        // from_repr clears capture tag but op tag is also cleared (both use MSB)
        // The clean node has neither flag — that's correct.
        // In practice, has_history is only read on raw stored values from VecI::get.
        let clean = N::from_repr(&stored);
        assert_eq!(clean.op(), OpId::new(3));
        assert_eq!(clean.global_id(), ENodeId::new(10));
        assert_eq!(clean.children, [ENodeId::new(7)]);
    }

    // prod-parity: production exposed `ENodeId::from_raw_unchecked` to fabricate
    // an id with the stolen MSB set, then asserted `Eq`/`Ord`/`Hash` masked that
    // bit off ("MSB-oblivious"). The verified crate takes a different, stronger
    // route: a clean id carries a `#[verifier::type_invariant]` that the MSB is
    // ALWAYS clear, so a dirty id cannot be constructed at all — there is no
    // `from_raw_unchecked`, and the masking the test checked is unnecessary
    // because the case it guards against is unrepresentable. The residual
    // property (equal clean ids compare/ hash equal) is what remains testable.
    #[test]
    fn dense_id_clean_ids_compare_and_hash_by_value() {
        let a = ENodeId::new(42);
        let b = ENodeId::new(42);
        assert_eq!(a, b);
        assert_eq!(a.cmp(&b), core::cmp::Ordering::Equal);

        use core::hash::{Hash, Hasher};
        let hash = |v: ENodeId| {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            v.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash(a), hash(b));
    }
}
