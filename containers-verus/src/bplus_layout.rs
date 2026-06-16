// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! `NodeLayout`: the packed B+tree node geometry, generic over node size and
//! word width, matching production's `NodeLayout` trait + `impl_layout!` family.
//!
//! Production packs a B+tree node into one cache-aligned struct
//! `{ flags: u8, count: u8, _pad, data: [Word; DATA_LEN], link }`, where the
//! `flags` byte holds **two stolen bits**: bit 0 (`FLAG_LEAF`) distinguishes
//! leaf from internal, and bit 1 (`FLAG_TAG`) is the semi-persistence capture
//! bit. The arena is an [`InlineStore`](crate::inline_store)-backed `VecI`, so
//! the node must be [`Tagged`]: the capture bit is stolen from the node itself.
//!
//! We encode that bit-steal exactly like [`DenseId31`](crate::dense_id), by
//! splitting the *clean value* from the *stored repr* (production uses one type
//! for both, which unverified Rust can do but the `Tagged` niche contract
//! cannot — `value_of(into_repr(self)) == self` would force the value and the
//! tag-set repr to be the same bit pattern):
//!   - the **value** `NodeNN` carries `is_leaf` as a plain `bool` and the keys
//!     / children; it has no flag bits, so nothing leaks. This is `L::Node`,
//!     the type the arena's abstract `view()` yields and the tree proof reasons
//!     over.
//!   - the **repr** `NodeReprNN` is the byte-packed `{ flags, count, data,
//!     link }`. `flags` bit 0 = leaf, bit 1 = capture tag, bits 2..7 unused.
//!     The niche predicate `repr_wf` pins those unused bits to 0 (so two reprs
//!     with the same value+tag are equal — the extensionality axiom), `value_of`
//!     masks the tag out, and `tag_of` reads bit 1.
//!
//! All bit-stealing is confined to the `Tagged` impl bridging value and repr;
//! the `NodeLayout` accessors read clean value fields and touch no flag bits.
//! The structural B+tree proof in [`bplus`](crate::bplus) is generic over
//! `L: NodeLayout`, written once and instantiated per layout.
//!
//! Build order: this step lands the trait and the base layout `Layout64U32`
//! (u32 word, u32 arena index, the e-graph's default), including its `Tagged`
//! niche; the other five production layouts follow with the same shape.

use vstd::prelude::*;

use crate::index_like::IndexLike;
use crate::tagged::Tagged;

verus! {

/// Compile-time node geometry, generic over word/arena width. Mirrors
/// production's `NodeLayout`. The node value is [`Tagged`] (capture bit stolen
/// into its packed repr's `flags` byte), so an `InlineStore`-backed arena makes
/// the tree semi-persistent. The structural B+tree proof is generic over this.
pub trait NodeLayout: Sized {
    /// Key storage word (`u32` or `u64`; equals the key type's `DenseId::Index`).
    type Word: IndexLike;
    /// Arena index type (`u32` for u32-word layouts, `usize` for u64-word).
    type ArenaIdx: IndexLike;
    /// The clean node value (`L::Node`). `Tagged` supplies the capture bit via
    /// its packed `Repr`, so the arena can be `InlineStore`-backed.
    type Node: Copy + Tagged;

    // -- geometry (spec + exec) --

    /// Max keys in a leaf (`= DATA_LEN`).
    spec fn leaf_cap_spec() -> nat;
    /// Max separators in an internal node (`= DATA_LEN / 2`).
    spec fn key_cap_spec() -> nat;
    /// Backing-array length (`= LEAF_CAP = 2 * KEY_CAP`).
    spec fn data_len_spec() -> nat;

    fn leaf_cap() -> (c: usize)
        ensures c as nat == Self::leaf_cap_spec();

    fn key_cap() -> (c: usize)
        ensures c as nat == Self::key_cap_spec();

    // -- logical views of a node (the refinement targets) --

    spec fn is_leaf_spec(n: Self::Node) -> bool;
    spec fn count_spec(n: Self::Node) -> nat;

    /// `data[0..count]` as a sequence of words (leaf keys / internal separators).
    spec fn keys_view(n: Self::Node) -> Seq<Self::Word>;

    /// Arena index of internal child `i` (`0 <= i <= count`), as a nat.
    spec fn child_view(n: Self::Node, i: int) -> nat;

    /// The `link` field, as a nat (leaf: next-leaf idx; internal: last child).
    spec fn link_view(n: Self::Node) -> nat;

    /// Node-local well-formedness: `count` fits its node kind's capacity. The
    /// accessors rely on this for in-bounds array indexing.
    spec fn node_wf(n: Self::Node) -> bool;

    // -- exec accessors, each proven to refine the views above --

    fn is_leaf(n: &Self::Node) -> (b: bool)
        ensures b == Self::is_leaf_spec(*n);

    fn count(n: &Self::Node) -> (c: usize)
        ensures c as nat == Self::count_spec(*n);

    /// `keys_view()[i]`, read from the packed array.
    fn key(n: &Self::Node, i: usize) -> (k: Self::Word)
        requires Self::node_wf(*n), i < Self::count_spec(*n),
        ensures k == Self::keys_view(*n)[i as int];

    /// `child_view(i)`, read from the packed array (internal nodes only).
    fn child(n: &Self::Node, i: usize) -> (c: Self::ArenaIdx)
        requires
            Self::node_wf(*n),
            !Self::is_leaf_spec(*n),
            i <= Self::count_spec(*n),
        ensures c.as_nat() == Self::child_view(*n, i as int);

    fn link(n: &Self::Node) -> (l: Self::ArenaIdx)
        ensures l.as_nat() == Self::link_view(*n);

    // -- construction --

    /// A fresh empty leaf.
    fn new_leaf() -> (n: Self::Node)
        ensures
            Self::is_leaf_spec(n),
            Self::count_spec(n) == 0,
            Self::node_wf(n);

    // -- proof glue --

    /// `node_wf` bounds `count` by the leaf capacity (the loosest bound; an
    /// internal node's `key_cap` is smaller). Lets generic code index keys.
    proof fn lemma_node_wf_count(n: Self::Node)
        requires Self::node_wf(n),
        ensures Self::count_spec(n) <= Self::leaf_cap_spec();

    /// The geometry identity `data_len = leaf_cap = 2 * key_cap`.
    proof fn lemma_geometry()
        ensures
            Self::data_len_spec() == Self::leaf_cap_spec(),
            Self::leaf_cap_spec() == 2 * Self::key_cap_spec();
}

// ===========================================================================
// Layout64U32 — the base layout (u32 word, u32 arena), bit-exact with
// production's `impl_layout!(Layout64U32, BPlusNode64U32, u32, u32, 14, 14, 7,
// 8, 10, 64)` and `define_node!(BPlusNode64U32, 64, u32, 14, u32)`.
// DATA_LEN = 14, LEAF_CAP = 14, KEY_CAP = 7.
// ===========================================================================

/// `flags` bit 0: set iff the node is a leaf (production `FLAG_LEAF`).
pub spec const FLAG_LEAF: u8 = 0x01;
/// `flags` bit 1: the semi-persistence capture tag (production `FLAG_TAG`).
pub spec const FLAG_TAG: u8 = 0x02;
/// The used-bit mask of `flags` (bits 0 and 1); bits 2..7 must be 0 in a repr.
pub spec const FLAG_USED: u8 = 0x03;

/// The clean node *value* for `Layout64U32`: `is_leaf` as a plain `bool`, the
/// key/child backing array, and the link. No flag bits, so the capture tag
/// cannot leak into it. This is `Layout64U32::Node`.
#[derive(Copy)]
pub struct Node64U32 {
    pub is_leaf: bool,
    pub count: usize,
    pub data: [u32; 14],
    pub link: u32,
}

impl Clone for Node64U32 {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

/// The stored *repr* for `Layout64U32`, byte-packed exactly like production's
/// `BPlusNode64U32`: `flags` bit 0 = leaf, bit 1 = capture tag, bits 2..7
/// unused (pinned to 0 by `repr_wf`). (`_pad` carries no logical content and is
/// omitted.)
#[derive(Copy)]
pub struct NodeRepr64U32 {
    pub flags: u8,
    pub count: usize,
    pub data: [u32; 14],
    pub link: u32,
}

impl Clone for NodeRepr64U32 {
    fn clone(&self) -> (r: Self)
        ensures r == *self,
    {
        *self
    }
}

// -- Tagged: the value/repr bit-steal, same shape as DenseId31 vs u32. --

impl Tagged for Node64U32 {
    type Repr = NodeRepr64U32;

    closed spec fn value_of(r: NodeRepr64U32) -> Node64U32 {
        Node64U32 {
            is_leaf: (r.flags & FLAG_LEAF) != 0,
            count: r.count,
            data: r.data,
            link: r.link,
        }
    }

    open spec fn tag_of(r: NodeRepr64U32) -> bool {
        (r.flags & FLAG_TAG) != 0
    }

    /// Niche: only bits 0 and 1 of `flags` are used; the rest are 0. This is
    /// what makes the encoding injective (extensionality below).
    open spec fn repr_wf(r: NodeRepr64U32) -> bool {
        (r.flags & 0xfcu8) == 0
    }

    proof fn lemma_repr_extensional(r1: NodeRepr64U32, r2: NodeRepr64U32) {
        // value_of equal: bit 0 of flags equal, and count/data/link equal.
        // tag_of equal: bit 1 of flags equal. repr_wf: bits 2..7 are 0 in both.
        // So all 8 bits of flags agree, hence the reprs are equal.
        let f1 = r1.flags;
        let f2 = r2.flags;
        assert(((f1 & FLAG_LEAF) != 0) == ((f2 & FLAG_LEAF) != 0));
        assert(((f1 & FLAG_TAG) != 0) == ((f2 & FLAG_TAG) != 0));
        assert(forall|x: u8, y: u8|
            #![auto]
            (x & 0xfcu8) == 0 && (y & 0xfcu8) == 0
                && (((x & 0x01u8) != 0) == ((y & 0x01u8) != 0))
                && (((x & 0x02u8) != 0) == ((y & 0x02u8) != 0))
                ==> x == y) by (bit_vector);
        assert(r1.flags == r2.flags);
        assert(r1.data == r2.data);
    }

    fn into_repr(self) -> (r: NodeRepr64U32) {
        // flags = leaf bit only (tag clear, junk bits clear).
        let flags: u8 = if self.is_leaf { FLAG_LEAF_EXEC } else { 0u8 };
        assert((0x01u8 & 0xfcu8) == 0 && (0u8 & 0xfcu8) == 0) by (bit_vector);
        assert((0x01u8 & 0x01u8) != 0 && (0u8 & 0x01u8) == 0) by (bit_vector);
        assert((0x01u8 & 0x02u8) == 0 && (0u8 & 0x02u8) == 0) by (bit_vector);
        NodeRepr64U32 { flags, count: self.count, data: self.data, link: self.link }
    }

    fn from_repr(r: &NodeRepr64U32) -> (v: Node64U32) {
        Node64U32 {
            is_leaf: (r.flags & 0x01u8) != 0,
            count: r.count,
            data: r.data,
            link: r.link,
        }
    }

    fn tag(r: &NodeRepr64U32) -> (b: bool) {
        (r.flags & 0x02u8) != 0
    }

    fn set_tag(r: &mut NodeRepr64U32) {
        // OR in bit 1: leaf bit and junk bits unchanged, tag set, niche kept.
        assert(forall|x: u8|
            #![auto]
            ((x | 0x02u8) & 0xfcu8) == (x & 0xfcu8)
                && ((x | 0x02u8) & 0x01u8) == (x & 0x01u8)
                && ((x | 0x02u8) & 0x02u8) != 0) by (bit_vector);
        r.flags = r.flags | 0x02u8;
    }

    fn clear_tag(r: &mut NodeRepr64U32) {
        // AND off bit 1: leaf bit and junk bits unchanged, tag clear.
        assert(forall|x: u8|
            #![auto]
            ((x & 0xfdu8) & 0xfcu8) == (x & 0xfcu8)
                && ((x & 0xfdu8) & 0x01u8) == (x & 0x01u8)
                && ((x & 0xfdu8) & 0x02u8) == 0) by (bit_vector);
        r.flags = r.flags & 0xfdu8;
    }
}

/// Exec mirror of `FLAG_LEAF` (spec consts are not exec-usable).
pub const FLAG_LEAF_EXEC: u8 = 0x01;

/// The `Layout64U32` geometry marker.
pub struct Layout64U32;

impl NodeLayout for Layout64U32 {
    type Word = u32;
    type ArenaIdx = u32;
    type Node = Node64U32;

    open spec fn leaf_cap_spec() -> nat { 14 }
    open spec fn key_cap_spec() -> nat { 7 }
    open spec fn data_len_spec() -> nat { 14 }

    fn leaf_cap() -> (c: usize) { 14 }
    fn key_cap() -> (c: usize) { 7 }

    open spec fn is_leaf_spec(n: Node64U32) -> bool { n.is_leaf }
    open spec fn count_spec(n: Node64U32) -> nat { n.count as nat }

    open spec fn keys_view(n: Node64U32) -> Seq<u32> {
        Seq::new(n.count as nat, |i: int| n.data[i])
    }

    open spec fn child_view(n: Node64U32, i: int) -> nat {
        if i < 7 {
            n.data[7 + i] as nat
        } else {
            n.link as nat
        }
    }

    open spec fn link_view(n: Node64U32) -> nat {
        n.link as nat
    }

    open spec fn node_wf(n: Node64U32) -> bool {
        if n.is_leaf {
            n.count <= 14
        } else {
            n.count <= 7
        }
    }

    fn is_leaf(n: &Node64U32) -> (b: bool) {
        n.is_leaf
    }

    fn count(n: &Node64U32) -> (c: usize) {
        n.count
    }

    fn key(n: &Node64U32, i: usize) -> (k: u32) {
        n.data[i]
    }

    fn child(n: &Node64U32, i: usize) -> (c: u32) {
        if i < 7 {
            n.data[7 + i]
        } else {
            n.link
        }
    }

    fn link(n: &Node64U32) -> (l: u32) {
        n.link
    }

    fn new_leaf() -> (n: Node64U32) {
        Node64U32 { is_leaf: true, count: 0, data: [0; 14], link: u32::MAX }
    }

    proof fn lemma_node_wf_count(n: Node64U32) {}

    proof fn lemma_geometry() {}
}

// ===========================================================================
// Generic sanity check: the trait is usable by proof-bearing generic code.
// ===========================================================================

/// First key of a non-empty node, via the generic trait. Witnesses that the
/// refinement `ensures` compose: the exec read equals the logical view.
pub fn first_key<L: NodeLayout>(n: &L::Node) -> (k: L::Word)
    requires L::node_wf(*n), L::count_spec(*n) > 0,
    ensures k == L::keys_view(*n)[0],
{
    L::key(n, 0)
}

} // verus!
