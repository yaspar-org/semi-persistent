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
//!     link }`. `flags` bit 0 = leaf, bit 1 = capture tag, bits 2..7 a niche
//!     pinned to 0 by `repr_wf`; `value_of` masks the tag out, `tag_of` reads
//!     bit 1.
//!
//! All bit-stealing is confined to the `Tagged` impl bridging value and repr;
//! the `NodeLayout` accessors read clean value fields and touch no flag bits.
//! The structural B+tree proof in [`bplus`](crate::bplus) is generic over
//! `L: NodeLayout`, written once and instantiated per layout.
//!
//! All six production layouts are stamped out by the `gen_layout_u32!` /
//! `gen_layout_u64!` macros below, bit-exact with production's `impl_layout!`:
//!
//! | layout       | word | arena | data_len | leaf_cap | key_cap |
//! |--------------|------|-------|----------|----------|---------|
//! | Layout64U32  | u32  | u32   | 14       | 14       | 7       |
//! | Layout128U32 | u32  | u32   | 30       | 30       | 14      |
//! | Layout256U32 | u32  | u32   | 62       | 62       | 30      |
//! | Layout128U64 | u64  | usize | 14       | 14       | 6       |
//! | Layout256U64 | u64  | usize | 30       | 30       | 14      |
//! | Layout512U64 | u64  | usize | 62       | 62       | 30      |
//!
//! The u32 layouts verify the `child` accessor outright (word == arena == u32,
//! no cast). The u64 layouts' `child` casts `u64 -> usize`; that one accessor
//! is `external_body`, matching the crate's existing treatment of the u64
//! `IndexLike::as_usize` cast (sound on 64-bit hosts; 32-bit is feature-gated).
//!
//! The layout-stamping macros live outside `verus! {}` (a `macro_rules!` that
//! emits `spec`/`ensures` syntax must, since the `verus!` proc-macro cannot
//! parse a nested `macro_rules!` definition); each invocation emits its own
//! `verus! {}` block.

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
    /// Max separators in an internal node.
    spec fn key_cap_spec() -> nat;
    /// Backing-array length (`= LEAF_CAP`; internal nodes use `2 * KEY_CAP <=
    /// DATA_LEN` of it).
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

    /// The geometry facts: the backing array holds a full leaf, and an internal
    /// node's separators + in-array children (`2 * key_cap`) fit within it.
    proof fn lemma_geometry()
        ensures
            Self::data_len_spec() == Self::leaf_cap_spec(),
            2 * Self::key_cap_spec() <= Self::data_len_spec();

    /// The arena index type can address a useful arena, and a leaf holds at
    /// least one key. Both hold for every real layout (u32/usize arena;
    /// `leaf_cap` 14..62). Lets the tree push a root node without overflow and
    /// gives a non-degenerate capacity.
    proof fn lemma_arena_capacity()
        ensures
            1 <= Self::leaf_cap_spec(),
            Self::leaf_cap_spec() < <Self::ArenaIdx as IndexLike>::max_nat();
}

/// `flags` bit 0: set iff the node is a leaf (production `FLAG_LEAF`).
pub spec const FLAG_LEAF: u8 = 0x01;
/// `flags` bit 1: the semi-persistence capture tag (production `FLAG_TAG`).
pub spec const FLAG_TAG: u8 = 0x02;
/// Exec mirror of `FLAG_LEAF` (spec consts are not exec-usable).
pub const FLAG_LEAF_EXEC: u8 = 0x01;

} // verus!

// ===========================================================================
// Layout generators. Each stamps a (value, repr, Tagged, NodeLayout) bundle
// bit-exact with production's `impl_layout!`. `gen_layout_u32!` covers the
// u32-word/u32-arena layouts (child needs no cast); `gen_layout_u64!` covers
// the u64-word/usize-arena layouts (child casts u64->usize). Defined outside
// `verus! {}`; each invocation emits its own block.
// ===========================================================================

macro_rules! gen_layout_u32 {
    ($layout:ident, $node:ident, $repr:ident, $data_len:literal, $leaf_cap:literal, $key_cap:literal) => {
        verus! {

        #[derive(Copy)]
        pub struct $node {
            pub is_leaf: bool,
            pub count: usize,
            pub data: [u32; $data_len],
            pub link: u32,
        }

        impl Clone for $node {
            fn clone(&self) -> (r: Self) ensures r == *self { *self }
        }

        #[derive(Copy)]
        pub struct $repr {
            pub flags: u8,
            pub count: usize,
            pub data: [u32; $data_len],
            pub link: u32,
        }

        impl Clone for $repr {
            fn clone(&self) -> (r: Self) ensures r == *self { *self }
        }

        impl Tagged for $node {
            type Repr = $repr;

            closed spec fn value_of(r: $repr) -> $node {
                $node { is_leaf: (r.flags & FLAG_LEAF) != 0, count: r.count, data: r.data, link: r.link }
            }
            open spec fn tag_of(r: $repr) -> bool { (r.flags & FLAG_TAG) != 0 }
            open spec fn repr_wf(r: $repr) -> bool { (r.flags & 0xfcu8) == 0 }

            proof fn lemma_repr_extensional(r1: $repr, r2: $repr) {
                let f1 = r1.flags; let f2 = r2.flags;
                assert(((f1 & FLAG_LEAF) != 0) == ((f2 & FLAG_LEAF) != 0));
                assert(((f1 & FLAG_TAG) != 0) == ((f2 & FLAG_TAG) != 0));
                assert(forall|x: u8, y: u8| #![auto]
                    (x & 0xfcu8) == 0 && (y & 0xfcu8) == 0
                        && (((x & 0x01u8) != 0) == ((y & 0x01u8) != 0))
                        && (((x & 0x02u8) != 0) == ((y & 0x02u8) != 0))
                        ==> x == y) by (bit_vector);
                assert(r1.flags == r2.flags);
                assert(r1.data == r2.data);
            }

            fn into_repr(self) -> (r: $repr) {
                let flags: u8 = if self.is_leaf { FLAG_LEAF_EXEC } else { 0u8 };
                assert((0x01u8 & 0xfcu8) == 0 && (0u8 & 0xfcu8) == 0) by (bit_vector);
                assert((0x01u8 & 0x01u8) != 0 && (0u8 & 0x01u8) == 0) by (bit_vector);
                assert((0x01u8 & 0x02u8) == 0 && (0u8 & 0x02u8) == 0) by (bit_vector);
                $repr { flags, count: self.count, data: self.data, link: self.link }
            }

            fn from_repr(r: &$repr) -> (v: $node) {
                $node { is_leaf: (r.flags & 0x01u8) != 0, count: r.count, data: r.data, link: r.link }
            }

            fn tag(r: &$repr) -> (b: bool) { (r.flags & 0x02u8) != 0 }

            fn set_tag(r: &mut $repr) {
                assert(forall|x: u8| #![auto]
                    ((x | 0x02u8) & 0xfcu8) == (x & 0xfcu8) && ((x | 0x02u8) & 0x01u8) == (x & 0x01u8)
                        && ((x | 0x02u8) & 0x02u8) != 0) by (bit_vector);
                r.flags = r.flags | 0x02u8;
            }

            fn clear_tag(r: &mut $repr) {
                assert(forall|x: u8| #![auto]
                    ((x & 0xfdu8) & 0xfcu8) == (x & 0xfcu8) && ((x & 0xfdu8) & 0x01u8) == (x & 0x01u8)
                        && ((x & 0xfdu8) & 0x02u8) == 0) by (bit_vector);
                r.flags = r.flags & 0xfdu8;
            }
        }

        pub struct $layout;

        impl NodeLayout for $layout {
            type Word = u32;
            type ArenaIdx = u32;
            type Node = $node;

            open spec fn leaf_cap_spec() -> nat { $leaf_cap }
            open spec fn key_cap_spec() -> nat { $key_cap }
            open spec fn data_len_spec() -> nat { $data_len }

            fn leaf_cap() -> (c: usize) { $leaf_cap }
            fn key_cap() -> (c: usize) { $key_cap }

            open spec fn is_leaf_spec(n: $node) -> bool { n.is_leaf }
            open spec fn count_spec(n: $node) -> nat { n.count as nat }

            open spec fn keys_view(n: $node) -> Seq<u32> {
                Seq::new(n.count as nat, |i: int| n.data[i])
            }
            open spec fn child_view(n: $node, i: int) -> nat {
                if i < $key_cap { n.data[$key_cap + i] as nat } else { n.link as nat }
            }
            open spec fn link_view(n: $node) -> nat { n.link as nat }
            open spec fn node_wf(n: $node) -> bool {
                if n.is_leaf { n.count <= $leaf_cap } else { n.count <= $key_cap }
            }

            fn is_leaf(n: &$node) -> (b: bool) { n.is_leaf }
            fn count(n: &$node) -> (c: usize) { n.count }
            fn key(n: &$node, i: usize) -> (k: u32) { n.data[i] }
            fn child(n: &$node, i: usize) -> (c: u32) {
                if i < $key_cap { n.data[$key_cap + i] } else { n.link }
            }
            fn link(n: &$node) -> (l: u32) { n.link }
            fn new_leaf() -> (n: $node) {
                $node { is_leaf: true, count: 0, data: [0; $data_len], link: u32::MAX }
            }
            proof fn lemma_node_wf_count(n: $node) {}
            proof fn lemma_geometry() {}
            proof fn lemma_arena_capacity() {}
        }

        } // verus!
    };
}

macro_rules! gen_layout_u64 {
    ($layout:ident, $node:ident, $repr:ident, $data_len:literal, $leaf_cap:literal, $key_cap:literal) => {
        verus! {

        #[derive(Copy)]
        pub struct $node {
            pub is_leaf: bool,
            pub count: usize,
            pub data: [u64; $data_len],
            pub link: usize,
        }

        impl Clone for $node {
            fn clone(&self) -> (r: Self) ensures r == *self { *self }
        }

        #[derive(Copy)]
        pub struct $repr {
            pub flags: u8,
            pub count: usize,
            pub data: [u64; $data_len],
            pub link: usize,
        }

        impl Clone for $repr {
            fn clone(&self) -> (r: Self) ensures r == *self { *self }
        }

        impl Tagged for $node {
            type Repr = $repr;

            closed spec fn value_of(r: $repr) -> $node {
                $node { is_leaf: (r.flags & FLAG_LEAF) != 0, count: r.count, data: r.data, link: r.link }
            }
            open spec fn tag_of(r: $repr) -> bool { (r.flags & FLAG_TAG) != 0 }
            open spec fn repr_wf(r: $repr) -> bool { (r.flags & 0xfcu8) == 0 }

            proof fn lemma_repr_extensional(r1: $repr, r2: $repr) {
                let f1 = r1.flags; let f2 = r2.flags;
                assert(((f1 & FLAG_LEAF) != 0) == ((f2 & FLAG_LEAF) != 0));
                assert(((f1 & FLAG_TAG) != 0) == ((f2 & FLAG_TAG) != 0));
                assert(forall|x: u8, y: u8| #![auto]
                    (x & 0xfcu8) == 0 && (y & 0xfcu8) == 0
                        && (((x & 0x01u8) != 0) == ((y & 0x01u8) != 0))
                        && (((x & 0x02u8) != 0) == ((y & 0x02u8) != 0))
                        ==> x == y) by (bit_vector);
                assert(r1.flags == r2.flags);
                assert(r1.data == r2.data);
            }

            fn into_repr(self) -> (r: $repr) {
                let flags: u8 = if self.is_leaf { FLAG_LEAF_EXEC } else { 0u8 };
                assert((0x01u8 & 0xfcu8) == 0 && (0u8 & 0xfcu8) == 0) by (bit_vector);
                assert((0x01u8 & 0x01u8) != 0 && (0u8 & 0x01u8) == 0) by (bit_vector);
                assert((0x01u8 & 0x02u8) == 0 && (0u8 & 0x02u8) == 0) by (bit_vector);
                $repr { flags, count: self.count, data: self.data, link: self.link }
            }

            fn from_repr(r: &$repr) -> (v: $node) {
                $node { is_leaf: (r.flags & 0x01u8) != 0, count: r.count, data: r.data, link: r.link }
            }

            fn tag(r: &$repr) -> (b: bool) { (r.flags & 0x02u8) != 0 }

            fn set_tag(r: &mut $repr) {
                assert(forall|x: u8| #![auto]
                    ((x | 0x02u8) & 0xfcu8) == (x & 0xfcu8) && ((x | 0x02u8) & 0x01u8) == (x & 0x01u8)
                        && ((x | 0x02u8) & 0x02u8) != 0) by (bit_vector);
                r.flags = r.flags | 0x02u8;
            }

            fn clear_tag(r: &mut $repr) {
                assert(forall|x: u8| #![auto]
                    ((x & 0xfdu8) & 0xfcu8) == (x & 0xfcu8) && ((x & 0xfdu8) & 0x01u8) == (x & 0x01u8)
                        && ((x & 0xfdu8) & 0x02u8) == 0) by (bit_vector);
                r.flags = r.flags & 0xfdu8;
            }
        }

        pub struct $layout;

        impl NodeLayout for $layout {
            type Word = u64;
            type ArenaIdx = usize;
            type Node = $node;

            open spec fn leaf_cap_spec() -> nat { $leaf_cap }
            open spec fn key_cap_spec() -> nat { $key_cap }
            open spec fn data_len_spec() -> nat { $data_len }

            fn leaf_cap() -> (c: usize) { $leaf_cap }
            fn key_cap() -> (c: usize) { $key_cap }

            open spec fn is_leaf_spec(n: $node) -> bool { n.is_leaf }
            open spec fn count_spec(n: $node) -> nat { n.count as nat }

            open spec fn keys_view(n: $node) -> Seq<u64> {
                Seq::new(n.count as nat, |i: int| n.data[i])
            }
            open spec fn child_view(n: $node, i: int) -> nat {
                if i < $key_cap { n.data[$key_cap + i] as nat } else { n.link as nat }
            }
            open spec fn link_view(n: $node) -> nat { n.link as nat }
            open spec fn node_wf(n: $node) -> bool {
                if n.is_leaf { n.count <= $leaf_cap } else { n.count <= $key_cap }
            }

            fn is_leaf(n: &$node) -> (b: bool) { n.is_leaf }
            fn count(n: &$node) -> (c: usize) { n.count }
            fn key(n: &$node, i: usize) -> (k: u64) { n.data[i] }

            // u64 word -> usize arena index: a value-preserving cast on 64-bit
            // hosts. external_body mirrors the crate's u64 `IndexLike::as_usize`.
            #[verifier::external_body]
            fn child(n: &$node, i: usize) -> (c: usize) {
                if i < $key_cap { n.data[$key_cap + i] as usize } else { n.link }
            }
            fn link(n: &$node) -> (l: usize) { n.link }
            fn new_leaf() -> (n: $node) {
                $node { is_leaf: true, count: 0, data: [0; $data_len], link: usize::MAX }
            }
            proof fn lemma_node_wf_count(n: $node) {}
            proof fn lemma_geometry() {}
            proof fn lemma_arena_capacity() {}
        }

        } // verus!
    };
}

// -- the six production layouts (bit-exact with `impl_layout!`) --

gen_layout_u32!(Layout64U32,  Node64U32,  NodeRepr64U32,  14, 14, 7);
gen_layout_u32!(Layout128U32, Node128U32, NodeRepr128U32, 30, 30, 14);
gen_layout_u32!(Layout256U32, Node256U32, NodeRepr256U32, 62, 62, 30);

gen_layout_u64!(Layout128U64, Node128U64, NodeRepr128U64, 14, 14, 6);
gen_layout_u64!(Layout256U64, Node256U64, NodeRepr256U64, 30, 30, 14);
gen_layout_u64!(Layout512U64, Node512U64, NodeRepr512U64, 62, 62, 30);

verus! {

/// First key of a non-empty node, via the generic trait. Witnesses that the
/// refinement `ensures` compose: the exec read equals the logical view.
pub fn first_key<L: NodeLayout>(n: &L::Node) -> (k: L::Word)
    requires L::node_wf(*n), L::count_spec(*n) > 0,
    ensures k == L::keys_view(*n)[0],
{
    L::key(n, 0)
}

} // verus!
