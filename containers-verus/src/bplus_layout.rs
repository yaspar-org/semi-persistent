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
//! The `data`/`link` fields are read two ways by node kind (decided by
//! `FLAG_LEAF`): a leaf uses `data[0..count]` for its sorted keys and `link` for
//! the next-leaf sibling pointer; an internal node uses `data[0..count]` for
//! separators, `data[KEY_CAP..KEY_CAP+KEY_CAP]` for its first `KEY_CAP`
//! children, and reuses `link` for the last child (index `KEY_CAP`). So `link`
//! is the leaf chain iff leaf, the last-child slot iff internal — never
//! ambiguous. The `child_view`/`link_view` specs and the `child`/`link`
//! accessors model exactly this (`2 * KEY_CAP <= DATA_LEN`, per `lemma_geometry`).
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

// The u64 layouts are compiled only on 64-bit targets (their `IndexLike` impls
// are `#[cfg(target_pointer_width = "64")]`). Pin the word size so Verus knows
// `usize::MAX == u64::MAX`, making the arena-index casts (`usize <-> u64`) value-
// preserving FACTS rather than trusted bodies. `global size_of` is checked
// against the build `--target`, so this is not an unchecked assumption: a
// non-8-byte-usize target fails to verify here rather than silently miscompiling.
global size_of usize == 8;

/// `(v as u64) as nat == v as nat` for a `usize`. The single arena-index cast
/// fact the u64 layouts' arena writes need: they store a `usize` id into a `u64`
/// data slot, and `child_view` reads it back as a nat. Verus proves it directly
/// when `usize::BITS <= 64` (so the widening `usize -> u64` is value-preserving),
/// which holds on every target this crate builds for (32- and 64-bit; the cast
/// is lossless on both). Concentrating the cast reasoning in ONE proven lemma
/// lets `set_internal_child` / `new_internal2` drop their `external_body`.
pub proof fn lemma_usize_u64_roundtrip(v: usize)
    ensures (v as u64) as nat == v as nat,
{
    // size_of::<usize>() == 8 (pinned above) ⟹ usize::MAX == u64::MAX, so
    // v <= u64::MAX and the widening cast is the identity (no truncation).
    lemma_usize_is_u64_wide();
    assert((v as u64) as nat == v as nat) by (nonlinear_arith)
        requires v <= u64::MAX as int;
}

/// `usize::MAX == u64::MAX`, from the pinned `size_of usize == 8`. The single
/// width fact both cast lemmas rest on.
pub proof fn lemma_usize_is_u64_wide()
    ensures usize::MAX as nat == u64::MAX as nat,
{
    vstd::layout::unsigned_int_max_values();
    // usize::MAX == pow2(usize::BITS) - 1, u64::MAX == pow2(64) - 1, and
    // usize::BITS == 8 * size_of::<usize>() == 64.
    assert(usize::BITS == 64);
}

/// `(x as usize) as nat == x as nat` for a `u64`: the NARROWING arena-index cast
/// the u64 layouts' `child` accessor performs (it reads a `u64` data slot and
/// returns a `usize`). Lossless iff `u64::MAX <= usize::MAX`, i.e. `usize` is
/// 64-bit — which is exactly the 64-bit-host assumption the u64 layouts already
/// declare (32-bit is feature-gated; see the module header). Verus checks it
/// against the build `--target`, so on a 64-bit build it is a proof, not an
/// axiom; the cast trust is thereby pinned to the target width, not scattered.
pub proof fn lemma_u64_usize_roundtrip(x: u64)
    ensures (x as usize) as nat == x as nat,
{
    lemma_usize_is_u64_wide();  // usize::MAX == u64::MAX, so x <= usize::MAX
    assert((x as usize) as nat == x as nat) by (nonlinear_arith)
        requires x <= usize::MAX as int;
}

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

    /// Arena index of internal child `i` (`0 <= i <= count`), as a nat. The
    /// first `key_cap` children pack into `data[key_cap + i]` (which is why
    /// `2 * key_cap <= data_len`); the last child, index `key_cap`, reuses the
    /// `link` field (production's `internal_child`: `if i < KEY_CAP {
    /// data[KEY_CAP + i] } else { link }`). The overload of `link` is
    /// unambiguous — it is the last-child slot iff the node is internal, the
    /// leaf sibling pointer iff it is a leaf (decided by `is_leaf_spec`).
    spec fn child_view(n: Self::Node, i: int) -> nat;

    /// The `link` field, as a nat. Leaf: the next-leaf arena index (the sibling
    /// chain, NIL at the last leaf). Internal: the last child's arena index
    /// (child index `key_cap`) — see `child_view`.
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

    /// `child_view(i)`, read from the packed array (internal nodes only). `i`
    /// ranges over `0 ..= count` (one more child than separators); `i == count
    /// <= key_cap` may be the `link`-held last child.
    fn child(n: &Self::Node, i: usize) -> (c: Self::ArenaIdx)
        requires
            Self::node_wf(*n),
            !Self::is_leaf_spec(*n),
            i <= Self::count_spec(*n),
        ensures c.as_nat() == Self::child_view(*n, i as int);

    fn link(n: &Self::Node) -> (l: Self::ArenaIdx)
        ensures l.as_nat() == Self::link_view(*n);

    // -- construction --

    /// A fresh empty leaf. Its `link` is NIL (`max_nat - 1`, the
    /// `u32::MAX`/`usize::MAX` sentinel), so a single-leaf tree's leaf-link
    /// chain terminates at it (clause 5).
    fn new_leaf() -> (n: Self::Node)
        ensures
            Self::is_leaf_spec(n),
            Self::count_spec(n) == 0,
            Self::node_wf(n),
            Self::link_view(n) == (<Self::ArenaIdx as IndexLike>::max_nat() - 1);

    // -- mutation (M3+) --

    /// Insert `w` into a leaf at sorted position `pos`, shifting `[pos..count)`
    /// up by one. The leaf must have room (`count < leaf_cap`). Refines the
    /// logical key view by `Seq::insert`: `keys_view' == keys_view.insert(pos,
    /// w)`, `count' == count + 1`, still a leaf, still `node_wf`. Production's
    /// `data_mut(&mut leaf).copy_within(pos..n, pos+1); data_mut[pos] = w`.
    fn leaf_insert_at(n: &mut Self::Node, pos: usize, w: Self::Word)
        requires
            Self::node_wf(*old(n)),
            Self::is_leaf_spec(*old(n)),
            Self::count_spec(*old(n)) < Self::leaf_cap_spec(),
            pos <= Self::count_spec(*old(n)),
        ensures
            Self::is_leaf_spec(*n),
            Self::node_wf(*n),
            Self::count_spec(*n) == Self::count_spec(*old(n)) + 1,
            Self::keys_view(*n) == Self::keys_view(*old(n)).insert(pos as int, w),
            Self::link_view(*n) == Self::link_view(*old(n));

    /// The leaf-split median: `ceil(leaf_cap / 2) = (leaf_cap + 1) / 2`. The
    /// left half keeps `split_mid` keys, the right half gets `leaf_cap + 1 -
    /// split_mid` (production's `mid = LEAF_CAP.div_ceil(2)`).
    spec fn split_mid_spec() -> nat;

    fn split_mid() -> (m: usize)
        ensures m as nat == Self::split_mid_spec();

    /// Split a FULL leaf, inserting `w` at sorted position `pos`. Returns
    /// `(left, right)`: `left` keeps the low half, `right` the high half, of the
    /// combined sequence `keys_view(n).insert(pos, w)` (length `leaf_cap + 1`),
    /// split at `split_mid`. Both are leaves; `right` inherits `n`'s old link
    /// (the caller re-points `left`'s link to `right`'s fresh arena id). This is
    /// production's leaf split, expressed by `Seq::subrange` rather than its
    /// in-place two-case `copy_within` (which a fixed-width array forces but
    /// verification need not mirror).
    fn leaf_split_at(n: &Self::Node, pos: usize, w: Self::Word) -> (res: (Self::Node, Self::Node))
        requires
            Self::is_leaf_spec(*n),
            Self::count_spec(*n) == Self::leaf_cap_spec(),
            pos <= Self::leaf_cap_spec(),
        ensures
            ({
                let combined = Self::keys_view(*n).insert(pos as int, w);
                let mid = Self::split_mid_spec();
                &&& Self::is_leaf_spec(res.0)
                &&& Self::is_leaf_spec(res.1)
                &&& Self::node_wf(res.0)
                &&& Self::node_wf(res.1)
                &&& Self::count_spec(res.0) == mid
                &&& Self::count_spec(res.1) == (Self::leaf_cap_spec() + 1 - mid) as nat
                &&& Self::keys_view(res.0) == combined.subrange(0, mid as int)
                &&& Self::keys_view(res.1) == combined.subrange(mid as int, combined.len() as int)
                &&& Self::link_view(res.1) == Self::link_view(*n)
            });

    /// The internal-split median: `key_cap / 2` (production's `imid =
    /// INTERNAL_KEY_CAP / 2`). A full internal node has `key_cap` separators;
    /// inserting one more makes `key_cap + 1`. `isplit_mid` separators stay left,
    /// one (`combined[isplit_mid]`) is promoted out, the remaining
    /// `key_cap - isplit_mid` go right.
    spec fn isplit_mid_spec() -> nat;

    fn isplit_mid() -> (m: usize)
        ensures m as nat == Self::isplit_mid_spec();

    proof fn lemma_isplit_mid()
        ensures
            Self::isplit_mid_spec() == Self::key_cap_spec() / 2,
            1 <= Self::isplit_mid_spec(),
            Self::isplit_mid_spec() < Self::key_cap_spec();

    /// Split a FULL internal node (`count == key_cap`) that is absorbing a new
    /// `(new_sep at key-pos cp, new_child at child-pos cp+1)`. Forms the combined
    /// separator sequence `cseps = keys_view(n).insert(cp, new_sep)` (length
    /// `key_cap + 1`) and the combined child sequence `cchild` (length
    /// `key_cap + 2`, `new_child` inserted at `cp+1`). Splits at `imid =
    /// isplit_mid`: returns `(left, right, promoted)` where
    ///   - `left.seps  == cseps[0 .. imid]`, `left.children  == cchild[0 ..= imid]`
    ///   - `promoted    == cseps[imid]` (removed from both halves — B-tree style)
    ///   - `right.seps == cseps[imid+1 ..]`, `right.children == cchild[imid+1 ..]`
    /// Both are internal nodes. Mirrors production's internal-node split.
    fn internal_split_at(
        n: &Self::Node,
        cp: usize,
        new_sep: Self::Word,
        new_child: Self::ArenaIdx,
    ) -> (res: (Self::Node, Self::Node, Self::Word))
        requires
            !Self::is_leaf_spec(*n),
            Self::node_wf(*n),
            Self::count_spec(*n) == Self::key_cap_spec(),
            cp <= Self::key_cap_spec(),
        ensures
            ({
                let cseps = Self::keys_view(*n).insert(cp as int, new_sep);
                let imid = Self::isplit_mid_spec();
                let kc = Self::key_cap_spec();
                &&& !Self::is_leaf_spec(res.0)
                &&& !Self::is_leaf_spec(res.1)
                &&& Self::node_wf(res.0)
                &&& Self::node_wf(res.1)
                &&& Self::count_spec(res.0) == imid
                &&& Self::count_spec(res.1) == (kc - imid) as nat
                &&& Self::keys_view(res.0) == cseps.subrange(0, imid as int)
                &&& Self::keys_view(res.1) == cseps.subrange(imid as int + 1, cseps.len() as int)
                &&& res.2 == cseps[imid as int]
                // children: left gets cchild[0..=imid], right gets cchild[imid+1..].
                // cchild at child-pos j = (j<=cp: child(n,j); j==cp+1: new_child;
                //                          else: child(n,j-1)).
                &&& (forall|j: int| 0 <= j <= imid ==>
                        #[trigger] Self::child_view(res.0, j) == Self::isplit_cchild(*n, cp as int, new_child, j))
                &&& (forall|j: int| 0 <= j <= (kc - imid) ==>
                        #[trigger] Self::child_view(res.1, j) == Self::isplit_cchild(*n, cp as int, new_child, imid as int + 1 + j))
            });

    /// The combined child arena-id at child-position `j` after inserting
    /// `new_child` at position `cp+1` (spec helper for `internal_split_at`).
    open spec fn isplit_cchild(n: Self::Node, cp: int, new_child: Self::ArenaIdx, j: int) -> nat {
        if j <= cp {
            Self::child_view(n, j)
        } else if j == cp + 1 {
            new_child.as_nat()
        } else {
            Self::child_view(n, j - 1)
        }
    }

    /// Expose `isplit_cchild`'s three cases generically (a trait spec fn is opaque
    /// to callers through the generic `L`; this is the same idiom as
    /// `lemma_isplit_mid`). Trivial per-impl bodies unfold the `open` definition.
    proof fn lemma_isplit_cchild(n: Self::Node, cp: int, new_child: Self::ArenaIdx, j: int)
        ensures
            Self::isplit_cchild(n, cp, new_child, j) == (
                if j <= cp { Self::child_view(n, j) }
                else if j == cp + 1 { new_child.as_nat() }
                else { Self::child_view(n, j - 1) }
            );

    /// Build a fresh internal node with one separator `sep` and two children
    /// `(left, right)` arena ids. Production's new-root construction
    /// (`set_count(1); set_internal_child(0, left); set_internal_child(1,
    /// right)`). `count == 1`, `keys_view == [sep]`, `child_view(0) == left`,
    /// `child_view(1) == right`.
    fn new_internal2(sep: Self::Word, left: Self::ArenaIdx, right: Self::ArenaIdx) -> (n: Self::Node)
        ensures
            !Self::is_leaf_spec(n),
            Self::node_wf(n),
            Self::count_spec(n) == 1,
            Self::keys_view(n) == seq![sep],
            Self::child_view(n, 0) == left.as_nat(),
            Self::child_view(n, 1) == right.as_nat();

    /// Set a leaf's forward link (production `set_link`). Used to splice the new
    /// right leaf into the chain. Only the link changes.
    fn set_link(n: &mut Self::Node, l: Self::ArenaIdx)
        ensures
            Self::is_leaf_spec(*n) == Self::is_leaf_spec(*old(n)),
            Self::count_spec(*n) == Self::count_spec(*old(n)),
            Self::keys_view(*n) == Self::keys_view(*old(n)),
            Self::node_wf(*n) == Self::node_wf(*old(n)),
            Self::link_view(*n) == l.as_nat();

    /// Set internal child `i` (`0 <= i <= key_cap`) to arena id `v`. Production's
    /// `set_internal_child`: writes `data[key_cap + i]` for `i < key_cap`, else
    /// the `link` field (the last child). Leaves `keys_view`, `count`, leaf-ness,
    /// and every *other* child unchanged. The single primitive that owns the
    /// `link`-as-last-child packing wrinkle; the internal insert/split build on it.
    fn set_internal_child(n: &mut Self::Node, i: usize, v: Self::ArenaIdx)
        requires
            !Self::is_leaf_spec(*old(n)),
            Self::node_wf(*old(n)),
            i <= Self::key_cap_spec(),
        ensures
            Self::is_leaf_spec(*n) == Self::is_leaf_spec(*old(n)),
            Self::node_wf(*n),
            Self::count_spec(*n) == Self::count_spec(*old(n)),
            Self::keys_view(*n) == Self::keys_view(*old(n)),
            Self::child_view(*n, i as int) == v.as_nat(),
            forall|j: int| 0 <= j <= Self::key_cap_spec() && j != i ==>
                Self::child_view(*n, j) == Self::child_view(*old(n), j);

    /// Insert separator `w` into an internal node at key-position `pos`,
    /// shifting `[pos..count)` up. The node must have separator room (`count <
    /// key_cap`). Refines `keys_view` by `Seq::insert` and leaves the children
    /// untouched (they live in `data[key_cap..]` + `link`, disjoint from the
    /// separators at `data[0..count]`). The internal analogue of
    /// `leaf_insert_at`; `internal_insert_at` shifts children separately via
    /// `set_internal_child`.
    fn internal_key_insert(n: &mut Self::Node, pos: usize, w: Self::Word)
        requires
            !Self::is_leaf_spec(*old(n)),
            Self::node_wf(*old(n)),
            Self::count_spec(*old(n)) < Self::key_cap_spec(),
            pos <= Self::count_spec(*old(n)),
        ensures
            Self::is_leaf_spec(*n) == Self::is_leaf_spec(*old(n)),
            Self::node_wf(*n),
            Self::count_spec(*n) == Self::count_spec(*old(n)) + 1,
            Self::keys_view(*n) == Self::keys_view(*old(n)).insert(pos as int, w),
            forall|j: int| 0 <= j <= Self::key_cap_spec() ==>
                Self::child_view(*n, j) == Self::child_view(*old(n), j);

    // -- proof glue --

    /// `node_wf` bounds `count` by the leaf capacity (the loosest bound; an
    /// internal node's `key_cap` is smaller). Lets generic code index keys.
    proof fn lemma_node_wf_count(n: Self::Node)
        requires Self::node_wf(n),
        ensures Self::count_spec(n) <= Self::leaf_cap_spec();

    /// The geometry facts: the backing array holds a full leaf
    /// (`data_len == leaf_cap`), and an internal node's `key_cap` separators plus
    /// its first `key_cap` children both fit in `data` (`2 * key_cap <=
    /// data_len`). The `(key_cap+1)`-th child does not need an array slot — it
    /// lives in `link` — so `2 * key_cap` (not `2 * key_cap + 1`) is the bound.
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
            1 <= Self::key_cap_spec(),
            Self::leaf_cap_spec() < <Self::ArenaIdx as IndexLike>::max_nat();

    /// `node_wf` characterization, exposed so generic code can establish it
    /// from the counts it controls (`node_wf` itself is layout-private): a leaf
    /// is `node_wf` iff `count <= leaf_cap`; an internal node iff
    /// `count <= key_cap`.
    proof fn lemma_node_wf_iff(n: Self::Node)
        ensures
            Self::node_wf(n) == (if Self::is_leaf_spec(n) {
                Self::count_spec(n) <= Self::leaf_cap_spec()
            } else {
                Self::count_spec(n) <= Self::key_cap_spec()
            });

    /// `split_mid` is `ceil(leaf_cap / 2)` (`(leaf_cap + 1) / 2`), exposed so
    /// generic code can relate it to `leaf_cap_spec` (both layout-private).
    proof fn lemma_split_mid()
        ensures
            Self::split_mid_spec() == (Self::leaf_cap_spec() + 1) / 2,
            1 <= Self::split_mid_spec() <= Self::leaf_cap_spec();

    /// The key view has length `count` (`keys_view` is `Seq::new(count, ..)`,
    /// layout-private). Lets generic code relate `keys_view(n).len()` to counts.
    proof fn lemma_keys_view_len(n: Self::Node)
        ensures Self::keys_view(n).len() == Self::count_spec(n);
}

/// Insert separator `sep` at key-position `cp` and child `child` at
/// child-position `cp+1` into a non-full internal node — the parent-absorb step
/// of a propagating split. Generic over `L`, built on `set_internal_child`
/// (shift children `[cp+1..=count]` up, then place `child` at `cp+1`) and
/// `internal_key_insert` (place `sep`; children untouched). A free function, not
/// a trait method, to keep the trait's spec surface lean (heavy default bodies
/// perturb crate-wide spec pruning — see the proof-attempts log).
pub fn internal_insert_at<L: NodeLayout>(n: &mut L::Node, cp: usize, sep: L::Word, child: L::ArenaIdx)
    requires
        !L::is_leaf_spec(*old(n)),
        L::node_wf(*old(n)),
        L::count_spec(*old(n)) < L::key_cap_spec(),
        cp <= L::count_spec(*old(n)),
    ensures
        !L::is_leaf_spec(*n),
        L::node_wf(*n),
        L::count_spec(*n) == L::count_spec(*old(n)) + 1,
        L::keys_view(*n) == L::keys_view(*old(n)).insert(cp as int, sep),
        forall|j: int| 0 <= j <= cp ==> L::child_view(*n, j) == L::child_view(*old(n), j),
        L::child_view(*n, cp + 1) == child.as_nat(),
        forall|j: int| cp + 1 < j <= L::count_spec(*old(n)) + 1 ==>
            L::child_view(*n, j) == L::child_view(*old(n), (j - 1)),
{
    let ghost old_n = *n;
    let cnt = L::count(n);
    let kc = L::key_cap();  // exec key_cap; cnt < kc, so m+1, cp+1 <= kc.
    // Phase A: shift children [cp+1..=cnt] up to [cp+2..=cnt+1], descending.
    let mut m = cnt;
    while m > cp
        invariant
            cp <= m <= cnt,
            cnt < kc,
            kc as nat == L::key_cap_spec(),
            !L::is_leaf_spec(*n),
            L::node_wf(*n),
            L::count_spec(*n) == cnt as nat,
            L::keys_view(*n) == L::keys_view(old_n),
            forall|j: int| 0 <= j <= m ==> L::child_view(*n, j) == L::child_view(old_n, j),
            forall|j: int| m + 1 < j <= cnt + 1 ==>
                L::child_view(*n, j) == L::child_view(old_n, (j - 1)),
        decreases m - cp,
    {
        let cm = L::child(n, m);
        L::set_internal_child(n, m + 1, cm);
        m = m - 1;
    }
    L::set_internal_child(n, cp + 1, child);
    // Phase B: insert the separator at key-pos cp (children untouched).
    L::internal_key_insert(n, cp, sep);
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

            fn leaf_insert_at(n: &mut $node, pos: usize, w: u32) {
                let ghost old_n = *n;
                let cnt = n.count;
                let mut j = cnt;
                while j > pos
                    invariant
                        pos <= j <= cnt,
                        cnt < $leaf_cap,
                        n.count == cnt,
                        n.is_leaf == old_n.is_leaf,
                        n.link == old_n.link,
                        forall|k: int| 0 <= k < j ==> n.data[k] == old_n.data[k],
                        forall|k: int| j < k <= cnt ==> n.data[k] == old_n.data[k - 1],
                    decreases j - pos,
                {
                    n.data[j] = n.data[j - 1];
                    j = j - 1;
                }
                n.data[pos] = w;
                n.count = cnt + 1;
                assert(Self::keys_view(*n) =~= Self::keys_view(old_n).insert(pos as int, w));
            }

            open spec fn split_mid_spec() -> nat { (($leaf_cap + 1) / 2) as nat }
            fn split_mid() -> (m: usize) { ($leaf_cap + 1) / 2 }

            fn leaf_split_at(n: &$node, pos: usize, w: u32) -> (res: ($node, $node)) {
                let ghost old_n = *n;
                let mid: usize = ($leaf_cap + 1) / 2;
                let rc: usize = $leaf_cap + 1 - mid;
                let mut left = $node { is_leaf: true, count: mid, data: [0; $data_len], link: n.link };
                let mut right = $node { is_leaf: true, count: rc, data: [0; $data_len], link: n.link };
                let mut j: usize = 0;
                while j < mid
                    invariant
                        mid == ($leaf_cap + 1) / 2, rc == $leaf_cap + 1 - mid,
                        n.count == $leaf_cap, pos <= $leaf_cap, mid <= $leaf_cap,
                        0 <= j <= mid, left.is_leaf, left.count == mid,
                        forall|t: int| 0 <= t < j ==> #[trigger] left.data[t]
                            == (if t < pos { n.data[t] } else if t == pos { w } else { n.data[t - 1] }),
                    decreases mid - j,
                {
                    let v: u32 = if j < pos { n.data[j] } else if j == pos { w } else { n.data[j - 1] };
                    left.data[j] = v;
                    j = j + 1;
                }
                let mut k: usize = 0;
                while k < rc
                    invariant
                        mid == ($leaf_cap + 1) / 2, rc == $leaf_cap + 1 - mid,
                        n.count == $leaf_cap, pos <= $leaf_cap, mid <= $leaf_cap,
                        0 <= k <= rc, right.is_leaf, right.count == rc, right.link == n.link,
                        forall|t: int| 0 <= t < k ==> #[trigger] right.data[t]
                            == (if mid + t < pos { n.data[mid + t] } else if mid + t == pos { w } else { n.data[mid + t - 1] }),
                    decreases rc - k,
                {
                    let idx: usize = mid + k;
                    let v: u32 = if idx < pos { n.data[idx] } else if idx == pos { w } else { n.data[idx - 1] };
                    right.data[k] = v;
                    k = k + 1;
                }
                proof {
                    let combined = Self::keys_view(old_n).insert(pos as int, w);
                    assert(combined.len() == $leaf_cap + 1);
                    assert(Self::keys_view(left) =~= combined.subrange(0, mid as int)) by {
                        assert forall|t: int| 0 <= t < mid implies
                            #[trigger] Self::keys_view(left)[t] == combined.subrange(0, mid as int)[t] by {
                            assert(left.data[t] == (if t < pos { n.data[t] } else if t == pos { w } else { n.data[t - 1] }));
                        }
                    }
                    assert(Self::keys_view(right) =~= combined.subrange(mid as int, combined.len() as int)) by {
                        assert forall|t: int| 0 <= t < rc implies
                            #[trigger] Self::keys_view(right)[t] == combined.subrange(mid as int, combined.len() as int)[t] by {
                            assert(right.data[t] == (if mid + t < pos { n.data[mid + t] } else if mid + t == pos { w } else { n.data[mid + t - 1] }));
                        }
                    }
                }
                (left, right)
            }

            fn new_internal2(sep: u32, left: u32, right: u32) -> (nn: $node) {
                let mut data = [0; $data_len];
                data[0] = sep;
                data[$key_cap] = left;
                data[$key_cap + 1] = right;
                let nn = $node { is_leaf: false, count: 1, data, link: 0u32 };
                assert(Self::keys_view(nn) =~= seq![sep]);
                nn
            }

            fn set_link(n: &mut $node, l: u32) {
                let ghost old_n = *n;
                n.link = l;
                assert(Self::keys_view(*n) =~= Self::keys_view(old_n));
            }
            fn internal_key_insert(n: &mut $node, pos: usize, w: u32) {
                let ghost old_n = *n;
                let cnt = n.count;
                let mut j = cnt;
                while j > pos
                    invariant
                        pos <= j <= cnt, cnt < $key_cap, n.count == cnt,
                        n.is_leaf == old_n.is_leaf, n.link == old_n.link,
                        forall|k: int| 0 <= k < j ==> n.data[k] == old_n.data[k],
                        forall|k: int| j < k <= cnt ==> n.data[k] == old_n.data[k - 1],
                        forall|k: int| $key_cap <= k < $data_len ==> n.data[k] == old_n.data[k],
                    decreases j - pos,
                {
                    n.data[j] = n.data[j - 1];
                    j = j - 1;
                }
                n.data[pos] = w;
                n.count = cnt + 1;
                assert(Self::keys_view(*n) =~= Self::keys_view(old_n).insert(pos as int, w));
                assert forall|jj: int| 0 <= jj <= $key_cap implies
                    Self::child_view(*n, jj) == Self::child_view(old_n, jj) by {}
            }
            fn set_internal_child(n: &mut $node, i: usize, v: u32) {
                let ghost old_n = *n;
                if i < $key_cap {
                    // i < key_cap and 2*key_cap <= data_len ⟹ key_cap + i in bounds.
                    assert($key_cap + i < $data_len);
                    n.data[$key_cap + i] = v;
                } else {
                    n.link = v;
                }
                // children sit at data[key_cap..] (>= count for an internal
                // node), so keys_view (data[0..count]) is untouched. Other
                // children: writing data[key_cap+i] (or link) leaves data[key_cap+j]
                // (j != i) and the other of data/link untouched.
                assert(Self::keys_view(*n) =~= Self::keys_view(old_n));
                assert forall|j: int| 0 <= j <= $key_cap && j != i implies
                    Self::child_view(*n, j) == Self::child_view(old_n, j) by {}
            }
            open spec fn isplit_mid_spec() -> nat { Self::key_cap_spec() / 2 }
            fn isplit_mid() -> (m: usize) { $key_cap / 2 }
            proof fn lemma_isplit_mid() {}
            proof fn lemma_isplit_cchild(n: Self::Node, cp: int, new_child: Self::ArenaIdx, j: int) {}

            fn internal_split_at(n: &$node, cp: usize, new_sep: u32, new_child: u32)
                -> (res: ($node, $node, u32))
            {
                let imid: usize = $key_cap / 2;
                let kc: usize = $key_cap;
                let ghost cseps = Self::keys_view(*n).insert(cp as int, new_sep);
                // Fresh left/right, counts set upfront so keys_view reads the
                // filled prefix. is_leaf=false; link is a child slot, set via children loop.
                let mut left = *n;
                let mut right = *n;
                left.count = imid;
                right.count = kc - imid;
                // left separators [0..imid) = cseps[0..imid].
                let mut j: usize = 0;
                while j < imid
                    invariant
                        imid as nat == Self::isplit_mid_spec(), kc as nat == Self::key_cap_spec(), Self::count_spec(*n) == Self::key_cap_spec(), cp as nat <= Self::key_cap_spec(),
                        0 <= j <= imid, !left.is_leaf, left.count == imid,
                        forall|t: int| 0 <= t < j ==> #[trigger] left.data[t]
                            == (if t < cp { n.data[t] } else if t == cp { new_sep } else { n.data[t - 1] }),
                    decreases imid - j,
                {
                    let v: u32 = if j < cp { n.data[j] } else if j == cp { new_sep } else { n.data[j - 1] };
                    left.data[j] = v;
                    j = j + 1;
                }
                // right separators [0..kc-imid) = cseps[imid+1..].
                let mut j2: usize = 0;
                while j2 < kc - imid
                    invariant
                        imid as nat == Self::isplit_mid_spec(), kc as nat == Self::key_cap_spec(), Self::count_spec(*n) == Self::key_cap_spec(), cp as nat <= Self::key_cap_spec(),
                        imid < kc, 0 <= j2 <= kc - imid, !right.is_leaf, right.count == kc - imid,
                        forall|t: int| 0 <= t < j2 ==> #[trigger] right.data[t]
                            == (if imid as int + 1 + t < cp { n.data[imid as int + 1 + t] }
                                else if imid as int + 1 + t == cp { new_sep } else { n.data[imid as int + 1 + t - 1] }),
                    decreases (kc - imid) - j2,
                {
                    let idx: usize = imid + 1 + j2;
                    let v: u32 = if idx < cp { n.data[idx] } else if idx == cp { new_sep } else { n.data[idx - 1] };
                    right.data[j2] = v;
                    j2 = j2 + 1;
                }
                proof {
                    // establish both seps subranges now (children loops preserve keys_view).
                    assert forall|i: int| 0 <= i < cseps.len() implies
                        cseps[i] == (if i < cp { n.data[i] } else if i == cp { new_sep } else { n.data[i - 1] }) by {
                        if i < cp { assert(cseps[i] == Self::keys_view(*n)[i]); }
                        else if i > cp { assert(cseps[i] == Self::keys_view(*n)[i - 1]); }
                    }
                    assert forall|t: int| 0 <= t < imid implies
                        #[trigger] Self::keys_view(left)[t] == cseps.subrange(0, imid as int)[t] by {
                        assert(Self::keys_view(left)[t] == left.data[t]);
                    }
                    assert(Self::keys_view(left) =~= cseps.subrange(0, imid as int));
                    assert forall|t: int| 0 <= t < (kc - imid) implies
                        Self::keys_view(right)[t] == cseps.subrange(imid as int + 1, cseps.len() as int)[t] by {
                        assert(Self::keys_view(right)[t] == right.data[t]);
                    }
                    assert(Self::keys_view(right) =~= cseps.subrange(imid as int + 1, cseps.len() as int));
                }
                // left children [0..=imid] = cchild[0..=imid].
                let mut k: usize = 0;
                while k <= imid
                    invariant
                        imid as nat == Self::isplit_mid_spec(), kc as nat == Self::key_cap_spec(), Self::count_spec(*n) == Self::key_cap_spec(), cp as nat <= Self::key_cap_spec(),
                        imid < kc, 0 <= k <= imid + 1, !left.is_leaf, left.count == imid, Self::node_wf(left),
                        !n.is_leaf, Self::node_wf(*n),
                        Self::keys_view(left) == cseps.subrange(0, imid as int),
                        Self::keys_view(right) == cseps.subrange(imid as int + 1, cseps.len() as int),
                        forall|t: int| 0 <= t < k ==> #[trigger] Self::child_view(left, t)
                            == Self::isplit_cchild(*n, cp as int, new_child, t),
                    decreases imid + 1 - k,
                {
                    let cv: u32 = if k <= cp { Self::child(n, k) } else if k == cp + 1 { new_child } else { Self::child(n, k - 1) };
                    Self::set_internal_child(&mut left, k, cv);
                    k = k + 1;
                }
                // right children [0..=kc-imid] = cchild[imid+1..].
                let mut k2: usize = 0;
                while k2 <= kc - imid
                    invariant
                        imid as nat == Self::isplit_mid_spec(), kc as nat == Self::key_cap_spec(), Self::count_spec(*n) == Self::key_cap_spec(), cp as nat <= Self::key_cap_spec(),
                        imid < kc, 0 <= k2 <= (kc - imid) + 1, !right.is_leaf, right.count == kc - imid, Self::node_wf(right),
                        !n.is_leaf, Self::node_wf(*n),
                        Self::keys_view(left) == cseps.subrange(0, imid as int),
                        Self::keys_view(right) == cseps.subrange(imid as int + 1, cseps.len() as int),
                        forall|t: int| 0 <= t < k2 ==> #[trigger] Self::child_view(right, t)
                            == Self::isplit_cchild(*n, cp as int, new_child, imid as int + 1 + t),
                    decreases (kc - imid) + 1 - k2,
                {
                    let cidx: usize = imid + 1 + k2;
                    let cv: u32 = if cidx <= cp { Self::child(n, cidx) } else if cidx == cp + 1 { new_child } else { Self::child(n, cidx - 1) };
                    Self::set_internal_child(&mut right, k2, cv);
                    k2 = k2 + 1;
                }
                let promoted: u32 = if imid < cp { n.data[imid] } else if imid == cp { new_sep } else { n.data[imid - 1] };
                (left, right, promoted)
            }
            proof fn lemma_node_wf_count(n: $node) {}
            proof fn lemma_geometry() {}
            proof fn lemma_arena_capacity() {}
            proof fn lemma_node_wf_iff(n: $node) {}
            proof fn lemma_keys_view_len(n: $node) {}
            proof fn lemma_split_mid() {}
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

            // u64 word -> usize arena index: the narrowing cast, lossless on a
            // 64-bit usize (the u64 layouts' declared target), proven via
            // lemma_u64_usize_roundtrip. The `i == count <= key_cap` case may read
            // the `link`-held last child (already a usize, no cast). The trait's
            // requires/ensures (node_wf, !is_leaf, i <= count; c == child_view) are
            // inherited.
            fn child(n: &$node, i: usize) -> (c: usize) {
                if i < $key_cap {
                    assert($key_cap + i < $data_len);  // 2*key_cap <= data_len
                    let c = n.data[$key_cap + i] as usize;
                    proof { lemma_u64_usize_roundtrip(n.data[$key_cap as int + i as int]); }
                    c
                } else {
                    n.link
                }
            }
            fn link(n: &$node) -> (l: usize) { n.link }
            fn new_leaf() -> (n: $node) {
                $node { is_leaf: true, count: 0, data: [0; $data_len], link: usize::MAX }
            }

            fn leaf_insert_at(n: &mut $node, pos: usize, w: u64) {
                let ghost old_n = *n;
                let cnt = n.count;
                let mut j = cnt;
                while j > pos
                    invariant
                        pos <= j <= cnt,
                        cnt < $leaf_cap,
                        n.count == cnt,
                        n.is_leaf == old_n.is_leaf,
                        n.link == old_n.link,
                        forall|k: int| 0 <= k < j ==> n.data[k] == old_n.data[k],
                        forall|k: int| j < k <= cnt ==> n.data[k] == old_n.data[k - 1],
                    decreases j - pos,
                {
                    n.data[j] = n.data[j - 1];
                    j = j - 1;
                }
                n.data[pos] = w;
                n.count = cnt + 1;
                assert(Self::keys_view(*n) =~= Self::keys_view(old_n).insert(pos as int, w));
            }

            open spec fn split_mid_spec() -> nat { (($leaf_cap + 1) / 2) as nat }
            fn split_mid() -> (m: usize) { ($leaf_cap + 1) / 2 }

            fn leaf_split_at(n: &$node, pos: usize, w: u64) -> (res: ($node, $node)) {
                let ghost old_n = *n;
                let mid: usize = ($leaf_cap + 1) / 2;
                let rc: usize = $leaf_cap + 1 - mid;
                let mut left = $node { is_leaf: true, count: mid, data: [0; $data_len], link: n.link };
                let mut right = $node { is_leaf: true, count: rc, data: [0; $data_len], link: n.link };
                let mut j: usize = 0;
                while j < mid
                    invariant
                        mid == ($leaf_cap + 1) / 2, rc == $leaf_cap + 1 - mid,
                        n.count == $leaf_cap, pos <= $leaf_cap, mid <= $leaf_cap,
                        0 <= j <= mid, left.is_leaf, left.count == mid,
                        forall|t: int| 0 <= t < j ==> #[trigger] left.data[t]
                            == (if t < pos { n.data[t] } else if t == pos { w } else { n.data[t - 1] }),
                    decreases mid - j,
                {
                    let v: u64 = if j < pos { n.data[j] } else if j == pos { w } else { n.data[j - 1] };
                    left.data[j] = v;
                    j = j + 1;
                }
                let mut k: usize = 0;
                while k < rc
                    invariant
                        mid == ($leaf_cap + 1) / 2, rc == $leaf_cap + 1 - mid,
                        n.count == $leaf_cap, pos <= $leaf_cap, mid <= $leaf_cap,
                        0 <= k <= rc, right.is_leaf, right.count == rc, right.link == n.link,
                        forall|t: int| 0 <= t < k ==> #[trigger] right.data[t]
                            == (if mid + t < pos { n.data[mid + t] } else if mid + t == pos { w } else { n.data[mid + t - 1] }),
                    decreases rc - k,
                {
                    let idx: usize = mid + k;
                    let v: u64 = if idx < pos { n.data[idx] } else if idx == pos { w } else { n.data[idx - 1] };
                    right.data[k] = v;
                    k = k + 1;
                }
                proof {
                    let combined = Self::keys_view(old_n).insert(pos as int, w);
                    assert(combined.len() == $leaf_cap + 1);
                    assert(Self::keys_view(left) =~= combined.subrange(0, mid as int)) by {
                        assert forall|t: int| 0 <= t < mid implies
                            #[trigger] Self::keys_view(left)[t] == combined.subrange(0, mid as int)[t] by {
                            assert(left.data[t] == (if t < pos { n.data[t] } else if t == pos { w } else { n.data[t - 1] }));
                        }
                    }
                    assert(Self::keys_view(right) =~= combined.subrange(mid as int, combined.len() as int)) by {
                        assert forall|t: int| 0 <= t < rc implies
                            #[trigger] Self::keys_view(right)[t] == combined.subrange(mid as int, combined.len() as int)[t] by {
                            assert(right.data[t] == (if mid + t < pos { n.data[mid + t] } else if mid + t == pos { w } else { n.data[mid + t - 1] }));
                        }
                    }
                }
                (left, right)
            }

            // Stores `usize` arena ids into the `u64` data array; child_view reads
            // them back as nat. The two stores' value-preservation is the same
            // `usize as u64 as nat == usize as nat` cast as set_internal_child,
            // discharged by `lemma_usize_u64_roundtrip` (no longer external_body).
            fn new_internal2(sep: u64, left: usize, right: usize) -> (nn: $node)
                ensures
                    !Self::is_leaf_spec(nn),
                    Self::node_wf(nn),
                    Self::count_spec(nn) == 1,
                    Self::keys_view(nn) == seq![sep],
                    Self::child_view(nn, 0) == left.as_nat(),
                    Self::child_view(nn, 1) == right.as_nat(),
            {
                let mut data = [0u64; $data_len];
                data[0] = sep;
                data[$key_cap] = left as u64;
                data[$key_cap + 1] = right as u64;
                let nn = $node { is_leaf: false, count: 1, data, link: 0usize };
                proof {
                    lemma_usize_u64_roundtrip(left);   // (left as u64) as nat == left as nat
                    lemma_usize_u64_roundtrip(right);
                }
                assert(Self::keys_view(nn) =~= seq![sep]);
                // child_view(nn,0)==data[key_cap]==left as u64; child_view(nn,1)==
                // data[key_cap+1]==right as u64; the roundtrip gives == left/right.as_nat.
                assert(Self::child_view(nn, 0) == left.as_nat());
                assert(Self::child_view(nn, 1) == right.as_nat());
                nn
            }

            fn set_link(n: &mut $node, l: usize) {
                let ghost old_n = *n;
                n.link = l;
                assert(Self::keys_view(*n) =~= Self::keys_view(old_n));
            }
            fn internal_key_insert(n: &mut $node, pos: usize, w: u64) {
                let ghost old_n = *n;
                let cnt = n.count;
                let mut j = cnt;
                while j > pos
                    invariant
                        pos <= j <= cnt, cnt < $key_cap, n.count == cnt,
                        n.is_leaf == old_n.is_leaf, n.link == old_n.link,
                        forall|k: int| 0 <= k < j ==> n.data[k] == old_n.data[k],
                        forall|k: int| j < k <= cnt ==> n.data[k] == old_n.data[k - 1],
                        forall|k: int| $key_cap <= k < $data_len ==> n.data[k] == old_n.data[k],
                    decreases j - pos,
                {
                    n.data[j] = n.data[j - 1];
                    j = j - 1;
                }
                n.data[pos] = w;
                n.count = cnt + 1;
                assert(Self::keys_view(*n) =~= Self::keys_view(old_n).insert(pos as int, w));
                assert forall|jj: int| 0 <= jj <= $key_cap implies
                    Self::child_view(*n, jj) == Self::child_view(old_n, jj) by {}
            }
            // Stores a `usize` arena id into the `u64` data slot (or the `usize`
            // link). The store goes through `v as u64`; child_view reads it back
            // as nat, so the obligation is the value-preserving `usize as u64 as
            // nat == usize as nat` cast, discharged by `lemma_usize_u64_roundtrip`.
            fn set_internal_child(n: &mut $node, i: usize, v: usize)
                ensures
                    Self::is_leaf_spec(*n) == Self::is_leaf_spec(*old(n)),
                    Self::node_wf(*n),
                    Self::count_spec(*n) == Self::count_spec(*old(n)),
                    Self::keys_view(*n) == Self::keys_view(*old(n)),
                    Self::child_view(*n, i as int) == v.as_nat(),
                    forall|j: int| 0 <= j <= Self::key_cap_spec() && j != i ==>
                        Self::child_view(*n, j) == Self::child_view(*old(n), j),
            {
                let ghost old_n = *n;
                if i < $key_cap {
                    assert($key_cap + i < $data_len);  // 2*key_cap <= data_len
                    n.data[$key_cap + i] = v as u64;
                    proof { lemma_usize_u64_roundtrip(v); }  // (v as u64) as nat == v as nat
                } else {
                    n.link = v;
                }
                // keys_view (data[0..count]) untouched; other children unchanged.
                assert(Self::keys_view(*n) =~= Self::keys_view(old_n));
                assert(Self::child_view(*n, i as int) == v.as_nat());
                assert forall|j: int| 0 <= j <= $key_cap && j != i implies
                    Self::child_view(*n, j) == Self::child_view(old_n, j) by {}
            }
            open spec fn isplit_mid_spec() -> nat { Self::key_cap_spec() / 2 }
            fn isplit_mid() -> (m: usize) { $key_cap / 2 }
            proof fn lemma_isplit_mid() {}
            proof fn lemma_isplit_cchild(n: Self::Node, cp: int, new_child: Self::ArenaIdx, j: int) {}

            fn internal_split_at(n: &$node, cp: usize, new_sep: u64, new_child: usize)
                -> (res: ($node, $node, u64))
            {
                let imid: usize = $key_cap / 2;
                let kc: usize = $key_cap;
                let ghost cseps = Self::keys_view(*n).insert(cp as int, new_sep);
                // Fresh left/right, counts set upfront so keys_view reads the
                // filled prefix. is_leaf=false; link is a child slot, set via children loop.
                let mut left = *n;
                let mut right = *n;
                left.count = imid;
                right.count = kc - imid;
                // left separators [0..imid) = cseps[0..imid].
                let mut j: usize = 0;
                while j < imid
                    invariant
                        imid as nat == Self::isplit_mid_spec(), kc as nat == Self::key_cap_spec(), Self::count_spec(*n) == Self::key_cap_spec(), cp as nat <= Self::key_cap_spec(),
                        0 <= j <= imid, !left.is_leaf, left.count == imid,
                        forall|t: int| 0 <= t < j ==> #[trigger] left.data[t]
                            == (if t < cp { n.data[t] } else if t == cp { new_sep } else { n.data[t - 1] }),
                    decreases imid - j,
                {
                    let v: u64 = if j < cp { n.data[j] } else if j == cp { new_sep } else { n.data[j - 1] };
                    left.data[j] = v;
                    j = j + 1;
                }
                // right separators [0..kc-imid) = cseps[imid+1..].
                let mut j2: usize = 0;
                while j2 < kc - imid
                    invariant
                        imid as nat == Self::isplit_mid_spec(), kc as nat == Self::key_cap_spec(), Self::count_spec(*n) == Self::key_cap_spec(), cp as nat <= Self::key_cap_spec(),
                        imid < kc, 0 <= j2 <= kc - imid, !right.is_leaf, right.count == kc - imid,
                        forall|t: int| 0 <= t < j2 ==> #[trigger] right.data[t]
                            == (if imid as int + 1 + t < cp { n.data[imid as int + 1 + t] }
                                else if imid as int + 1 + t == cp { new_sep } else { n.data[imid as int + 1 + t - 1] }),
                    decreases (kc - imid) - j2,
                {
                    let idx: usize = imid + 1 + j2;
                    let v: u64 = if idx < cp { n.data[idx] } else if idx == cp { new_sep } else { n.data[idx - 1] };
                    right.data[j2] = v;
                    j2 = j2 + 1;
                }
                proof {
                    // establish both seps subranges now (children loops preserve keys_view).
                    assert forall|i: int| 0 <= i < cseps.len() implies
                        cseps[i] == (if i < cp { n.data[i] } else if i == cp { new_sep } else { n.data[i - 1] }) by {
                        if i < cp { assert(cseps[i] == Self::keys_view(*n)[i]); }
                        else if i > cp { assert(cseps[i] == Self::keys_view(*n)[i - 1]); }
                    }
                    assert forall|t: int| 0 <= t < imid implies
                        #[trigger] Self::keys_view(left)[t] == cseps.subrange(0, imid as int)[t] by {
                        assert(Self::keys_view(left)[t] == left.data[t]);
                    }
                    assert(Self::keys_view(left) =~= cseps.subrange(0, imid as int));
                    assert forall|t: int| 0 <= t < (kc - imid) implies
                        Self::keys_view(right)[t] == cseps.subrange(imid as int + 1, cseps.len() as int)[t] by {
                        assert(Self::keys_view(right)[t] == right.data[t]);
                    }
                    assert(Self::keys_view(right) =~= cseps.subrange(imid as int + 1, cseps.len() as int));
                }
                // left children [0..=imid] = cchild[0..=imid].
                let mut k: usize = 0;
                while k <= imid
                    invariant
                        imid as nat == Self::isplit_mid_spec(), kc as nat == Self::key_cap_spec(), Self::count_spec(*n) == Self::key_cap_spec(), cp as nat <= Self::key_cap_spec(),
                        imid < kc, 0 <= k <= imid + 1, !left.is_leaf, left.count == imid, Self::node_wf(left),
                        !n.is_leaf, Self::node_wf(*n),
                        Self::keys_view(left) == cseps.subrange(0, imid as int),
                        Self::keys_view(right) == cseps.subrange(imid as int + 1, cseps.len() as int),
                        forall|t: int| 0 <= t < k ==> #[trigger] Self::child_view(left, t)
                            == Self::isplit_cchild(*n, cp as int, new_child, t),
                    decreases imid + 1 - k,
                {
                    let cv: usize = if k <= cp { Self::child(n, k) } else if k == cp + 1 { new_child } else { Self::child(n, k - 1) };
                    Self::set_internal_child(&mut left, k, cv);
                    k = k + 1;
                }
                // right children [0..=kc-imid] = cchild[imid+1..].
                let mut k2: usize = 0;
                while k2 <= kc - imid
                    invariant
                        imid as nat == Self::isplit_mid_spec(), kc as nat == Self::key_cap_spec(), Self::count_spec(*n) == Self::key_cap_spec(), cp as nat <= Self::key_cap_spec(),
                        imid < kc, 0 <= k2 <= (kc - imid) + 1, !right.is_leaf, right.count == kc - imid, Self::node_wf(right),
                        !n.is_leaf, Self::node_wf(*n),
                        Self::keys_view(left) == cseps.subrange(0, imid as int),
                        Self::keys_view(right) == cseps.subrange(imid as int + 1, cseps.len() as int),
                        forall|t: int| 0 <= t < k2 ==> #[trigger] Self::child_view(right, t)
                            == Self::isplit_cchild(*n, cp as int, new_child, imid as int + 1 + t),
                    decreases (kc - imid) + 1 - k2,
                {
                    let cidx: usize = imid + 1 + k2;
                    let cv: usize = if cidx <= cp { Self::child(n, cidx) } else if cidx == cp + 1 { new_child } else { Self::child(n, cidx - 1) };
                    Self::set_internal_child(&mut right, k2, cv);
                    k2 = k2 + 1;
                }
                let promoted: u64 = if imid < cp { n.data[imid] } else if imid == cp { new_sep } else { n.data[imid - 1] };
                proof {
                    assert forall|i: int| 0 <= i < cseps.len() implies
                        cseps[i] == (if i < cp { n.data[i] } else if i == cp { new_sep } else { n.data[i - 1] }) by {
                        if i < cp {
                            assert(cseps[i] == Self::keys_view(*n)[i]);
                        } else if i > cp {
                            assert(cseps[i] == Self::keys_view(*n)[i - 1]);
                        }
                    }
                    // per-index: keys_view(left)[t] == left.data[t] == formula(t)
                    //          == cseps[t] == cseps.subrange(0, imid)[t].
                    assert forall|t: int| 0 <= t < imid implies
                        #[trigger] Self::keys_view(left)[t] == cseps.subrange(0, imid as int)[t] by {
                        assert(Self::keys_view(left)[t] == left.data[t]);
                    }
                    assert(Self::keys_view(left) =~= cseps.subrange(0, imid as int));
                    assert forall|t: int| 0 <= t < (kc - imid) implies
                        Self::keys_view(right)[t] == cseps.subrange(imid as int + 1, cseps.len() as int)[t] by {
                        assert(Self::keys_view(right)[t] == right.data[t]);
                    }
                    assert(Self::keys_view(right) =~= cseps.subrange(imid as int + 1, cseps.len() as int));
                }
                (left, right, promoted)
            }
            proof fn lemma_node_wf_count(n: $node) {}
            proof fn lemma_geometry() {}
            proof fn lemma_arena_capacity() {}
            proof fn lemma_node_wf_iff(n: $node) {}
            proof fn lemma_keys_view_len(n: $node) {}
            proof fn lemma_split_mid() {}
        }

        } // verus!
    };
}

// -- the six production layouts (bit-exact with `impl_layout!`) --

gen_layout_u32!(Layout64U32, Node64U32, NodeRepr64U32, 14, 14, 7);
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
