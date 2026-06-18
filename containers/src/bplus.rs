// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Arena-backed B+Tree set of `DenseId` keys.
//!
//! Parameterized over:
//! - `K: DenseId` — key type. The raw backing word `K::Index` is `u32`
//!   (31-bit IDs) or `u64` (63-bit IDs).
//! - `L: NodeLayout<Word = K::Index>` — node size / alignment (64, 128, 256, 512 bytes).
//!   Controls leaf and internal capacities, derived from `NODE_SIZE` and
//!   `sizeof(Word)`.
//! - `S: SearchKind` — leaf/internal key search strategy.
//! - `const TRACK: bool` — compile out semi-persistent tracking when false.
//!
//! All nodes share a single cache-aligned struct in a `VecI<L::Node>` arena.
//! Leaves form a linked chain via the `link` field for O(1) `step()`.
//!
//! # Arena index width
//!
//! The arena index type is per-layout via `NodeLayout::ArenaIdx`:
//! - u32-keyed layouts use `u32` arena indices — the `link` field and child
//!   slots store u32 without waste.
//! - u64-keyed layouts use `usize` arena indices — the `link` field is 8 bytes
//!   (eating padding that u32 link would otherwise leave) and child slots are
//!   stored as u64, natively matching the arena index width on 64-bit platforms.
//!
//! This gives u64 layouts the full u64 arena capacity (`usize::MAX` nodes on
//! 64-bit platforms), matching the 63-bit DenseId key space with comfortable
//! headroom. `alloc_leaf`/`alloc_internal` assert that the arena never grows
//! past `ArenaIdx::MAX`, which is reserved as the NIL sentinel.

use core::marker::PhantomData;

use crate::{DenseId, IndexLike};

// NIL sentinel is per-layout: `<L::ArenaIdx>::MAX`. u32 layouts use u32::MAX,
// u64 layouts use usize::MAX. Not a single module const — kept inline at the
// call sites that need it.

const FLAG_LEAF: u8 = 0x01;
const FLAG_TAG: u8 = 0x02;

// ===========================================================================
// Concrete node structs — one per (size, word, link-type) combination
// ===========================================================================

macro_rules! define_node {
    ($name:ident, $align:literal, $word:ty, $data_len:literal, $link:ty) => {
        #[derive(Clone, Copy)]
        #[repr(C, align($align))]
        pub struct $name {
            flags: u8,
            count: u8,
            _pad: u16,
            data: [$word; $data_len],
            link: $link,
        }

        const _: () = assert!(size_of::<$name>() == $align);

        impl $crate::Tagged for $name {
            type Repr = $name;
            #[inline(always)]
            fn into_repr(self) -> $name {
                let mut r = self;
                r.flags &= !FLAG_TAG;
                r
            }
            #[inline(always)]
            fn from_repr(r: &$name) -> $name {
                let mut v = *r;
                v.flags &= !FLAG_TAG;
                v
            }
            #[inline(always)]
            fn tag(r: &$name) -> bool {
                r.flags & FLAG_TAG != 0
            }
            #[inline(always)]
            fn set_tag(r: &mut $name) {
                r.flags |= FLAG_TAG;
            }
            #[inline(always)]
            fn clear_tag(r: &mut $name) {
                r.flags &= !FLAG_TAG;
            }
        }

        // All-zero default: a degenerate node used only as a `resize_default`
        // filler during `restore`. It is never observed (every regrown cell is
        // overwritten by its captured diff value). `flags: 0` clears the tag
        // bit, so the all-zero repr is niche-safe. A manual impl (not derive)
        // because the data array length can exceed `[T; N]: Default`'s limit.
        impl ::core::default::Default for $name {
            fn default() -> Self {
                Self {
                    flags: 0,
                    count: 0,
                    _pad: 0,
                    data: [<$word as ::core::default::Default>::default(); $data_len],
                    link: <$link as ::core::default::Default>::default(),
                }
            }
        }
    };
}

// u32-backed: u32 keys, u32 link. (NODE_SIZE - 8) / 4 key slots.
define_node!(BPlusNode64U32, 64, u32, 14, u32);
define_node!(BPlusNode128U32, 128, u32, 30, u32);
define_node!(BPlusNode256U32, 256, u32, 62, u32);

// u64-backed: u64 keys, usize link (full arena reach on 64-bit platforms).
// 64-byte u64 variant omitted (fanout=3 yields pathologically deep trees).
// Layout size math: 4 header + 4 align-pad + 8*DATA_LEN data + 8 link.
define_node!(BPlusNode128U64, 128, u64, 14, usize);
define_node!(BPlusNode256U64, 256, u64, 30, usize);
define_node!(BPlusNode512U64, 512, u64, 62, usize);

// Back-compat aliases.
pub type BPlusNode64 = BPlusNode64U32;
pub type BPlusNode128 = BPlusNode128U32;
pub type BPlusNode256 = BPlusNode256U32;
pub type BPlusNode = BPlusNode64U32;

// ===========================================================================
// NodeLayout trait
// ===========================================================================

/// Compile-time node geometry. `Word` is the raw storage word (u32 or u64)
/// used inside the data array; keys are stored as `K::Index` values (which
/// must equal `Word`).
pub trait NodeLayout: Copy + Clone + 'static {
    type Word: Copy + Ord + Default + 'static;
    /// Arena index type. `u32` for u32-keyed layouts, `usize` for u64-keyed
    /// layouts (full address-space reach on 64-bit platforms). The sentinel
    /// value `<ArenaIdx as IndexLike>::MAX` is reserved as NIL.
    type ArenaIdx: IndexLike + Default + 'static;
    type Node: Copy + crate::Tagged<Repr = Self::Node>;

    const NODE_SIZE: usize;
    const LEAF_CAP: usize;
    const INTERNAL_KEY_CAP: usize;
    const INTERNAL_CHILD_CAP: usize;
    const MAX_DEPTH: usize;

    fn zero() -> Self::Word;
    fn child_to_word(c: Self::ArenaIdx) -> Self::Word;
    fn word_to_child(w: Self::Word) -> Self::ArenaIdx;

    fn new_leaf() -> Self::Node;
    fn new_internal() -> Self::Node;
    fn is_leaf(n: &Self::Node) -> bool;
    fn count(n: &Self::Node) -> usize;
    fn set_count(n: &mut Self::Node, c: usize);
    fn data(n: &Self::Node) -> &[Self::Word];
    fn data_mut(n: &mut Self::Node) -> &mut [Self::Word];
    fn link(n: &Self::Node) -> Self::ArenaIdx;
    fn set_link(n: &mut Self::Node, v: Self::ArenaIdx);
    fn internal_child(n: &Self::Node, i: usize) -> Self::ArenaIdx;
    fn set_internal_child(n: &mut Self::Node, i: usize, v: Self::ArenaIdx);
}

macro_rules! impl_layout {
    ($layout:ident, $node:ident, $word:ty, $arena:ty, $data_len:literal, $leaf_cap:literal, $key_cap:literal, $child_cap:literal, $max_depth:literal, $size:literal) => {
        #[derive(Copy, Clone)]
        pub struct $layout;

        impl NodeLayout for $layout {
            type Word = $word;
            type ArenaIdx = $arena;
            type Node = $node;
            const NODE_SIZE: usize = $size;
            const LEAF_CAP: usize = $leaf_cap;
            const INTERNAL_KEY_CAP: usize = $key_cap;
            const INTERNAL_CHILD_CAP: usize = $child_cap;
            const MAX_DEPTH: usize = $max_depth;

            #[inline(always)]
            fn zero() -> $word {
                0
            }
            #[inline(always)]
            fn child_to_word(c: $arena) -> $word {
                c as $word
            }
            #[inline(always)]
            fn word_to_child(w: $word) -> $arena {
                w as $arena
            }

            #[inline(always)]
            fn new_leaf() -> $node {
                $node {
                    flags: FLAG_LEAF,
                    count: 0,
                    _pad: 0,
                    data: [0; $data_len],
                    link: <$arena>::MAX,
                }
            }
            #[inline(always)]
            fn new_internal() -> $node {
                $node {
                    flags: 0,
                    count: 0,
                    _pad: 0,
                    data: [0; $data_len],
                    link: 0 as $arena,
                }
            }
            #[inline(always)]
            fn is_leaf(n: &$node) -> bool {
                n.flags & FLAG_LEAF != 0
            }
            #[inline(always)]
            fn count(n: &$node) -> usize {
                n.count as usize
            }
            #[inline(always)]
            fn set_count(n: &mut $node, c: usize) {
                n.count = c as u8;
            }
            #[inline(always)]
            fn data(n: &$node) -> &[$word] {
                &n.data
            }
            #[inline(always)]
            fn data_mut(n: &mut $node) -> &mut [$word] {
                &mut n.data
            }
            #[inline(always)]
            fn link(n: &$node) -> $arena {
                n.link
            }
            #[inline(always)]
            fn set_link(n: &mut $node, v: $arena) {
                n.link = v;
            }
            #[inline(always)]
            fn internal_child(n: &$node, i: usize) -> $arena {
                if i < $key_cap {
                    n.data[$key_cap + i] as $arena
                } else {
                    n.link
                }
            }
            #[inline(always)]
            fn set_internal_child(n: &mut $node, i: usize, v: $arena) {
                if i < $key_cap {
                    n.data[$key_cap + i] = v as $word;
                } else {
                    n.link = v;
                }
            }
        }
    };
}

// u32 layouts: u32 arena index, u32 data words. Arena cap = u32::MAX nodes.
// MAX_DEPTH is the ceiling for worst-case 31-bit DenseId key space (2^31).
impl_layout!(Layout64U32, BPlusNode64U32, u32, u32, 14, 14, 7, 8, 10, 64);
impl_layout!(
    Layout128U32,
    BPlusNode128U32,
    u32,
    u32,
    30,
    30,
    14,
    15,
    7,
    128
);
impl_layout!(
    Layout256U32,
    BPlusNode256U32,
    u32,
    u32,
    62,
    62,
    30,
    31,
    6,
    256
);

// u64 layouts: usize arena index, u64 data words. Arena cap = usize::MAX
// nodes on 64-bit platforms. MAX_DEPTH is the ceiling for worst-case 63-bit
// DenseId key space (2^63) with the corresponding fanout.
impl_layout!(
    Layout128U64,
    BPlusNode128U64,
    u64,
    usize,
    14,
    14,
    6,
    7,
    22,
    128
);
impl_layout!(
    Layout256U64,
    BPlusNode256U64,
    u64,
    usize,
    30,
    30,
    14,
    15,
    16,
    256
);
impl_layout!(
    Layout512U64,
    BPlusNode512U64,
    u64,
    usize,
    62,
    62,
    30,
    31,
    12,
    512
);

// Back-compat aliases.
pub type Layout64 = Layout64U32;
pub type Layout128 = Layout128U32;
pub type Layout256 = Layout256U32;

// ===========================================================================
// SearchKind — generic over the word type
// ===========================================================================

pub trait SearchKind: Copy + Clone + 'static {
    fn find_ge<W: Copy + Ord>(keys: &[W], target: W) -> usize;
    fn find_gt<W: Copy + Ord>(keys: &[W], target: W) -> usize;
}

/// Branched binary search via `partition_point`.
/// Overflow-safe: slices are bounded by `L::LEAF_CAP` ≤ 62.
#[derive(Copy, Clone)]
pub struct BinarySearch;

impl SearchKind for BinarySearch {
    #[inline(always)]
    fn find_ge<W: Copy + Ord>(keys: &[W], target: W) -> usize {
        debug_assert!(keys.len() <= u32::MAX as usize);
        keys.partition_point(|k| *k < target)
    }
    #[inline(always)]
    fn find_gt<W: Copy + Ord>(keys: &[W], target: W) -> usize {
        debug_assert!(keys.len() <= u32::MAX as usize);
        keys.partition_point(|k| *k <= target)
    }
}

/// Branchless linear count — auto-vectorizable for small contiguous slices.
#[derive(Copy, Clone)]
pub struct Branchless;

impl SearchKind for Branchless {
    #[inline(always)]
    fn find_ge<W: Copy + Ord>(keys: &[W], target: W) -> usize {
        let mut n = 0usize;
        for k in keys {
            n += (*k < target) as usize;
        }
        n
    }
    #[inline(always)]
    fn find_gt<W: Copy + Ord>(keys: &[W], target: W) -> usize {
        let mut n = 0usize;
        for k in keys {
            n += (*k <= target) as usize;
        }
        n
    }
}

// ===========================================================================
// BPlusTreeSet
// ===========================================================================

#[derive(Clone, Copy, Default)]
struct BPlusHeader<I: Copy> {
    root: I,
    last_leaf: I,
    nkeys: usize,
}

#[derive(Clone)]
pub struct BPlusToken {
    nodes_token: crate::VecToken,
    meta_token: crate::VecToken,
}

/// Arena-backed B+Tree set of `DenseId` keys.
///
/// `K::Index` (the raw word: u32 or u64) must match `L::Word`.
pub struct BPlusTreeSet<
    K: DenseId,
    L: NodeLayout<Word = <K as DenseId>::Index> = Layout64U32,
    S: SearchKind = BinarySearch,
    const TRACK: bool = true,
> where
    <K as DenseId>::Index: IndexLike,
{
    nodes: crate::VecI<L::Node, L::ArenaIdx, TRACK>,
    meta: crate::VecP<BPlusHeader<L::ArenaIdx>, u32, TRACK>,
    _k: PhantomData<K>,
    _s: PhantomData<S>,
}

impl<K, L, S, const TRACK: bool> Default for BPlusTreeSet<K, L, S, TRACK>
where
    K: DenseId,
    L: NodeLayout<Word = <K as DenseId>::Index>,
    S: SearchKind,
    <K as DenseId>::Index: IndexLike,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, L, S, const TRACK: bool> BPlusTreeSet<K, L, S, TRACK>
where
    K: DenseId,
    L: NodeLayout<Word = <K as DenseId>::Index>,
    S: SearchKind,
    <K as DenseId>::Index: IndexLike,
{
    /// NIL sentinel value for `L::ArenaIdx`. `u32::MAX` for u32 arenas,
    /// `usize::MAX` for usize arenas. `alloc_*` asserts we never reach it.
    #[inline(always)]
    fn nil() -> L::ArenaIdx {
        <L::ArenaIdx as IndexLike>::MAX
    }

    pub fn new() -> Self {
        let nil = Self::nil();
        let mut s = Self {
            nodes: crate::VecI::new(),
            meta: crate::VecP::new(),
            _k: PhantomData,
            _s: PhantomData,
        };
        s.meta.push(BPlusHeader {
            root: nil,
            last_leaf: nil,
            nkeys: 0,
        });
        let r = s.alloc_leaf();
        s.set_root(r);
        s.set_last_leaf(r);
        s
    }

    #[inline(always)]
    fn key_to_word(k: K) -> L::Word {
        k.into()
    }

    #[inline(always)]
    fn root(&self) -> L::ArenaIdx {
        self.meta.get(0u32).root
    }
    #[inline(always)]
    fn last_leaf(&self) -> L::ArenaIdx {
        self.meta.get(0u32).last_leaf
    }
    #[inline(always)]
    fn nkeys(&self) -> usize {
        self.meta.get(0u32).nkeys
    }
    #[inline(always)]
    fn set_root(&mut self, v: L::ArenaIdx) {
        let mut h = self.meta.get(0u32);
        h.root = v;
        self.meta.set(0u32, h);
    }
    #[inline(always)]
    fn set_last_leaf(&mut self, v: L::ArenaIdx) {
        let mut h = self.meta.get(0u32);
        h.last_leaf = v;
        self.meta.set(0u32, h);
    }
    #[inline(always)]
    fn set_nkeys(&mut self, v: usize) {
        let mut h = self.meta.get(0u32);
        h.nkeys = v;
        self.meta.set(0u32, h);
    }

    pub fn mark(&mut self, shrink: crate::ShrinkPolicy) -> BPlusToken {
        BPlusToken {
            nodes_token: self.nodes.mark(shrink),
            meta_token: self.meta.mark(shrink),
        }
    }
    pub fn restore(&mut self, token: BPlusToken)
    where
        L::Node: Default,
    {
        self.nodes.restore(token.nodes_token);
        self.meta.restore(token.meta_token);
    }

    #[inline(always)]
    fn node(&self, idx: L::ArenaIdx) -> L::Node {
        self.nodes.get(idx)
    }
    #[inline(always)]
    fn set_node(&mut self, idx: L::ArenaIdx, node: L::Node) {
        self.nodes.set(idx, node);
    }

    pub fn is_empty(&self) -> bool {
        self.nkeys() == 0
    }
    pub fn len(&self) -> usize {
        self.nkeys()
    }

    fn alloc_leaf(&mut self) -> L::ArenaIdx {
        let idx = self.nodes.len();
        assert!(
            idx < Self::nil(),
            "BPlusTreeSet arena exhausted: ArenaIdx::MAX reserved as NIL"
        );
        self.nodes.push(L::new_leaf());
        idx
    }
    fn alloc_internal(&mut self) -> L::ArenaIdx {
        let idx = self.nodes.len();
        assert!(
            idx < Self::nil(),
            "BPlusTreeSet arena exhausted: ArenaIdx::MAX reserved as NIL"
        );
        self.nodes.push(L::new_internal());
        idx
    }

    fn first_key_word(&self, idx: L::ArenaIdx) -> L::Word {
        let node = self.node(idx);
        if L::is_leaf(&node) {
            L::data(&node)[0]
        } else {
            self.first_key_word(L::internal_child(&node, 0))
        }
    }

    /// Build from a sorted, deduplicated slice of keys. O(N).
    pub fn from_sorted(sorted: &[K]) -> Self {
        if sorted.is_empty() {
            return Self::new();
        }

        // Convert user keys → raw words up-front.
        let words: Vec<L::Word> = sorted.iter().map(|&k| Self::key_to_word(k)).collect();

        let nil = Self::nil();
        let mut s = Self {
            nodes: crate::VecI::new(),
            meta: crate::VecP::new(),
            _k: PhantomData,
            _s: PhantomData,
        };
        s.meta.push(BPlusHeader {
            root: nil,
            last_leaf: nil,
            nkeys: 0,
        });
        s.set_nkeys(sorted.len());

        let mut leaf_indices: Vec<L::ArenaIdx> = Vec::new();
        for chunk in words.chunks(L::LEAF_CAP) {
            let idx = s.alloc_leaf();
            let mut node = s.node(idx);
            L::data_mut(&mut node)[..chunk.len()].copy_from_slice(chunk);
            L::set_count(&mut node, chunk.len());
            s.set_node(idx, node);
            leaf_indices.push(idx);
        }

        for i in 0..leaf_indices.len() - 1 {
            let mut node = s.node(leaf_indices[i]);
            L::set_link(&mut node, leaf_indices[i + 1]);
            s.set_node(leaf_indices[i], node);
        }
        s.set_last_leaf(*leaf_indices.last().unwrap());

        if leaf_indices.len() == 1 {
            s.set_root(leaf_indices[0]);
            return s;
        }

        let mut children = leaf_indices;
        while children.len() > 1 {
            let mut next_level = Vec::new();
            for chunk in children.chunks(L::INTERNAL_CHILD_CAP) {
                let idx = s.alloc_internal();
                let n_keys = chunk.len() - 1;
                let mut node = s.node(idx);
                for k in 0..n_keys {
                    L::data_mut(&mut node)[k] = s.first_key_word(chunk[k + 1]);
                }
                L::set_count(&mut node, n_keys);
                for (i, &c) in chunk.iter().enumerate() {
                    L::set_internal_child(&mut node, i, c);
                }
                s.set_node(idx, node);
                next_level.push(idx);
            }
            children = next_level;
        }
        s.set_root(children[0]);
        s
    }

    /// Insert a key. Returns true if newly inserted.
    pub fn insert(&mut self, key: K) -> bool {
        let word = Self::key_to_word(key);
        let nil = Self::nil();

        // Fast path: append to rightmost leaf.
        let ll = self.last_leaf();
        if ll != nil {
            let leaf = self.node(ll);
            let n = L::count(&leaf);
            let data = L::data(&leaf);
            if n > 0 && n < L::LEAF_CAP && word > data[n - 1] {
                let mut leaf = leaf;
                L::data_mut(&mut leaf)[n] = word;
                L::set_count(&mut leaf, n + 1);
                self.set_node(ll, leaf);
                self.set_nkeys(self.nkeys() + 1);
                return true;
            }
        }

        let default_idx: L::ArenaIdx = L::ArenaIdx::default();
        let mut path: [(L::ArenaIdx, usize); 24] = [(default_idx, 0usize); 24];
        debug_assert!(L::MAX_DEPTH <= path.len());
        let mut depth = 0usize;
        let mut idx = self.root();

        loop {
            let nd = self.node(idx);
            if L::is_leaf(&nd) {
                break;
            }
            let n = L::count(&nd);
            let cp = S::find_gt(&L::data(&nd)[..n], word);
            path[depth] = (idx, cp);
            depth += 1;
            idx = L::internal_child(&nd, cp);
        }

        let mut leaf = self.node(idx);
        let n = L::count(&leaf);
        let pos = S::find_ge(&L::data(&leaf)[..n], word);
        if pos < n && L::data(&leaf)[pos] == word {
            return false;
        }
        self.set_nkeys(self.nkeys() + 1);

        if n < L::LEAF_CAP {
            L::data_mut(&mut leaf).copy_within(pos..n, pos + 1);
            L::data_mut(&mut leaf)[pos] = word;
            L::set_count(&mut leaf, n + 1);
            self.set_node(idx, leaf);
            return true;
        }

        let leaf_cap = L::LEAF_CAP;
        let mid = leaf_cap.div_ceil(2);
        let new_right = self.alloc_leaf();
        let old_data: Vec<L::Word> = L::data(&leaf)[..leaf_cap].to_vec();
        let mut right = self.node(new_right);

        if pos < mid {
            let rc = leaf_cap - mid + 1;
            L::data_mut(&mut right)[..rc].copy_from_slice(&old_data[mid - 1..leaf_cap]);
            L::data_mut(&mut leaf).copy_within(pos..mid - 1, pos + 1);
            L::data_mut(&mut leaf)[pos] = word;
            L::set_count(&mut leaf, mid);
            L::set_count(&mut right, rc);
        } else {
            let rpos = pos - mid;
            let rc = leaf_cap - mid + 1;
            L::data_mut(&mut right)[..rpos].copy_from_slice(&old_data[mid..pos]);
            L::data_mut(&mut right)[rpos] = word;
            let tail = leaf_cap - pos;
            L::data_mut(&mut right)[rpos + 1..rpos + 1 + tail]
                .copy_from_slice(&old_data[pos..leaf_cap]);
            L::set_count(&mut leaf, mid);
            L::set_count(&mut right, rc);
        }

        let old_link = L::link(&leaf);
        L::set_link(&mut leaf, new_right);
        L::set_link(&mut right, old_link);
        self.set_node(idx, leaf);
        self.set_node(new_right, right);
        if old_link == nil {
            self.set_last_leaf(new_right);
        }

        let mut pkey = L::data(&self.node(new_right))[0];
        let mut pchild = new_right;

        while depth > 0 {
            depth -= 1;
            let (pidx, cp) = path[depth];
            let mut pnode = self.node(pidx);
            let n = L::count(&pnode);

            if n < L::INTERNAL_KEY_CAP {
                L::data_mut(&mut pnode).copy_within(cp..n, cp + 1);
                L::data_mut(&mut pnode)[cp] = pkey;
                for i in (cp + 1..=n).rev() {
                    let c = L::internal_child(&pnode, i);
                    L::set_internal_child(&mut pnode, i + 1, c);
                }
                L::set_internal_child(&mut pnode, cp + 1, pchild);
                L::set_count(&mut pnode, n + 1);
                self.set_node(pidx, pnode);
                return true;
            }

            let key_cap = L::INTERNAL_KEY_CAP;
            let imid = key_cap / 2;
            let new_int = self.alloc_internal();

            let zero = L::zero();
            let mut kb = vec![zero; key_cap + 1];
            kb[..cp].copy_from_slice(&L::data(&pnode)[..cp]);
            kb[cp] = pkey;
            kb[cp + 1..=n].copy_from_slice(&L::data(&pnode)[cp..n]);

            let mut cb: Vec<L::ArenaIdx> = vec![default_idx; L::INTERNAL_CHILD_CAP + 1];
            for i in 0..=cp {
                cb[i] = L::internal_child(&pnode, i);
            }
            cb[cp + 1] = pchild;
            for i in cp + 1..=n {
                cb[i + 1] = L::internal_child(&pnode, i);
            }

            L::data_mut(&mut pnode)[..imid].copy_from_slice(&kb[..imid]);
            L::set_count(&mut pnode, imid);
            for i in 0..=imid {
                L::set_internal_child(&mut pnode, i, cb[i]);
            }
            self.set_node(pidx, pnode);

            let rk = n - imid;
            let mut rnode = self.node(new_int);
            L::data_mut(&mut rnode)[..rk].copy_from_slice(&kb[imid + 1..=n]);
            L::set_count(&mut rnode, rk);
            for i in 0..=rk {
                L::set_internal_child(&mut rnode, i, cb[imid + 1 + i]);
            }
            self.set_node(new_int, rnode);

            pkey = kb[imid];
            pchild = new_int;
        }

        let new_root = self.alloc_internal();
        let mut rnode = self.node(new_root);
        L::data_mut(&mut rnode)[0] = pkey;
        L::set_count(&mut rnode, 1);
        L::set_internal_child(&mut rnode, 0, self.root());
        L::set_internal_child(&mut rnode, 1, pchild);
        self.set_node(new_root, rnode);
        self.set_root(new_root);
        true
    }

    pub fn cursor(&self) -> BPlusCursor<'_, K, L, S, TRACK> {
        BPlusCursor {
            tree: self,
            node: Self::nil(),
            pos: 0,
            _k: PhantomData,
        }
    }

    fn seek_leaf(&self, word: L::Word) -> (L::ArenaIdx, usize) {
        let mut idx = self.root();
        loop {
            let node = self.node(idx);
            if L::is_leaf(&node) {
                let n = L::count(&node);
                let pos = S::find_ge(&L::data(&node)[..n], word);
                return (idx, pos);
            }
            let n = L::count(&node);
            let child_pos = S::find_gt(&L::data(&node)[..n], word);
            idx = L::internal_child(&node, child_pos);
        }
    }
}

// ===========================================================================
// Cursor
// ===========================================================================

pub struct BPlusCursor<'a, K, L, S, const TRACK: bool>
where
    K: DenseId,
    L: NodeLayout<Word = <K as DenseId>::Index>,
    S: SearchKind,
    <K as DenseId>::Index: IndexLike,
{
    tree: &'a BPlusTreeSet<K, L, S, TRACK>,
    node: L::ArenaIdx,
    pos: usize,
    _k: PhantomData<K>,
}

impl<'a, K, L, S, const TRACK: bool> BPlusCursor<'a, K, L, S, TRACK>
where
    K: DenseId,
    L: NodeLayout<Word = <K as DenseId>::Index>,
    S: SearchKind,
    <K as DenseId>::Index: IndexLike,
{
    #[inline(always)]
    fn nil() -> L::ArenaIdx {
        <L::ArenaIdx as IndexLike>::MAX
    }

    /// Position at the first key ≥ `target`. Fast path checks current leaf
    /// and next linked leaf before falling back to root descent.
    pub fn seek(&mut self, target: K) {
        let nil = Self::nil();
        if self.tree.root() == nil {
            return;
        }
        let word: L::Word = target.into();

        if self.node != nil {
            let cur = self.tree.node(self.node);
            let n = L::count(&cur);
            if n > 0 {
                let last = L::data(&cur)[n - 1];
                if word <= last {
                    self.pos = S::find_ge(&L::data(&cur)[..n], word);
                    return;
                }
                let link = L::link(&cur);
                if link != nil {
                    let nxt = self.tree.node(link);
                    let nn = L::count(&nxt);
                    if nn > 0 && word <= L::data(&nxt)[nn - 1] {
                        self.pos = S::find_ge(&L::data(&nxt)[..nn], word);
                        self.node = link;
                        return;
                    }
                }
            }
        }

        let (leaf, pos) = self.tree.seek_leaf(word);
        let node = self.tree.node(leaf);
        if pos < L::count(&node) {
            self.node = leaf;
            self.pos = pos;
        } else {
            let link = L::link(&node);
            if link == nil {
                self.node = nil;
            } else {
                self.node = link;
                self.pos = 0;
            }
        }
    }

    #[inline(always)]
    pub fn key(&self) -> Option<K> {
        if self.node == Self::nil() {
            return None;
        }
        let node = self.tree.node(self.node);
        if self.pos < L::count(&node) {
            let w = L::data(&node)[self.pos];
            Some(K::from_usize(<L::Word as IndexLike>::as_usize(w)))
        } else {
            None
        }
    }

    #[inline(always)]
    pub fn step(&mut self) {
        if self.node == Self::nil() {
            return;
        }
        self.pos += 1;
        let node = self.tree.node(self.node);
        if self.pos >= L::count(&node) {
            self.node = L::link(&node);
            self.pos = 0;
        }
    }

    pub fn seek_first(&mut self) {
        self.seek(K::from_usize(0));
    }
}

impl<'a, K, L, S, const TRACK: bool> crate::SortedCursor for BPlusCursor<'a, K, L, S, TRACK>
where
    K: DenseId,
    L: NodeLayout<Word = <K as DenseId>::Index>,
    S: SearchKind,
    <K as DenseId>::Index: IndexLike,
{
    type Key = K;
    #[inline]
    fn key(&self) -> Option<K> {
        BPlusCursor::key(self)
    }
    #[inline]
    fn step(&mut self) {
        BPlusCursor::step(self);
    }
    #[inline]
    fn seek(&mut self, target: K) {
        BPlusCursor::seek(self, target);
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // Stamp local 31-bit and 63-bit IDs for testing.
    crate::define_id31! { pub struct TestId31 / StoredTestId31, "t"; }
    crate::define_id63! { pub struct TestId63 / StoredTestId63, "t64"; }

    macro_rules! gen_tests {
        ($mod:ident, $id:ident, $layout:ident, $search:ident) => {
            mod $mod {
                use super::*;
                type Tree = BPlusTreeSet<$id, $layout, $search, true>;

                fn k(n: u32) -> $id {
                    <$id>::new(n as _)
                }

                #[test]
                fn empty() {
                    let t = Tree::new();
                    assert_eq!(t.len(), 0);
                    let mut c = t.cursor();
                    c.seek(k(0));
                    assert_eq!(c.key(), None);
                }

                #[test]
                fn from_sorted_roundtrip() {
                    let data: Vec<$id> = (0..1000u32).map(k).collect();
                    let t = Tree::from_sorted(&data);
                    assert_eq!(t.len(), 1000);
                    let mut c = t.cursor();
                    c.seek(k(0));
                    let keys: Vec<$id> = std::iter::from_fn(|| {
                        let r = c.key();
                        c.step();
                        r
                    })
                    .collect();
                    assert_eq!(keys, data);
                }

                #[test]
                fn insert_and_iterate() {
                    let mut t = Tree::new();
                    for i in 0..500u32 {
                        t.insert(k(i));
                    }
                    let mut c = t.cursor();
                    c.seek(k(0));
                    let keys: Vec<$id> = std::iter::from_fn(|| {
                        let r = c.key();
                        c.step();
                        r
                    })
                    .collect();
                    let expected: Vec<$id> = (0..500u32).map(k).collect();
                    assert_eq!(keys, expected);
                }

                #[test]
                fn insert_reverse_and_dedup() {
                    let mut t = Tree::new();
                    for i in (0..500u32).rev() {
                        t.insert(k(i));
                    }
                    assert!(!t.insert(k(5)));
                    assert_eq!(t.len(), 500);
                }

                #[test]
                fn seek_semantics() {
                    let data: Vec<$id> = [10u32, 20, 30, 40, 50].iter().copied().map(k).collect();
                    let t = Tree::from_sorted(&data);
                    let mut c = t.cursor();
                    c.seek(k(30));
                    assert_eq!(c.key(), Some(k(30)));
                    c.seek(k(25));
                    assert_eq!(c.key(), Some(k(30)));
                    c.seek(k(100));
                    assert_eq!(c.key(), None);
                }
            }
        };
    }

    // u32-backed layouts × both search strategies.
    gen_tests!(t31_l64_bin, TestId31, Layout64U32, BinarySearch);
    gen_tests!(t31_l64_br, TestId31, Layout64U32, Branchless);
    gen_tests!(t31_l128_bin, TestId31, Layout128U32, BinarySearch);
    gen_tests!(t31_l256_bin, TestId31, Layout256U32, BinarySearch);

    // u64-backed layouts × both search strategies on default (512-byte) layout.
    gen_tests!(t63_l128_bin, TestId63, Layout128U64, BinarySearch);
    gen_tests!(t63_l128_br, TestId63, Layout128U64, Branchless);
    gen_tests!(t63_l256_bin, TestId63, Layout256U64, BinarySearch);
    gen_tests!(t63_l512_bin, TestId63, Layout512U64, BinarySearch);
    gen_tests!(t63_l512_br, TestId63, Layout512U64, Branchless);

    /// Verify per-layout node sizes match the expected byte budget.
    #[test]
    fn node_size_invariants() {
        assert_eq!(size_of::<BPlusNode64U32>(), 64);
        assert_eq!(size_of::<BPlusNode128U32>(), 128);
        assert_eq!(size_of::<BPlusNode256U32>(), 256);
        assert_eq!(size_of::<BPlusNode128U64>(), 128);
        assert_eq!(size_of::<BPlusNode256U64>(), 256);
        assert_eq!(size_of::<BPlusNode512U64>(), 512);
    }

    /// Verify u32 layouts still use u32 arena index and u64 layouts use usize.
    #[test]
    fn arena_idx_widths() {
        assert_eq!(size_of::<<Layout256U32 as NodeLayout>::ArenaIdx>(), 4);
        assert_eq!(
            size_of::<<Layout512U64 as NodeLayout>::ArenaIdx>(),
            size_of::<usize>()
        );
    }
}
