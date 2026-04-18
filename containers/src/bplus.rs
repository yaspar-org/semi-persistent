// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Arena-backed B+Tree set of `u32` keys.
//!
//! All nodes — leaf and internal — share a single 64-byte
//! cache-aligned struct [`BPlusNode`] in a `VecI<BPlusNode>` arena.
//!
//! Fields are ordered to match the leaf iteration access pattern:
//! check flags → read count → scan data → follow link to next leaf.
//!
//! Leaves pack up to 14 `u32` keys and have a `link` pointer to the
//! next leaf for O(1) `step()`. Internal nodes hold up to 7 keys and
//! 8 child pointers (branching factor 8).

const LEAF_CAP: usize = 14;
const INTERNAL_KEY_CAP: usize = 7;
const INTERNAL_CHILD_CAP: usize = 8; // keys + 1
const NIL: u32 = u32::MAX;

const FLAG_LEAF: u8 = 0x01;
const FLAG_TAG: u8 = 0x02;

/// 64-byte cache-aligned B+Tree node.
///
/// Layout: `[flags:u8] [count:u8] [_pad:u16] [data: [u32; 14]] [link:u32]`
///
/// - `flags`: bit 0 = is_leaf, bit 1 = capture tag (for semi-persistent `VecI`)
/// - `count`: plain element count (max 14 for leaves, max 7 for internal)
/// - `data`: leaf: up to 14 sorted keys; internal: 7 keys in `[0..7]` + 7 children in `[7..14]`
/// - `link`: leaf: next-leaf index (NIL = end); internal: 8th child pointer
#[derive(Clone, Copy)]
#[repr(C, align(64))]
pub struct BPlusNode {
    flags: u8,
    count: u8,
    _pad: u16,
    data: [u32; 14],
    link: u32,
}

const _: () = assert!(size_of::<BPlusNode>() == 64);

impl crate::Tagged for BPlusNode {
    type Repr = BPlusNode;

    #[inline(always)]
    fn into_repr(self) -> BPlusNode {
        let mut r = self;
        r.flags &= !FLAG_TAG;
        r
    }

    #[inline(always)]
    fn from_repr(r: &BPlusNode) -> BPlusNode {
        let mut v = *r;
        v.flags &= !FLAG_TAG;
        v
    }

    #[inline(always)]
    fn tag(r: &BPlusNode) -> bool {
        r.flags & FLAG_TAG != 0
    }

    #[inline(always)]
    fn set_tag(r: &mut BPlusNode) {
        r.flags |= FLAG_TAG;
    }

    #[inline(always)]
    fn clear_tag(r: &mut BPlusNode) {
        r.flags &= !FLAG_TAG;
    }
}

impl BPlusNode {
    fn new_leaf() -> Self {
        Self {
            flags: FLAG_LEAF,
            count: 0,
            _pad: 0,
            data: [0; 14],
            link: NIL,
        }
    }

    fn new_internal() -> Self {
        Self {
            flags: 0,
            count: 0,
            _pad: 0,
            data: [0; 14],
            link: 0,
        }
    }

    #[inline(always)]
    fn is_leaf(&self) -> bool {
        self.flags & FLAG_LEAF != 0
    }

    #[inline(always)]
    fn count(&self) -> usize {
        self.count as usize
    }

    #[inline(always)]
    fn set_count(&mut self, n: usize) {
        self.count = n as u8;
    }

    // --- Leaf accessors ---

    #[inline(always)]
    fn leaf_keys(&self) -> &[u32] {
        &self.data[..self.count()]
    }

    #[inline(always)]
    fn leaf_link(&self) -> u32 {
        self.link
    }

    #[inline(always)]
    fn set_leaf_link(&mut self, next: u32) {
        self.link = next;
    }

    // --- Internal accessors ---
    // data[0..7]: keys, data[7..14]: children 0-6, link: child 7 (8th)

    #[inline(always)]
    #[allow(dead_code)]
    fn internal_keys(&self) -> &[u32] {
        &self.data[..self.count()]
    }

    #[inline(always)]
    fn internal_child(&self, i: usize) -> u32 {
        if i < 7 { self.data[7 + i] } else { self.link }
    }

    #[inline(always)]
    fn set_internal_child(&mut self, i: usize, val: u32) {
        if i < 7 {
            self.data[7 + i] = val;
        } else {
            self.link = val;
        }
    }
}

/// Tree metadata, stored in a separate single-element `VecP` so that
/// mark/restore tracks it via the diff log alongside the node arena.
#[derive(Clone)]
struct BPlusHeader {
    root: u32,
    last_leaf: u32,
    nkeys: usize,
}

/// Token for restoring a `BPlusTreeSet` to a previous state.
#[derive(Clone)]
pub struct BPlusToken {
    nodes_token: crate::VecToken,
    meta_token: crate::VecToken,
}

/// Arena-backed B+Tree set.
pub struct BPlusTreeSet<const TRACK: bool = true> {
    nodes: crate::VecI<BPlusNode, u32, TRACK>,
    meta: crate::VecP<BPlusHeader, u32, TRACK>,
}

impl<const TRACK: bool> Default for BPlusTreeSet<TRACK> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const TRACK: bool> BPlusTreeSet<TRACK> {
    pub fn new() -> Self {
        let mut s = Self {
            nodes: crate::VecI::new(),
            meta: crate::VecP::new(),
        };
        s.meta.push(BPlusHeader {
            root: NIL,
            last_leaf: NIL,
            nkeys: 0,
        });
        let r = s.alloc_leaf();
        s.set_root(r);
        s.set_last_leaf(r);
        s.set_last_leaf(r);
        s
    }

    // --- Header accessors ---

    #[inline(always)]
    fn root(&self) -> u32 {
        self.meta.get(0u32).root
    }
    #[inline(always)]
    fn last_leaf(&self) -> u32 {
        self.meta.get(0u32).last_leaf
    }
    #[inline(always)]
    fn nkeys(&self) -> usize {
        self.meta.get(0u32).nkeys
    }

    #[inline(always)]
    fn set_root(&mut self, v: u32) {
        let mut h = self.meta.get(0u32);
        h.root = v;
        self.meta.set(0u32, h);
    }
    #[inline(always)]
    fn set_last_leaf(&mut self, v: u32) {
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

    /// Snapshot the current state. Returns a token for `restore()`.
    pub fn mark(&mut self, shrink: crate::ShrinkPolicy) -> BPlusToken {
        BPlusToken {
            nodes_token: self.nodes.mark(shrink),
            meta_token: self.meta.mark(shrink),
        }
    }

    /// Restore to the state captured by `mark()`.
    pub fn restore(&mut self, token: BPlusToken) {
        self.nodes.restore(token.nodes_token);
        self.meta.restore(token.meta_token);
    }

    // --- Node access helpers ---
    // VecI doesn't expose &mut T indexing. We read-copy-modify-write instead.
    // BPlusNode is 64 bytes (one cache line), so copies are cheap.

    #[inline(always)]
    fn node(&self, idx: u32) -> BPlusNode {
        self.nodes.get(idx)
    }

    #[inline(always)]
    fn set_node(&mut self, idx: u32, node: BPlusNode) {
        self.nodes.set(idx, node);
    }

    pub fn is_empty(&self) -> bool {
        self.nkeys() == 0
    }

    pub fn len(&self) -> usize {
        self.nkeys()
    }

    /// Build from a sorted, deduplicated slice. O(N).
    pub fn from_sorted(sorted: &[u32]) -> Self {
        if sorted.is_empty() {
            return Self::new();
        }

        let mut s = Self {
            nodes: crate::VecI::new(),
            meta: crate::VecP::new(),
        };
        s.meta.push(BPlusHeader {
            root: NIL,
            last_leaf: NIL,
            nkeys: 0,
        });
        s.set_nkeys(sorted.len());

        // 1. Build leaves left-to-right, filling each to capacity.
        let mut leaf_indices = Vec::new();
        for chunk in sorted.chunks(LEAF_CAP) {
            let idx = s.alloc_leaf();
            let mut node = s.node(idx);
            node.data[..chunk.len()].copy_from_slice(chunk);
            node.set_count(chunk.len());
            s.set_node(idx, node);
            leaf_indices.push(idx);
        }

        // Link leaves.
        for i in 0..leaf_indices.len() - 1 {
            let mut node = s.node(leaf_indices[i]);
            node.set_leaf_link(leaf_indices[i + 1]);
            s.set_node(leaf_indices[i], node);
        }

        s.set_last_leaf(*leaf_indices.last().unwrap());

        if leaf_indices.len() == 1 {
            s.set_root(leaf_indices[0]);
            return s;
        }

        // 2. Build internal levels bottom-up.
        let mut children = leaf_indices;
        while children.len() > 1 {
            let mut next_level = Vec::new();
            for chunk in children.chunks(INTERNAL_CHILD_CAP) {
                let idx = s.alloc_internal();
                let n_keys = chunk.len() - 1;
                let mut node = s.node(idx);
                for k in 0..n_keys {
                    node.data[k] = s.first_key(chunk[k + 1] as usize);
                }
                node.set_count(n_keys);
                for (i, &c) in chunk.iter().enumerate() {
                    node.set_internal_child(i, c);
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
    ///
    /// Fast path: if the key is greater than all existing keys and the
    /// rightmost leaf has room, appends in O(1) without tree traversal.
    pub fn insert(&mut self, key: u32) -> bool {
        // Fast path: append to rightmost leaf.
        let ll = self.last_leaf();
        if ll != NIL {
            let leaf = self.node(ll);
            let n = leaf.count();
            if n > 0 && n < LEAF_CAP && key > leaf.data[n - 1] {
                let mut leaf = leaf;
                leaf.data[n] = key;
                leaf.set_count(n + 1);
                self.set_node(ll, leaf);
                self.set_nkeys(self.nkeys() + 1);
                return true;
            }
        }

        // Iterative path-saving descent + splits.
        let mut path: [(u32, usize); 8] = [(0, 0); 8];
        let mut depth = 0usize;
        let mut idx = self.root();

        // 1. Descend to leaf, saving path.
        loop {
            let nd = self.node(idx);
            if nd.is_leaf() {
                break;
            }
            let n = nd.count();
            let cp = nd.data[..n].partition_point(|&k| k <= key);
            path[depth] = (idx, cp);
            depth += 1;
            idx = nd.internal_child(cp);
        }

        // 2. Insert into leaf.
        let mut leaf = self.node(idx);
        let n = leaf.count();
        let pos = leaf.data[..n].partition_point(|&k| k < key);
        if pos < n && leaf.data[pos] == key {
            return false;
        }
        self.set_nkeys(self.nkeys() + 1);

        if n < LEAF_CAP {
            leaf.data.copy_within(pos..n, pos + 1);
            leaf.data[pos] = key;
            leaf.set_count(n + 1);
            self.set_node(idx, leaf);
            return true;
        }

        // 3. Leaf split.
        let mid = LEAF_CAP.div_ceil(2);
        let new_right = self.alloc_leaf();
        let old_data = leaf.data;
        let mut right = self.node(new_right);

        if pos < mid {
            let rc = LEAF_CAP - mid + 1;
            right.data[..rc].copy_from_slice(&old_data[mid - 1..LEAF_CAP]);
            leaf.data.copy_within(pos..mid - 1, pos + 1);
            leaf.data[pos] = key;
            leaf.set_count(mid);
            right.set_count(rc);
        } else {
            let rpos = pos - mid;
            let rc = LEAF_CAP - mid + 1;
            right.data[..rpos].copy_from_slice(&old_data[mid..pos]);
            right.data[rpos] = key;
            let tail = LEAF_CAP - pos;
            right.data[rpos + 1..rpos + 1 + tail].copy_from_slice(&old_data[pos..LEAF_CAP]);
            leaf.set_count(mid);
            right.set_count(rc);
        }

        let old_link = leaf.leaf_link();
        leaf.set_leaf_link(new_right);
        right.set_leaf_link(old_link);
        self.set_node(idx, leaf);
        self.set_node(new_right, right);
        if old_link == NIL {
            self.set_last_leaf(new_right);
        }

        let mut pkey = self.node(new_right).data[0];
        let mut pchild = new_right;

        // 4. Propagate splits up.
        while depth > 0 {
            depth -= 1;
            let (pidx, cp) = path[depth];
            let mut pnode = self.node(pidx);
            let n = pnode.count();

            if n < INTERNAL_KEY_CAP {
                pnode.data.copy_within(cp..n, cp + 1);
                pnode.data[cp] = pkey;
                for i in (cp + 1..=n).rev() {
                    let c = pnode.internal_child(i);
                    pnode.set_internal_child(i + 1, c);
                }
                pnode.set_internal_child(cp + 1, pchild);
                pnode.set_count(n + 1);
                self.set_node(pidx, pnode);
                return true;
            }

            // Internal split.
            let imid = INTERNAL_KEY_CAP / 2;
            let new_int = self.alloc_internal();

            let mut kb = [0u32; INTERNAL_KEY_CAP + 1];
            kb[..cp].copy_from_slice(&pnode.data[..cp]);
            kb[cp] = pkey;
            kb[cp + 1..=n].copy_from_slice(&pnode.data[cp..n]);

            let mut cb = [0u32; INTERNAL_CHILD_CAP + 1];
            for i in 0..=cp {
                cb[i] = pnode.internal_child(i);
            }
            cb[cp + 1] = pchild;
            for i in cp + 1..=n {
                cb[i + 1] = pnode.internal_child(i);
            }

            pnode.data[..imid].copy_from_slice(&kb[..imid]);
            pnode.set_count(imid);
            for i in 0..=imid {
                pnode.set_internal_child(i, cb[i]);
            }
            self.set_node(pidx, pnode);

            let rk = n - imid;
            let mut rnode = self.node(new_int);
            rnode.data[..rk].copy_from_slice(&kb[imid + 1..=n]);
            rnode.set_count(rk);
            for i in 0..=rk {
                rnode.set_internal_child(i, cb[imid + 1 + i]);
            }
            self.set_node(new_int, rnode);

            pkey = kb[imid];
            pchild = new_int;
        }

        // 5. Root split.
        let new_root = self.alloc_internal();
        let mut rnode = self.node(new_root);
        rnode.data[0] = pkey;
        rnode.set_count(1);
        rnode.set_internal_child(0, self.root());
        rnode.set_internal_child(1, pchild);
        self.set_node(new_root, rnode);
        self.set_root(new_root);
        true
    }

    /// Seek-based cursor for iteration.
    pub fn cursor(&self) -> BPlusCursor<'_, TRACK> {
        BPlusCursor {
            tree: self,
            node: NIL,
            pos: 0,
        }
    }

    // --- Internal helpers ---

    fn alloc_leaf(&mut self) -> u32 {
        let idx = self.nodes.len();
        self.nodes.push(BPlusNode::new_leaf());
        idx
    }

    fn alloc_internal(&mut self) -> u32 {
        let idx = self.nodes.len();
        self.nodes.push(BPlusNode::new_internal());
        idx
    }

    fn first_key(&self, node_idx: usize) -> u32 {
        let node = self.node(node_idx as u32);
        if node.is_leaf() {
            node.data[0]
        } else {
            self.first_key(node.internal_child(0) as usize)
        }
    }

    /// Find the leftmost leaf and position for seek.
    fn seek_leaf(&self, key: u32) -> (u32, usize) {
        let mut idx = self.root();
        loop {
            let node = self.node(idx);
            if node.is_leaf() {
                let pos = node.leaf_keys().partition_point(|&k| k < key);
                return (idx, pos);
            }
            let n = node.count();
            let child_pos = node.data[..n].partition_point(|&k| k <= key);
            idx = node.internal_child(child_pos);
        }
    }
}

/// Cursor for iteration over a `BPlusTreeSet`.
pub struct BPlusCursor<'a, const TRACK: bool> {
    tree: &'a BPlusTreeSet<TRACK>,
    node: u32,  // current leaf index (NIL = invalid)
    pos: usize, // position within leaf
}

impl<'a, const TRACK: bool> BPlusCursor<'a, TRACK> {
    /// Position at the first key >= target.
    pub fn seek(&mut self, target: u32) {
        if self.tree.root() == NIL {
            return;
        }
        let (leaf, pos) = self.tree.seek_leaf(target);
        let node = self.tree.node(leaf);
        if pos < node.count() {
            self.node = leaf;
            self.pos = pos;
        } else {
            let link = node.leaf_link();
            if link == NIL {
                self.node = NIL;
            } else {
                self.node = link;
                self.pos = 0;
            }
        }
    }

    /// Current key, or None if exhausted.
    #[inline(always)]
    pub fn key(&self) -> Option<u32> {
        if self.node == NIL {
            return None;
        }
        let node = self.tree.node(self.node);
        if self.pos < node.count() {
            Some(node.data[self.pos])
        } else {
            None
        }
    }

    /// Advance to next key.
    #[inline(always)]
    pub fn step(&mut self) {
        if self.node == NIL {
            return;
        }
        self.pos += 1;
        let node = self.tree.node(self.node);
        if self.pos >= node.count() {
            self.node = node.leaf_link();
            self.pos = 0;
        }
    }

    /// Seek to first, then iterate all keys.
    pub fn seek_first(&mut self) {
        self.seek(0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Tree = BPlusTreeSet<true>;

    #[test]
    fn empty() {
        let t = Tree::new();
        assert_eq!(t.len(), 0);
        let mut c = t.cursor();
        c.seek(0);
        assert_eq!(c.key(), None);
    }

    #[test]
    fn from_sorted_small() {
        let t = Tree::from_sorted(&[1, 3, 5, 7, 9]);
        assert_eq!(t.len(), 5);
        let mut c = t.cursor();
        c.seek(0);
        let keys: Vec<u32> = std::iter::from_fn(|| {
            let k = c.key();
            c.step();
            k
        })
        .collect();
        assert_eq!(keys, vec![1, 3, 5, 7, 9]);
    }

    #[test]
    fn from_sorted_large() {
        let data: Vec<u32> = (0..1000).collect();
        let t = Tree::from_sorted(&data);
        assert_eq!(t.len(), 1000);
        let mut c = t.cursor();
        c.seek(0);
        let keys: Vec<u32> = std::iter::from_fn(|| {
            let k = c.key();
            c.step();
            k
        })
        .collect();
        assert_eq!(keys, data);
    }

    #[test]
    fn seek_exact() {
        let t = Tree::from_sorted(&[10, 20, 30, 40, 50]);
        let mut c = t.cursor();
        c.seek(30);
        assert_eq!(c.key(), Some(30));
    }

    #[test]
    fn seek_between() {
        let t = Tree::from_sorted(&[10, 20, 30, 40, 50]);
        let mut c = t.cursor();
        c.seek(25);
        assert_eq!(c.key(), Some(30));
    }

    #[test]
    fn seek_past_end() {
        let t = Tree::from_sorted(&[10, 20, 30]);
        let mut c = t.cursor();
        c.seek(100);
        assert_eq!(c.key(), None);
    }

    #[test]
    fn insert_basic() {
        let mut t = Tree::new();
        assert!(t.insert(5));
        assert!(t.insert(3));
        assert!(t.insert(7));
        assert!(!t.insert(5)); // duplicate
        assert_eq!(t.len(), 3);
        let mut c = t.cursor();
        c.seek(0);
        let keys: Vec<u32> = std::iter::from_fn(|| {
            let k = c.key();
            c.step();
            k
        })
        .collect();
        assert_eq!(keys, vec![3, 5, 7]);
    }

    #[test]
    fn insert_causes_splits() {
        let mut t = Tree::new();
        for i in 0..100 {
            t.insert(i);
        }
        assert_eq!(t.len(), 100);
        let mut c = t.cursor();
        c.seek(0);
        let keys: Vec<u32> = std::iter::from_fn(|| {
            let k = c.key();
            c.step();
            k
        })
        .collect();
        let expected: Vec<u32> = (0..100).collect();
        assert_eq!(keys, expected);
    }

    #[test]
    fn insert_reverse() {
        let mut t = Tree::new();
        for i in (0..100).rev() {
            t.insert(i);
        }
        assert_eq!(t.len(), 100);
        let mut c = t.cursor();
        c.seek(0);
        let keys: Vec<u32> = std::iter::from_fn(|| {
            let k = c.key();
            c.step();
            k
        })
        .collect();
        let expected: Vec<u32> = (0..100).collect();
        assert_eq!(keys, expected);
    }

    #[test]
    fn insert_random_then_iterate() {
        let mut t = Tree::new();
        let vals = [42, 17, 99, 3, 55, 71, 8, 33, 61, 25, 88, 14, 47, 76, 2, 90];
        for &v in &vals {
            t.insert(v);
        }
        assert_eq!(t.len(), vals.len());
        let mut c = t.cursor();
        c.seek(0);
        let keys: Vec<u32> = std::iter::from_fn(|| {
            let k = c.key();
            c.step();
            k
        })
        .collect();
        let mut expected = vals.to_vec();
        expected.sort();
        assert_eq!(keys, expected);
    }

    #[test]
    fn seek_after_insert() {
        let mut t = Tree::new();
        for i in (0..200).step_by(2) {
            t.insert(i);
        }
        let mut c = t.cursor();
        c.seek(51);
        assert_eq!(c.key(), Some(52));
        c.seek(100);
        assert_eq!(c.key(), Some(100));
        c.seek(199);
        assert_eq!(c.key(), None);
    }
}
