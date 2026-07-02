// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Generic node caches — hash-consing tables parameterized by id types.
//!
//! - `FixedArityCache<G, O, L, K, TRACK>` — for Plain0..3 and Commutative
//! - `VariableArityCache<G, O, C, L, TRACK>` — for PlainN, A, AC, ACI
//! - `LitCache<G, O, V, L, TRACK>` — for literal leaves

use std::hash::{BuildHasher, Hash, Hasher};

use crate::canon::{FixedCanon, VarCanon};
use crate::containers::DenseId;
use crate::containers::Tagged;
use crate::containers::{InlineStore, ShrinkPolicy, VecI, VecToken};
use crate::node_types::{FixedArityNode, LitNode, VariableArityNode};

// ---------------------------------------------------------------------------
// Shared infrastructure
// ---------------------------------------------------------------------------

#[derive(Default, Clone)]
struct PassthroughHasher(u64);

impl Hasher for PassthroughHasher {
    fn write(&mut self, _bytes: &[u8]) {}
    fn write_u64(&mut self, i: u64) {
        self.0 = i;
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

#[derive(Default, Clone)]
struct PassthroughBuildHasher;

impl BuildHasher for PassthroughBuildHasher {
    type Hasher = PassthroughHasher;
    fn build_hasher(&self) -> PassthroughHasher {
        PassthroughHasher(0)
    }
}

#[derive(Clone, Copy, Debug)]
struct StoredKey<L> {
    content_hash: u64,
    local_id: L,
}

impl<L> Hash for StoredKey<L> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.content_hash);
    }
}
impl<L: PartialEq> PartialEq for StoredKey<L> {
    fn eq(&self, other: &Self) -> bool {
        self.local_id == other.local_id
    }
}
impl<L: Eq> Eq for StoredKey<L> {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InsertResult<G, L> {
    Hit { global_id: G },
    Inserted { local_id: L },
}

#[derive(Clone, Copy, Debug)]
pub struct CacheToken {
    nodes: VecToken,
    history: Option<VecToken>,
}

#[derive(Clone, Copy, Debug)]
pub struct PoolCacheToken {
    nodes: VecToken,
    children: VecToken,
    history_nodes: Option<VecToken>,
    history_children: Option<VecToken>,
}

// ---------------------------------------------------------------------------
// FixedArityCache<G, O, L, K, TRACK, PROOFS>
// ---------------------------------------------------------------------------

pub struct FixedArityCache<
    G: DenseId,
    O: DenseId,
    L: DenseId,
    const K: usize,
    const TRACK: bool = true,
    const PROOFS: bool = false,
> {
    nodes: VecI<FixedArityNode<G, O, K>, L, TRACK>,
    index: hashbrown::HashMap<StoredKey<L>, G, PassthroughBuildHasher>,
    history: Option<VecI<FixedArityNode<G, O, K>, usize, TRACK>>,
}

impl<
    G: DenseId + Hash,
    O: DenseId + Hash,
    L: DenseId,
    const K: usize,
    const TRACK: bool,
    const PROOFS: bool,
> Default for FixedArityCache<G, O, L, K, TRACK, PROOFS>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<
    G: DenseId + Hash,
    O: DenseId + Hash,
    L: DenseId,
    const K: usize,
    const TRACK: bool,
    const PROOFS: bool,
> FixedArityCache<G, O, L, K, TRACK, PROOFS>
{
    pub fn new() -> Self {
        Self {
            nodes: VecI::with_store(InlineStore::new()),
            index: hashbrown::HashMap::with_hasher(PassthroughBuildHasher),
            history: if PROOFS {
                Some(VecI::with_store(InlineStore::new()))
            } else {
                None
            },
        }
    }

    pub fn len(&self) -> L {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.len() == L::MIN
    }

    pub fn get(&self, id: L) -> FixedArityNode<G, O, K> {
        self.nodes.get(id)
    }

    pub fn set(&mut self, id: L, node: FixedArityNode<G, O, K>) {
        self.nodes.set(id, node);
    }

    pub fn probe(&self, op: &O, children: &[G; K]) -> Option<G> {
        let h = self.hash_content(op, children);
        self.index
            .raw_entry()
            .from_hash(h, |sk| {
                sk.content_hash == h && {
                    let n = self.nodes.get(sk.local_id);
                    n.op() == *op && n.children == *children
                }
            })
            .map(|(_, &gid)| gid)
    }

    pub fn insert(&mut self, global_id: G, op: O, children: [G; K]) -> L {
        let node = FixedArityNode::new(global_id, op, children);
        let h = self.hash_content(&op, &children);
        let lid = self.nodes.len();
        self.nodes.push(node);
        self.index.insert(
            StoredKey {
                content_hash: h,
                local_id: lid,
            },
            global_id,
        );
        lid
    }

    pub fn probe_or_insert(&mut self, global_id: G, op: O, children: [G; K]) -> InsertResult<G, L> {
        if let Some(gid) = self.probe(&op, &children) {
            return InsertResult::Hit { global_id: gid };
        }
        let lid = self.insert(global_id, op, children);
        InsertResult::Inserted { local_id: lid }
    }

    pub fn node_get(&self, id: L) -> FixedArityNode<G, O, K> {
        self.nodes.get(id)
    }

    pub fn node_set(&mut self, id: L, node: FixedArityNode<G, O, K>) {
        self.nodes.set(id, node);
    }

    /// Recanonize a single node's children. Pushes collision pair into
    /// `collisions` if the new canonical form matches an existing node.
    /// When `PROOFS=true`, saves the original node to history on first recanonize.
    pub fn recanonize_node<F: FixedCanon<G, K>>(
        &mut self,
        local_id: L,
        find: impl Fn(G) -> G,
        collisions: &mut Vec<(G, G)>,
        touched: &mut Vec<G>,
    ) {
        let mut node = self.nodes.get(local_id);
        let old_hash = self.hash_content(&node.op(), &node.children);

        F::canonize(&mut node.children, &find);

        let new_hash = self.hash_content(&node.op(), &node.children);
        if new_hash == old_hash {
            let old = self.nodes.get(local_id);
            if old.children == node.children {
                return;
            }
        }

        // Node's canonical form genuinely changed this round — record it for
        // the semi-naive delta (after the no-change early-return above).
        touched.push(node.global_id());

        // save to history on first recanonize
        if let Some(hist) = &mut self.history
            && !node.has_history()
        {
            hist.push(self.nodes.get(local_id));
        }

        self.index.remove(&StoredKey {
            content_hash: old_hash,
            local_id,
        });

        let gid = node.global_id();
        let mut new_node = FixedArityNode::new(gid, node.op(), node.children);
        if PROOFS {
            new_node.set_history();
        }
        self.nodes.set(local_id, new_node);

        if let Some(existing_gid) = self.probe(&node.op(), &node.children) {
            collisions.push((gid, existing_gid));
        }

        self.index.insert(
            StoredKey {
                content_hash: new_hash,
                local_id,
            },
            gid,
        );
    }

    /// Retrieve the original (pre-recanonize) children for a node by global id.
    /// Linear scan of the history store. Returns `None` if no history or not found.
    pub fn original_children(&self, global_id: G) -> Option<[G; K]> {
        let hist = self.history.as_ref()?;
        let len = hist.len();
        for i in 0..len {
            let node = hist.get(i);
            if node.global_id() == global_id {
                return Some(node.children);
            }
        }
        None
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> CacheToken {
        CacheToken {
            nodes: self.nodes.mark(shrink),
            history: self.history.as_mut().map(|h| h.mark(shrink)),
        }
    }

    pub fn restore(&mut self, token: CacheToken) {
        self.nodes.restore(token.nodes);
        if let (Some(h), Some(tok)) = (&mut self.history, token.history) {
            h.restore(tok);
        }
        self.rebuild_index();
    }

    fn rebuild_index(&mut self) {
        self.index.clear();
        let count = self.nodes.len().as_usize();
        for i in 0..count {
            let lid = L::from_usize(i);
            let n = self.nodes.get(lid);
            let h = n.content_hash();
            self.index.insert(
                StoredKey {
                    content_hash: h,
                    local_id: L::from_usize(i),
                },
                n.global_id(),
            );
        }
    }

    fn hash_content(&self, op: &O, children: &[G; K]) -> u64 {
        let mut h = rapidhash::fast::RapidHasher::default();
        op.hash(&mut h);
        children.hash(&mut h);
        h.finish()
    }
}

// ---------------------------------------------------------------------------
// VariableArityCache<G, O, C, L, TRACK, PROOFS>
// ---------------------------------------------------------------------------

pub struct VariableArityCache<
    G: DenseId,
    O: DenseId,
    C: Tagged + Clone + Copy + Hash + Eq,
    L: DenseId,
    const TRACK: bool = true,
    const PROOFS: bool = false,
> {
    nodes: VecI<VariableArityNode<G, O>, L, TRACK>,
    children: VecI<C, usize, TRACK>,
    index: hashbrown::HashMap<StoredKey<L>, G, PassthroughBuildHasher>,
    history_nodes: Option<VecI<VariableArityNode<G, O>, usize, TRACK>>,
    history_children: Option<VecI<C, usize, TRACK>>,
}

impl<
    G: DenseId + Hash,
    O: DenseId + Hash,
    C: Tagged + Clone + Copy + Hash + Eq + core::fmt::Debug,
    L: DenseId,
    const TRACK: bool,
    const PROOFS: bool,
> Default for VariableArityCache<G, O, C, L, TRACK, PROOFS>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<
    G: DenseId + Hash,
    O: DenseId + Hash,
    C: Tagged + Clone + Copy + Hash + Eq + core::fmt::Debug,
    L: DenseId,
    const TRACK: bool,
    const PROOFS: bool,
> VariableArityCache<G, O, C, L, TRACK, PROOFS>
{
    pub fn new() -> Self {
        Self {
            nodes: VecI::with_store(InlineStore::new()),
            children: VecI::with_store(InlineStore::new()),
            index: hashbrown::HashMap::with_hasher(PassthroughBuildHasher),
            history_nodes: if PROOFS {
                Some(VecI::with_store(InlineStore::new()))
            } else {
                None
            },
            history_children: if PROOFS {
                Some(VecI::with_store(InlineStore::new()))
            } else {
                None
            },
        }
    }

    pub fn len(&self) -> L {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.len() == L::MIN
    }

    pub fn get(&self, id: L) -> VariableArityNode<G, O> {
        self.nodes.get(id)
    }

    pub fn set(&mut self, id: L, node: VariableArityNode<G, O>) {
        self.nodes.set(id, node);
    }

    pub fn children_vec(&self, node: &VariableArityNode<G, O>) -> Vec<C> {
        let (start, end) = node.span();
        (start..end).map(|i| self.children.get(i)).collect()
    }

    pub fn pool_get(&self, i: usize) -> C {
        self.children.get(i)
    }

    pub fn pool_set(&mut self, i: usize, value: C) {
        self.children.set(i, value);
    }

    pub fn probe(&self, op: O, elems: &[C]) -> Option<G> {
        let h = self.hash_content(&op, elems);
        self.index
            .raw_entry()
            .from_hash(h, |sk| {
                sk.content_hash == h && {
                    let n = self.nodes.get(sk.local_id);
                    n.op() == op && self.children_eq(&n, elems)
                }
            })
            .map(|(_, &gid)| gid)
    }

    pub fn insert(&mut self, global_id: G, op: O, elems: &[C]) -> L {
        let start = self.children.len();
        for &e in elems {
            self.children.push(e);
        }
        let end = self.children.len();
        let node = VariableArityNode::make(global_id, op, start, end);
        let h = self.hash_content(&op, elems);
        let lid = self.nodes.len();
        self.nodes.push(node);
        self.index.insert(
            StoredKey {
                content_hash: h,
                local_id: lid,
            },
            global_id,
        );
        lid
    }

    pub fn probe_or_insert(&mut self, global_id: G, op: O, elems: &[C]) -> InsertResult<G, L> {
        if let Some(gid) = self.probe(op, elems) {
            return InsertResult::Hit { global_id: gid };
        }
        let lid = self.insert(global_id, op, elems);
        InsertResult::Inserted { local_id: lid }
    }

    pub fn node_get(&self, id: L) -> VariableArityNode<G, O> {
        self.nodes.get(id)
    }

    pub fn node_set(&mut self, id: L, node: VariableArityNode<G, O>) {
        self.nodes.set(id, node);
    }

    /// Recanonize a single node's children. `buf` is a caller-owned scratch
    /// buffer, cleared internally. Pushes collision pair into `collisions`
    /// if the new canonical form matches an existing node.
    /// When `PROOFS=true`, saves the original node+children to history on first recanonize.
    pub fn recanonize_node<V: VarCanon<G, C>>(
        &mut self,
        local_id: L,
        find: impl Fn(G) -> G,
        buf: &mut Vec<C>,
        collisions: &mut Vec<(G, G)>,
        touched: &mut Vec<G>,
        mode: crate::canon::MSetClamp,
    ) {
        let node = self.nodes.get(local_id);
        let (start, end) = node.span();
        let old_hash = self.hash_children(&node);

        buf.clear();
        V::canonize(buf, start, end, |i| self.children.get(i), &find, mode);

        let new_len = buf.len();

        if new_len == end - start {
            let mut same = true;
            for i in 0..new_len {
                if buf[i] != self.children.get(start + i) {
                    same = false;
                    break;
                }
            }
            if same {
                return;
            }
        }

        // Node's canonical form genuinely changed this round — record it for
        // the semi-naive delta (after the no-change early-return above).
        touched.push(node.global_id());

        // save to history on first recanonize
        if let (Some(hn), Some(hc)) = (&mut self.history_nodes, &mut self.history_children)
            && !node.has_history()
        {
            let hist_start = hc.len();
            for i in start..end {
                hc.push(self.children.get(i));
            }
            let hist_end = hc.len();
            hn.push(VariableArityNode::make(
                node.global_id(),
                node.op(),
                hist_start,
                hist_end,
            ));
        }

        self.index.remove(&StoredKey {
            content_hash: old_hash,
            local_id,
        });

        for i in 0..new_len {
            self.children.set(start + i, buf[i]);
        }

        let new_end = start + new_len;
        let gid = node.global_id();
        let mut updated = VariableArityNode::make(gid, node.op(), start, new_end);
        if PROOFS {
            updated.set_history();
        }
        if new_end != end || PROOFS {
            self.nodes.set(local_id, updated);
        }

        let new_hash = self.hash_content(&node.op(), &buf[..new_len]);

        if let Some(existing_gid) = self.probe(node.op(), &buf[..new_len]) {
            collisions.push((gid, existing_gid));
        }

        self.index.insert(
            StoredKey {
                content_hash: new_hash,
                local_id,
            },
            gid,
        );
    }

    /// Retrieve the original (pre-recanonize) children for a node by global id.
    /// Linear scan of the history store. Appends children to `out`.
    /// Returns `true` if found.
    pub fn original_children(&self, global_id: G, out: &mut Vec<C>) -> bool {
        let (hn, hc) = match (&self.history_nodes, &self.history_children) {
            (Some(hn), Some(hc)) => (hn, hc),
            _ => return false,
        };
        let len = hn.len();
        for i in 0..len {
            let node = hn.get(i);
            if node.global_id() == global_id {
                let (s, e) = node.span();
                for j in s..e {
                    out.push(hc.get(j));
                }
                return true;
            }
        }
        false
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> PoolCacheToken {
        PoolCacheToken {
            nodes: self.nodes.mark(shrink),
            children: self.children.mark(shrink),
            history_nodes: self.history_nodes.as_mut().map(|h| h.mark(shrink)),
            history_children: self.history_children.as_mut().map(|h| h.mark(shrink)),
        }
    }

    pub fn restore(&mut self, token: PoolCacheToken) {
        self.nodes.restore(token.nodes);
        self.children.restore(token.children);
        if let (Some(h), Some(tok)) = (&mut self.history_nodes, token.history_nodes) {
            h.restore(tok);
        }
        if let (Some(h), Some(tok)) = (&mut self.history_children, token.history_children) {
            h.restore(tok);
        }
        self.rebuild_index();
    }

    fn children_eq(&self, node: &VariableArityNode<G, O>, elems: &[C]) -> bool {
        let (start, end) = node.span();
        if end - start != elems.len() {
            return false;
        }
        (0..elems.len()).all(|i| self.children.get(start + i) == elems[i])
    }

    fn rebuild_index(&mut self) {
        self.index.clear();
        let count = self.nodes.len().as_usize();
        for i in 0..count {
            let lid = L::from_usize(i);
            let n = self.nodes.get(lid);
            let h = self.hash_children(&n);
            self.index.insert(
                StoredKey {
                    content_hash: h,
                    local_id: L::from_usize(i),
                },
                n.global_id(),
            );
        }
    }

    fn hash_content(&self, op: &O, elems: &[C]) -> u64 {
        let mut h = rapidhash::fast::RapidHasher::default();
        op.hash(&mut h);
        elems.hash(&mut h);
        h.finish()
    }

    fn hash_children(&self, node: &VariableArityNode<G, O>) -> u64 {
        let mut h = rapidhash::fast::RapidHasher::default();
        node.op().hash(&mut h);
        let (start, end) = node.span();
        (end - start).hash(&mut h);
        for i in start..end {
            self.children.get(i).hash(&mut h);
        }
        h.finish()
    }
}

// ---------------------------------------------------------------------------
// LitCache<G, O, V, L, TRACK>
// ---------------------------------------------------------------------------

pub struct LitCache<G: DenseId, O: DenseId, V: DenseId, L: DenseId, const TRACK: bool = true> {
    nodes: VecI<LitNode<G, O, V>, L, TRACK>,
    index: hashbrown::HashMap<StoredKey<L>, G, PassthroughBuildHasher>,
}

impl<G: DenseId + Hash, O: DenseId + Hash, V: DenseId + Hash, L: DenseId, const TRACK: bool> Default
    for LitCache<G, O, V, L, TRACK>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<G: DenseId + Hash, O: DenseId + Hash, V: DenseId + Hash, L: DenseId, const TRACK: bool>
    LitCache<G, O, V, L, TRACK>
{
    pub fn new() -> Self {
        Self {
            nodes: VecI::with_store(InlineStore::new()),
            index: hashbrown::HashMap::with_hasher(PassthroughBuildHasher),
        }
    }

    pub fn len(&self) -> L {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.len() == L::MIN
    }

    pub fn get(&self, id: L) -> LitNode<G, O, V> {
        self.nodes.get(id)
    }

    pub fn set(&mut self, id: L, node: LitNode<G, O, V>) {
        self.nodes.set(id, node);
    }

    pub fn probe(&self, op: O, lit: V) -> Option<G> {
        let h = self.hash_content(&op, &lit);
        self.index
            .raw_entry()
            .from_hash(h, |sk| {
                sk.content_hash == h && {
                    let n = self.nodes.get(sk.local_id);
                    n.op() == op && n.lit == lit
                }
            })
            .map(|(_, &gid)| gid)
    }

    pub fn insert(&mut self, global_id: G, op: O, lit: V) -> L {
        let node = LitNode::new(global_id, op, lit);
        let h = self.hash_content(&op, &lit);
        let lid = self.nodes.len();
        self.nodes.push(node);
        self.index.insert(
            StoredKey {
                content_hash: h,
                local_id: lid,
            },
            global_id,
        );
        lid
    }

    pub fn probe_or_insert(&mut self, global_id: G, op: O, lit: V) -> InsertResult<G, L> {
        if let Some(gid) = self.probe(op, lit) {
            return InsertResult::Hit { global_id: gid };
        }
        let lid = self.insert(global_id, op, lit);
        InsertResult::Inserted { local_id: lid }
    }

    pub fn mark(&mut self, shrink: ShrinkPolicy) -> CacheToken {
        CacheToken {
            nodes: self.nodes.mark(shrink),
            history: None,
        }
    }

    pub fn restore(&mut self, token: CacheToken) {
        self.nodes.restore(token.nodes);
        self.rebuild_index();
    }

    fn rebuild_index(&mut self) {
        self.index.clear();
        let count = self.nodes.len().as_usize();
        for i in 0..count {
            let lid = L::from_usize(i);
            let n = self.nodes.get(lid);
            let h = n.content_hash();
            self.index.insert(
                StoredKey {
                    content_hash: h,
                    local_id: L::from_usize(i),
                },
                n.global_id(),
            );
        }
    }

    fn hash_content(&self, op: &O, lit: &V) -> u64 {
        let mut h = rapidhash::fast::RapidHasher::default();
        op.hash(&mut h);
        lit.hash(&mut h);
        h.finish()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::canon::{CCanon, MSetCanon, OrderedCanon, PlainCanon, SetCanon};
    use crate::id::{ENodeId, OpId};
    use crate::multiplicity::Multiplicity;
    use crate::nodes::{
        LitNodeId, LitValId, MSetNodeId, Plain0Id, Plain2Id, PlainNId, SPairNodeId, SetNodeId,
    };

    #[test]
    fn fixed_arity_probe_insert() {
        let mut c = FixedArityCache::<ENodeId, OpId, Plain0Id, 0, false>::new();
        let op = OpId::new(0);
        let r = c.probe_or_insert(ENodeId::new(0), op, []);
        assert!(matches!(r, InsertResult::Inserted { .. }));
        let r2 = c.probe_or_insert(ENodeId::new(99), op, []);
        assert!(matches!(r2, InsertResult::Hit { .. }));
    }

    #[test]
    fn fixed_arity_binary() {
        let mut c = FixedArityCache::<ENodeId, OpId, Plain2Id, 2, false>::new();
        let op = OpId::new(0);
        let ch = [ENodeId::new(1), ENodeId::new(2)];
        let r = c.probe_or_insert(ENodeId::new(0), op, ch);
        assert!(matches!(r, InsertResult::Inserted { .. }));
        assert!(c.probe(&op, &ch).is_some());
        assert!(c.probe(&op, &[ENodeId::new(2), ENodeId::new(1)]).is_none());
    }

    #[test]
    fn variable_arity_probe_insert() {
        let mut c = VariableArityCache::<ENodeId, OpId, ENodeId, PlainNId, false>::new();
        let op = OpId::new(0);
        let ch = &[ENodeId::new(1), ENodeId::new(2), ENodeId::new(3)];
        let r = c.probe_or_insert(ENodeId::new(0), op, ch);
        assert!(matches!(r, InsertResult::Inserted { .. }));
        assert!(c.probe(op, ch).is_some());
    }

    #[test]
    fn lit_cache_probe_insert() {
        let mut c = LitCache::<ENodeId, OpId, LitValId, LitNodeId, false>::new();
        let op = OpId::new(0);
        let lit = LitValId::new(42);
        let r = c.probe_or_insert(ENodeId::new(0), op, lit);
        assert!(matches!(r, InsertResult::Inserted { .. }));
        assert!(c.probe(op, lit).is_some());
        assert!(c.probe(op, LitValId::new(99)).is_none());
    }

    // -- recanonize_node tests --

    fn id(n: u32) -> ENodeId {
        ENodeId::new(n)
    }

    #[test]
    fn recanonize_fixed_no_change() {
        let mut c = FixedArityCache::<ENodeId, OpId, Plain2Id, 2, false>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(0), op, [id(1), id(2)]);
        let mut collisions = Vec::new();
        c.recanonize_node::<PlainCanon>(Plain2Id::new(0), |g| g, &mut collisions, &mut Vec::new());
        assert!(collisions.is_empty());
        // node unchanged
        assert!(c.probe(&op, &[id(1), id(2)]).is_some());
    }

    #[test]
    fn recanonize_fixed_plain_updates_children() {
        let mut c = FixedArityCache::<ENodeId, OpId, Plain2Id, 2, false>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(0), op, [id(1), id(2)]);
        let mut collisions = Vec::new();
        // find: 2 → 1
        c.recanonize_node::<PlainCanon>(
            Plain2Id::new(0),
            |g| {
                if g == id(2) { id(1) } else { g }
            },
            &mut collisions,
            &mut Vec::new(),
        );
        assert!(collisions.is_empty());
        // old key gone, new key present
        assert!(c.probe(&op, &[id(1), id(2)]).is_none());
        assert!(c.probe(&op, &[id(1), id(1)]).is_some());
    }

    #[test]
    fn recanonize_fixed_collision() {
        let mut c = FixedArityCache::<ENodeId, OpId, Plain2Id, 2, false>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(10), op, [id(1), id(1)]); // node A: (op, [1,1]) → gid 10
        c.probe_or_insert(id(20), op, [id(1), id(2)]); // node B: (op, [1,2]) → gid 20
        let mut collisions = Vec::new();
        // find: 2 → 1, so node B becomes (op, [1,1]) → collision with A
        c.recanonize_node::<PlainCanon>(
            Plain2Id::new(1),
            |g| {
                if g == id(2) { id(1) } else { g }
            },
            &mut collisions,
            &mut Vec::new(),
        );
        assert_eq!(collisions.len(), 1);
        assert_eq!(collisions[0], (id(20), id(10)));
    }

    #[test]
    fn recanonize_c_sorts_pair() {
        let mut c = FixedArityCache::<ENodeId, OpId, SPairNodeId, 2, false>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(10), op, [id(1), id(5)]); // sorted: [1, 5]
        let mut collisions = Vec::new();
        // find: 1 → 9, so children become [9, 5], CCanon sorts to [5, 9]
        c.recanonize_node::<CCanon>(
            SPairNodeId::new(0),
            |g| {
                if g == id(1) { id(9) } else { g }
            },
            &mut collisions,
            &mut Vec::new(),
        );
        assert!(collisions.is_empty());
        assert!(c.probe(&op, &[id(5), id(9)]).is_some());
    }

    #[test]
    fn recanonize_var_ordered_no_change() {
        let mut c = VariableArityCache::<ENodeId, OpId, ENodeId, PlainNId, false>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(0), op, &[id(1), id(2), id(3)]);
        let mut buf = Vec::new();
        let mut collisions = Vec::new();
        c.recanonize_node::<OrderedCanon>(
            PlainNId::new(0),
            |g| g,
            &mut buf,
            &mut collisions,
            &mut Vec::new(),
            crate::canon::MSetClamp::None,
        );
        assert!(collisions.is_empty());
    }

    #[test]
    fn recanonize_var_ordered_collision() {
        let mut c = VariableArityCache::<ENodeId, OpId, ENodeId, PlainNId, false>::new();
        let op = OpId::new(0);
        c.probe_or_insert(id(10), op, &[id(1), id(1)]);
        c.probe_or_insert(id(20), op, &[id(1), id(2)]);
        let mut buf = Vec::new();
        let mut collisions = Vec::new();
        c.recanonize_node::<OrderedCanon>(
            PlainNId::new(1),
            |g| {
                if g == id(2) { id(1) } else { g }
            },
            &mut buf,
            &mut collisions,
            &mut Vec::new(),
            crate::canon::MSetClamp::None,
        );
        assert_eq!(collisions, vec![(id(20), id(10))]);
    }

    #[test]
    fn recanonize_aci_shrinks() {
        let mut c = VariableArityCache::<ENodeId, OpId, ENodeId, SetNodeId, false>::new();
        let op = OpId::new(0);
        // {1, 2, 3} sorted
        c.probe_or_insert(id(10), op, &[id(1), id(2), id(3)]);
        let mut buf = Vec::new();
        let mut collisions = Vec::new();
        // find: 2 → 1, 3 → 3 → after ACI canon: {1, 3} (deduped, sorted)
        c.recanonize_node::<SetCanon>(
            SetNodeId::new(0),
            |g| {
                if g == id(2) { id(1) } else { g }
            },
            &mut buf,
            &mut collisions,
            &mut Vec::new(),
            crate::canon::MSetClamp::None,
        );
        assert!(collisions.is_empty());
        assert!(c.probe(op, &[id(1), id(3)]).is_some());
        // old 3-element key gone
        assert!(c.probe(op, &[id(1), id(2), id(3)]).is_none());
    }

    #[test]
    fn recanonize_ac_merges_mult() {
        type MSetChild = (ENodeId, Multiplicity);
        let mut c = VariableArityCache::<ENodeId, OpId, MSetChild, MSetNodeId, false>::new();
        let op = OpId::new(0);
        let elems: &[MSetChild] = &[
            (id(1), Multiplicity(1)),
            (id(2), Multiplicity(1)),
            (id(3), Multiplicity(1)),
        ];
        c.probe_or_insert(id(10), op, elems);
        let mut buf = Vec::new();
        let mut collisions = Vec::new();
        c.recanonize_node::<MSetCanon>(
            MSetNodeId::new(0),
            |g| {
                if g == id(2) { id(1) } else { g }
            },
            &mut buf,
            &mut collisions,
            &mut Vec::new(),
            crate::canon::MSetClamp::None,
        );
        assert!(collisions.is_empty());
        let expected: &[MSetChild] = &[(id(1), Multiplicity(2)), (id(3), Multiplicity(1))];
        assert!(c.probe(op, expected).is_some());
    }
}
